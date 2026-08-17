#!/usr/bin/env python3
"""Generate split kernel-only DFS certificates for E274.

The default mode is read-only and fails unless every generated Lean file is
byte-for-byte current.  Pass ``--write`` to update the generated files.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "ErdosProblems" / "E274"
GENERATED_PREFIX = "FiberKernelDFSCertificateP"
DATA_FILE = LEAN_DIR / "FiberKernelDFSProfileData.lean"
MAX_LEAF_NODES = 6000

PROFILES = (
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96),
)

Column = tuple[int, tuple[int, ...]]
State = tuple[Column, Column, Column]


def choices(index: int) -> tuple[tuple[int, int], ...]:
    result = []
    for mask in range(1, 8):
        support_size = bin(mask).count("1")
        if index * support_size % 4 == 0:
            result.append((mask, index * support_size // 4))
    return tuple(result)


def scale_for(rows: tuple[int, ...]) -> int:
    scale = 1
    for index in rows:
        for _mask, induced in choices(index):
            scale = lcm(scale, induced)
    return scale


def update(state: State, scale: int, mask: int, induced: int) -> State | None:
    columns = [[fill, list(seen)] for fill, seen in state]
    for box in range(3):
        if not mask & (1 << box):
            continue
        fill, seen = columns[box]
        if any(gcd(induced, old) == 1 for old in seen):
            return None
        fill += scale // induced
        if fill > scale:
            return None
        columns[box] = [fill, [induced, *seen]]
    return tuple((fill, tuple(seen)) for fill, seen in columns)  # type: ignore[return-value]


@dataclass
class Node:
    depth: int
    state: State
    count: int = 0
    children: list[tuple[int, "Node"]] = field(default_factory=list)
    number: int = -1
    leaf_number: int = -1


def build_tree(rows: tuple[int, ...], scale: int) -> Node:
    initial: State = ((0, ()), (0, ()), (0, ()))

    @lru_cache(None)
    def count(depth: int, state: State) -> int:
        total = 1
        if depth < len(rows):
            for mask, induced in choices(rows[depth]):
                next_state = update(state, scale, mask, induced)
                if next_state is not None:
                    total += count(depth + 1, next_state)
        return total

    def split(depth: int, state: State) -> Node:
        node = Node(depth=depth, state=state, count=count(depth, state))
        if node.count <= MAX_LEAF_NODES or depth == len(rows):
            return node
        for mask, induced in choices(rows[depth]):
            next_state = update(state, scale, mask, induced)
            if next_state is not None:
                node.children.append((mask, split(depth + 1, next_state)))
        return node

    return split(0, initial)


def assign_numbers(root: Node) -> tuple[list[Node], list[Node]]:
    all_nodes: list[Node] = []
    leaves: list[Node] = []

    def visit(node: Node) -> None:
        node.number = len(all_nodes)
        all_nodes.append(node)
        if not node.children:
            node.leaf_number = len(leaves)
            leaves.append(node)
        for _mask, child in node.children:
            visit(child)

    visit(root)
    return all_nodes, leaves


def lean_list(values: tuple[int, ...] | list[int]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def lean_state(state: State) -> str:
    return "[" + ", ".join(
        f"({fill}, {lean_list(list(seen))})" for fill, seen in state
    ) + "]"


def lean_choices(index: int) -> str:
    return "[" + ", ".join(
        f"({mask}, {induced})" for mask, induced in choices(index)
    ) + "]"


def theorem_name(profile: int, node: Node) -> str:
    if node.children:
        return f"kernelFiberP{profile}_node{node.number}_unsat"
    return f"kernelFiberP{profile}_leaf{node.leaf_number}_unsat"


def module_stem(profile: int, node: Node) -> str:
    if node.children:
        return f"{GENERATED_PREFIX}{profile}N{node.number:03d}"
    return f"{GENERATED_PREFIX}{profile}B{node.leaf_number:03d}"


def theorem_statement(profile: int, node: Node, rows: tuple[int, ...], scale: int) -> str:
    remaining = rows[node.depth :]
    return (
        f"theorem {theorem_name(profile, node)} :\n"
        f"    kernelFiberDFS4 {scale} {lean_list(remaining)}\n"
        f"      {lean_state(node.state)} = false := by\n"
    )


def profile_data() -> str:
    lines = [
        "import ErdosProblems.E274.FiberKernelDFSCore",
        "",
        "/-! Generated fixed data for the five E274 fiber certificates. -/",
        "",
        "namespace ErdosProblems.E274",
        "",
    ]
    for profile, values in enumerate(PROFILES, 1):
        rows = values[1:]
        lines.extend(
            [
                f"def fiberProfile{profile}Rows : List Nat := {lean_list(rows)}",
                f"def fiberProfile{profile}Scale : Nat := {scale_for(rows)}",
                "",
            ]
        )
    indices = sorted({index for profile in PROFILES for index in profile[1:]})
    for index in indices:
        lines.extend(
            [
                "set_option maxRecDepth 1000000 in",
                f"theorem kernelFiberChoices4_{index} :",
                f"    kernelFiberChoices4 {index} = {lean_choices(index)} := by",
                "  decide +kernel",
                "",
            ]
        )
    for mask in range(1, 8):
        for bit in range(3):
            value = "true" if mask & (1 << bit) else "false"
            lines.extend(
                [
                    f"@[simp] theorem kernelTestBit_{mask}_{bit} :",
                    f"    Nat.testBit {mask} {bit} = {value} := by",
                    "  decide",
                    "",
                ]
            )
    lines.extend(["end ErdosProblems.E274", ""])
    return "\n".join(lines)


def leaf_module(profile: int, node: Node, rows: tuple[int, ...], scale: int) -> str:
    return "\n".join(
        [
            "import ErdosProblems.E274.FiberKernelDFSProfileData",
            "",
            "/-! Generated kernel certificate branch; do not edit by hand. -/",
            "",
            "namespace ErdosProblems.E274",
            "",
            "set_option maxRecDepth 1000000 in",
            "set_option maxHeartbeats 0 in",
            f"/-- Kernel evaluation rejects a DFS subtree of {node.count} visited states. -/",
            theorem_statement(profile, node, rows, scale)
            + "  decide +kernel",
            "",
            "end ErdosProblems.E274",
            "",
        ]
    )


def internal_module(
    profile: int,
    node: Node,
    rows: tuple[int, ...],
    scale: int,
) -> str:
    lines = [
        *(
            f"import ErdosProblems.E274.{module_stem(profile, child)}"
            for _mask, child in node.children
        ),
        "",
        "/-! Generated internal node of the split kernel DFS certificate. -/",
        "",
        "namespace ErdosProblems.E274",
        "",
        "set_option maxRecDepth 1000000 in",
        "set_option maxHeartbeats 0 in",
    ]
    if profile >= 4:
        lines.append("set_option linter.unusedSimpArgs false in")
    child_names = ", ".join(
        theorem_name(profile, child) for _mask, child in node.children
    )
    proof_lines = [
        theorem_statement(profile, node, rows, scale).rstrip(),
        f"  rw [kernelFiberDFS4, kernelFiberChoices4_{rows[node.depth]}]",
        "  simp [kernelUpdateFiberColumns, kernelUpdateFiberColumn"
        + (", Nat.odd_iff" if profile >= 4 else "")
        + ", "
        + child_names
        + "]",
    ]
    lines.extend(
        [
            "\n".join(proof_lines),
            "",
            "end ErdosProblems.E274",
            "",
        ]
    )
    return "\n".join(lines)


def aggregator_module(profile: int, root: Node) -> str:
    return "\n".join(
        [
            f"import ErdosProblems.E274.{module_stem(profile, root)}",
            "",
            "/-! Generated endpoint of the split kernel DFS certificate. -/",
            "",
            "namespace ErdosProblems.E274",
            "",
            f"theorem kernelFiberProfile{profile}_unsat :",
            f"    kernelFiberDFS4 fiberProfile{profile}Scale fiberProfile{profile}Rows",
            "      emptyKernelFiberState = false := by",
            f"  simpa [fiberProfile{profile}Scale, fiberProfile{profile}Rows,",
            "    emptyKernelFiberState] using " + theorem_name(profile, root),
            "",
            "end ErdosProblems.E274",
            "",
        ]
    )


def generated_files() -> dict[Path, str]:
    result = {DATA_FILE: profile_data()}
    for profile, values in enumerate(PROFILES, 1):
        rows = values[1:]
        scale = scale_for(rows)
        root = build_tree(rows, scale)
        all_nodes, leaves = assign_numbers(root)
        for leaf in leaves:
            path = LEAN_DIR / f"{GENERATED_PREFIX}{profile}B{leaf.leaf_number:03d}.lean"
            result[path] = leaf_module(profile, leaf, rows, scale)
        for node in all_nodes:
            if not node.children:
                continue
            path = LEAN_DIR / f"{GENERATED_PREFIX}{profile}N{node.number:03d}.lean"
            result[path] = internal_module(profile, node, rows, scale)
        path = LEAN_DIR / f"{GENERATED_PREFIX}{profile}.lean"
        result[path] = aggregator_module(profile, root)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    expected = generated_files()
    existing = {
        path
        for path in LEAN_DIR.glob(f"{GENERATED_PREFIX}*.lean")
        if path.is_file()
    }
    existing.add(DATA_FILE) if DATA_FILE.exists() else None

    if args.write:
        for stale in sorted(existing - expected.keys()):
            stale.unlink()
        for path, content in sorted(expected.items()):
            path.write_text(content)
        print(f"generated {len(expected)} Lean files")
        return

    problems = []
    for path, content in sorted(expected.items()):
        if not path.exists():
            problems.append(f"missing: {path.relative_to(ROOT)}")
        elif path.read_text() != content:
            problems.append(f"stale: {path.relative_to(ROOT)}")
    for path in sorted(existing - expected.keys()):
        problems.append(f"unexpected: {path.relative_to(ROOT)}")
    if problems:
        raise SystemExit("\n".join(problems))
    print(f"fiber kernel certificate check: PASS ({len(expected)} files)")


if __name__ == "__main__":
    main()
