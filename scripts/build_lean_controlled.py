#!/usr/bin/env python3
"""Build the standalone E274 Lean closure with bounded parallelism.

The generated fiber leaves are independent and memory intensive.  A plain
unbounded build may start too many of them at once on a small runner.  This
script computes the local import DAG and invokes Lean on at most two ready
modules concurrently.  It writes only ordinary `.olean` files under `.lake/`.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
MODULE_RE = re.compile(r"^import\s+(ErdosProblems(?:\.E274(?:\.[A-Za-z0-9_]+)?)?)\s*$")


def module_path(name: str) -> Path:
    return ROOT / (name.replace(".", "/") + ".lean")


def local_imports(path: Path) -> tuple[str, ...]:
    result: list[str] = []
    for line in path.read_text().splitlines():
        match = MODULE_RE.match(line)
        if match:
            result.append(match.group(1))
    return tuple(result)


def dependency_closure(root_module: str) -> dict[str, tuple[str, ...]]:
    closure: dict[str, tuple[str, ...]] = {}

    def visit(name: str) -> None:
        if name in closure:
            return
        path = module_path(name)
        if not path.is_file():
            raise SystemExit(f"missing local module: {path.relative_to(ROOT)}")
        imports = local_imports(path)
        closure[name] = imports
        for imported in imports:
            visit(imported)

    visit(root_module)
    return closure


def module_output(name: str) -> Path:
    return ROOT / ".lake" / "build" / "lib" / "lean" / (
        name.replace(".", "/") + ".olean"
    )


def compile_module(name: str) -> tuple[str, str, bool]:
    source = module_path(name)
    output = module_output(name)
    output.parent.mkdir(parents=True, exist_ok=True)
    imports = local_imports(source)
    if output.is_file():
        output_time = output.stat().st_mtime_ns
        dependencies_current = all(
            module_output(dep).is_file()
            and module_output(dep).stat().st_mtime_ns <= output_time
            for dep in imports
        )
        if dependencies_current and source.stat().st_mtime_ns <= output_time:
            return name, "", True
    result = subprocess.run(
        ["lake", "env", "lean", "-o", str(output), str(source)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        details = result.stdout + result.stderr
        raise RuntimeError(f"Lean failed for {name}\n{details}")
    return name, result.stdout + result.stderr, False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1 or args.jobs > 2:
        raise SystemExit("--jobs must be 1 or 2 for the reviewed build profile")

    graph = dependency_closure("ErdosProblems")
    if "ErdosProblems.E274.UnconditionalTheorem" not in graph or len(graph) < 250:
        raise SystemExit(
            "incomplete E274 import closure: expected the unconditional theorem "
            f"and at least 250 local modules, found {len(graph)}"
        )
    pending = set(graph)
    completed: set[str] = set()
    reused_count = 0
    running: dict[Future[tuple[str, str, bool]], str] = {}

    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while pending or running:
            ready = sorted(
                name
                for name in pending
                if all(dep in completed for dep in graph[name])
            )
            while ready and len(running) < args.jobs:
                name = ready.pop(0)
                pending.remove(name)
                running[executor.submit(compile_module, name)] = name

            if not running:
                blocked = ", ".join(sorted(pending)[:10])
                raise SystemExit(f"local import cycle or missing dependency near: {blocked}")

            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                try:
                    _built, output, reused = future.result()
                except Exception as error:
                    for other in running:
                        other.cancel()
                    raise SystemExit(str(error)) from error
                if output.strip():
                    sys.stdout.write(output)
                completed.add(name)
                if reused:
                    reused_count += 1
                else:
                    print(f"[{len(completed)}/{len(graph)}] {name}", flush=True)

    print(
        "controlled Lean build: PASS "
        f"({len(completed)} modules, jobs={args.jobs}, reused={reused_count})"
    )


if __name__ == "__main__":
    main()
