#!/usr/bin/env python3
"""Exact fiber-intersection sieve for the E274 arithmetic profiles.

For a sorted distinct-index profile ``(m, n_1, ..., n_s)``, use the cell of
smallest index ``m`` as an anchor.  Its complement consists of ``m - 1``
left-coset fibers.  If the cell of index ``n`` meets exactly ``d`` fibers and
the induced subgroup has index ``e`` inside the anchor subgroup, then

    n * d = m * e,    1 <= d <= m - 1.

Within each fiber the induced cosets are pairwise disjoint.  Consequently
their induced indices have pairwise gcd greater than one, and their reciprocal
sum is one.  This program enumerates every support set allowed by those exact
conditions.

The group-theoretic implication from a coset partition to this finite model is
a separate proof obligation.  A surviving arithmetic/fiber profile is not a
group partition or a counterexample.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path
from typing import Iterable, NamedTuple

from exact_index_obstruction_search import (
    EXPECTED_FULL_R17,
    FULL_PROFILE,
    canonical_sha256,
    exact_search,
)


ROOT = Path(__file__).resolve().parents[2]


class FiberStepTrace(NamedTuple):
    depth: int
    index: int
    choice_count: int
    incoming_distinct_states: int
    transition_attempt_count: int
    successful_transition_results_before_dedup: int
    outgoing_distinct_states: int


class FiberTrace(NamedTuple):
    survives: bool
    scale: int
    row_order: tuple[int, ...]
    layer_state_counts: tuple[int, ...]
    transition_attempt_count: int
    admissible_transition_count: int
    accepted_state_count: int
    steps: tuple[FiberStepTrace, ...]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fiber_options(anchor: int, index: int) -> tuple[tuple[tuple[int, ...], int], ...]:
    """Return every support and induced index allowed by index multiplication."""

    boxes = anchor - 1
    result: list[tuple[tuple[int, ...], int]] = []
    for support_size in range(1, boxes + 1):
        if index * support_size % anchor:
            continue
        induced_index = index * support_size // anchor
        for support in combinations(range(boxes), support_size):
            result.append((support, induced_index))
    return tuple(result)


def canonical_columns(
    columns: Iterable[tuple[int, tuple[int, ...]]]
) -> tuple[tuple[int, tuple[int, ...]], ...]:
    """Quotient by permutation symmetry of the unnamed anchor fibers."""

    return tuple(sorted(columns, key=lambda column: (column[0], column[1])))


def fiber_sieve(profile: tuple[int, ...]) -> FiberTrace:
    """Decide the exact first-order fiber constraints for one profile.

    The state of a fiber consists of its exact integer-scaled fill and the set
    of induced indices already placed there.  Multiplicity of a seen index is
    irrelevant to future gcd tests, so retaining the set is complete.
    """

    if not profile or profile[0] < 2:
        raise ValueError(f"invalid anchor profile: {profile!r}")
    anchor = profile[0]
    boxes = anchor - 1
    rows = profile[1:]
    options = {index: fiber_options(anchor, index) for index in rows}
    if any(not choices for choices in options.values()):
        return FiberTrace(False, 1, rows, (1, 0), 0, 0, 0, ())

    # Fewer choices first reduces runtime without changing the explored model.
    order = tuple(
        sorted(rows, key=lambda index: (
            len(options[index]), -Fraction(anchor, index), index
        ))
    )

    scale = 1
    for choices in options.values():
        for _support, induced_index in choices:
            scale = lcm(scale, induced_index)

    remaining_mass = [0] * (len(order) + 1)
    for position in range(len(order) - 1, -1, -1):
        remaining_mass[position] = (
            remaining_mass[position + 1]
            + anchor * scale // order[position]
        )

    empty_column = (0, ())
    states = {canonical_columns((empty_column,) * boxes)}
    layer_counts = [1]
    transition_attempt_count = 0
    admissible_transition_count = 0
    steps: list[FiberStepTrace] = []

    for position, index in enumerate(order):
        incoming_distinct_states = len(states)
        attempted_before = transition_attempt_count
        admissible_before = admissible_transition_count
        next_states = set()
        mass_after = remaining_mass[position + 1]
        for state in states:
            for support, induced_index in options[index]:
                transition_attempt_count += 1
                increment = scale // induced_index
                columns = list(state)
                admissible = True
                for column_number in support:
                    filled, seen = columns[column_number]
                    if filled + increment > scale:
                        admissible = False
                        break
                    if any(gcd(induced_index, old) == 1 for old in seen):
                        admissible = False
                        break
                    columns[column_number] = (
                        filled + increment,
                        tuple(sorted(set(seen) | {induced_index})),
                    )
                if not admissible:
                    continue
                next_state = canonical_columns(columns)
                # Even assigning every remaining cell to a fiber cannot repair
                # a residual larger than the total remaining mass.
                if any(scale - filled > mass_after for filled, _seen in next_state):
                    continue
                admissible_transition_count += 1
                next_states.add(next_state)
        steps.append(
            FiberStepTrace(
                position + 1,
                index,
                len(options[index]),
                incoming_distinct_states,
                transition_attempt_count - attempted_before,
                admissible_transition_count - admissible_before,
                len(next_states),
            )
        )
        states = next_states
        layer_counts.append(len(states))
        if not states:
            break

    accepted_state_count = sum(
        all(filled == scale for filled, _seen in state) for state in states
    )
    return FiberTrace(
        accepted_state_count > 0,
        scale,
        order,
        tuple(layer_counts),
        transition_attempt_count,
        admissible_transition_count,
        accepted_state_count,
        tuple(steps),
    )


def labelled_choices4(index: int) -> tuple[tuple[int, int], ...]:
    """Enumerate masks ``1,...,7`` in fixed labelled-box order."""

    result = []
    for mask in range(1, 8):
        support_size = bin(mask).count("1")
        if index * support_size % 4 == 0:
            result.append((mask, index * support_size // 4))
    return tuple(result)


def labelled_transition_trace4(profile: tuple[int, ...]) -> FiberTrace:
    """Replay the supplementary fixed-order labelled transition system.

    Unlike :func:`fiber_sieve`, this trace keeps all three boxes labelled,
    processes the profile tail in its original order, retains the sorted
    induced-index lists with multiplicity, applies no remaining-mass prune,
    and removes only literally equal states.
    """

    if not profile or profile[0] != 4:
        raise ValueError(f"expected an index-four profile: {profile!r}")
    rows = profile[1:]
    choices = {index: labelled_choices4(index) for index in rows}
    scale = 1
    for index in rows:
        for _mask, induced_index in choices[index]:
            scale = lcm(scale, induced_index)

    empty_column = (0, ())
    states = {(empty_column, empty_column, empty_column)}
    layer_counts = [1]
    transition_attempt_count = 0
    admissible_transition_count = 0
    steps: list[FiberStepTrace] = []

    for depth, index in enumerate(rows, 1):
        incoming_distinct_states = len(states)
        attempted_before = transition_attempt_count
        admissible_before = admissible_transition_count
        next_states = set()
        for state in states:
            for mask, induced_index in choices[index]:
                transition_attempt_count += 1
                if induced_index == 0 or scale % induced_index != 0:
                    continue
                increment = scale // induced_index
                columns = list(state)
                admissible = True
                for column_number in range(3):
                    if mask & (1 << column_number) == 0:
                        continue
                    filled, seen = columns[column_number]
                    if filled + increment > scale:
                        admissible = False
                        break
                    if any(gcd(induced_index, old) == 1 for old in seen):
                        admissible = False
                        break
                    columns[column_number] = (
                        filled + increment,
                        tuple(sorted((induced_index,) + seen)),
                    )
                if admissible:
                    admissible_transition_count += 1
                    next_states.add(tuple(columns))
        steps.append(
            FiberStepTrace(
                depth,
                index,
                len(choices[index]),
                incoming_distinct_states,
                transition_attempt_count - attempted_before,
                admissible_transition_count - admissible_before,
                len(next_states),
            )
        )
        states = next_states
        layer_counts.append(len(states))

    accepted_state_count = sum(
        all(filled == scale for filled, _seen in state) for state in states
    )
    return FiberTrace(
        accepted_state_count > 0,
        scale,
        rows,
        tuple(layer_counts),
        transition_attempt_count,
        admissible_transition_count,
        accepted_state_count,
        tuple(steps),
    )


def trace_payload(trace: FiberTrace) -> dict[str, object]:
    first_empty = next(
        (step for step in trace.steps if step.outgoing_distinct_states == 0),
        None,
    )
    peak_layer_size = max(trace.layer_state_counts)
    return {
        "rows_in_processing_order": list(trace.row_order),
        "processed_row_count": len(trace.layer_state_counts) - 1,
        "layer_distinct_state_counts": list(trace.layer_state_counts),
        "sum_distinct_layer_sizes": sum(trace.layer_state_counts),
        "expanded_distinct_state_count": sum(trace.layer_state_counts[:-1]),
        "peak_layer_size": peak_layer_size,
        "peak_depth": trace.layer_state_counts.index(peak_layer_size),
        "transition_attempt_count": trace.transition_attempt_count,
        "successful_transition_results_before_dedup": (
            trace.admissible_transition_count
        ),
        "first_empty_after_index": first_empty.index if first_empty else None,
        "final_distinct_state_count": trace.layer_state_counts[-1],
        "accepting_state_count": trace.accepted_state_count,
        "sieve_result": trace.survives,
        "steps": [
            {
                "depth": step.depth,
                "index": step.index,
                "choice_count": step.choice_count,
                "incoming_distinct_states": step.incoming_distinct_states,
                "transition_attempt_count": step.transition_attempt_count,
                "successful_transition_results_before_dedup": (
                    step.successful_transition_results_before_dedup
                ),
                "outgoing_distinct_states": step.outgoing_distinct_states,
                "duplicate_results_removed": (
                    step.successful_transition_results_before_dedup
                    - step.outgoing_distinct_states
                ),
            }
            for step in trace.steps
        ],
    }


def profile_rows(
    candidates: tuple[tuple[int, ...], ...],
    *,
    detailed: bool = False,
) -> tuple[
    tuple[tuple[int, ...], ...],
    dict[str, int],
    list[dict[str, object]],
]:
    survivors: list[tuple[int, ...]] = []
    anchor_counts: dict[str, int] = {}
    audit_rows: list[dict[str, object]] = []
    for profile in candidates:
        anchor_key = str(profile[0])
        anchor_counts[anchor_key] = anchor_counts.get(anchor_key, 0) + 1
        primary_trace = fiber_sieve(profile)
        if primary_trace.survives:
            survivors.append(profile)
        row: dict[str, object] = {
            "profile_sha256": canonical_sha256((profile,)),
            "anchor": profile[0],
            "scale": primary_trace.scale,
            "peak_state_count": max(primary_trace.layer_state_counts),
            "survives": primary_trace.survives,
        }
        if detailed:
            row["profile"] = list(profile)
            row["primary_symmetry_reduced_trace"] = trace_payload(primary_trace)
            if profile[0] == 4:
                labelled_trace = labelled_transition_trace4(profile)
                if labelled_trace.survives != primary_trace.survives:
                    raise RuntimeError("labelled and symmetry-reduced traces disagree")
                row["labelled_python_transition_replay"] = trace_payload(labelled_trace)
        audit_rows.append(row)
    return tuple(survivors), anchor_counts, audit_rows


def build_payload() -> dict[str, object]:
    _nodes17, candidates17 = exact_search(17, FULL_PROFILE)
    nodes18, candidates18 = exact_search(18, FULL_PROFILE)
    if candidates17 != EXPECTED_FULL_R17:
        raise RuntimeError("length-seventeen arithmetic input drifted")

    survivors17, anchors17, audit17 = profile_rows(candidates17, detailed=True)
    survivors18, anchors18, audit18 = profile_rows(candidates18)
    if survivors17:
        raise RuntimeError("the five length-seventeen profiles must be eliminated")

    primary = Path(__file__).resolve()
    independent = primary.with_name("verify_fiber_intersection_sieve.py")
    return {
        "schema_version": 3,
        "problem_id": "E274",
        "provenance": {
            "primary_script_sha256": file_sha256(primary),
            "independent_script_sha256": (
                file_sha256(independent) if independent.exists() else None
            ),
        },
        "model": {
            "model_id": "index-four-labelled-transition-v1",
            "anchor": "the smallest subgroup index m in the sorted profile",
            "boxes": "m-1 non-anchor left cosets of the anchor subgroup",
            "row_equation": "n*d=m*e with 1<=d<=m-1",
            "column_capacity": "the reciprocal sum of incident e-values is one",
            "column_disjointness": "every two incident e-values have gcd greater than one",
            "labelled_python_transition_replay": (
                "three labelled boxes, profile-tail order, sorted seen-index lists "
                "with multiplicity, no symmetry quotient or remaining-mass pruning, "
                "and literal state equality only"
            ),
            "primary_python_optimization": (
                "box-permutation canonicalization, choice-count row order, seen-index "
                "sets, and a safe remaining-mass prune"
            ),
            "theorem_facing_lean_route": (
                "separate checked-in split kernel DFS certificates; this Python "
                "artifact is supplementary diagnostic evidence"
            ),
        },
        "results": {
            "r17": {
                "arithmetic_candidate_count": len(candidates17),
                "arithmetic_candidates_sha256": canonical_sha256(candidates17),
                "anchor_counts": anchors17,
                "fiber_survivor_count": len(survivors17),
                "fiber_survivors_sha256": canonical_sha256(survivors17),
                "audit": audit17,
            },
            "r18": {
                "arithmetic_node_count": nodes18,
                "arithmetic_candidate_count": len(candidates18),
                "arithmetic_candidates_sha256": canonical_sha256(candidates18),
                "anchor_counts": anchors18,
                "fiber_survivor_count": len(survivors18),
                "fiber_survivors": [list(profile) for profile in survivors18],
                "fiber_survivors_sha256": canonical_sha256(survivors18),
                "audit": audit18,
            },
        },
        "first_fiber_survivor_r": 18,
        "claim_boundary": (
            "The empty r=17 labelled model is used through the proved "
            "group-to-assignment and assignment-to-search implications. The r=18 "
            "survivors satisfy necessary arithmetic and first-order fiber conditions "
            "only; they are not group partitions or counterexamples."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = build_payload()
    rendered = (
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
        if args.pretty
        else json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    )
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
