#!/usr/bin/env python3
"""Separately implemented verifier for the E274 index-four fiber artifact.

This file imports no project module.  It independently regenerates the
arithmetic profiles with a reduced-integer explicit-stack search, then checks
the fiber obstruction with a labelled-column memoized DFS.  The primary
program instead uses ``Fraction`` recursion, symmetry-canonicalized columns,
and a layer-by-layer dynamic program. The programs share the same mathematical
obstruction specification and are not independent mathematical proofs.

The default run checks the theorem-facing r=17 boundary.  ``--extended`` also
checks the recorded r=18 diagnostic layer.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ARTIFACT = ROOT / "data" / "e274" / "fiber_intersection_sieve.json"

EXPECTED = {
    17: {
        "nodes": 1052,
        "arithmetic_count": 5,
        "arithmetic_sha256": (
            "0244dcaa451200177fe26b8ea2b8ab53f3737817004129afbd9969e1bead2d57"
        ),
        "fiber_count": 0,
        "fiber_sha256": (
            "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"
        ),
    },
    18: {
        "nodes": 24221,
        "arithmetic_count": 470,
        "arithmetic_sha256": (
            "93990cb52b62f08cd529081e76e72ffed2e01ef83f24a193302899322a22cd24"
        ),
        "fiber_count": 39,
        "fiber_sha256": (
            "589513a618402b335e622356dc26ded1be17d1fd20c2c5bb627a60e41ddd7eb3"
        ),
    },
}


def fail(*details: object) -> None:
    raise SystemExit(f"verify_fiber_intersection_sieve: FAIL: {details!r}")


def canonical_sha256(values: tuple[tuple[int, ...], ...]) -> str:
    payload = json.dumps(tuple(sorted(values)), separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def pairwise_coprime(values: tuple[int, ...]) -> bool:
    return all(
        gcd(a, b) == 1
        for position, a in enumerate(values)
        for b in values[position + 1 :]
    )


def forbidden(values: tuple[int, ...]) -> bool:
    even = tuple(x // 2 for x in values if x % 2 == 0)
    if any(pairwise_coprime(part) for part in combinations(even, 3)):
        return True

    thirds = tuple(x // 3 for x in values if x % 3 == 0)
    if any(pairwise_coprime(part) for part in combinations(thirds, 4)):
        return True

    first_pool = tuple(x // 2 for x in values if x % 4 == 2)
    tail_pool = tuple(x // 4 for x in values if x % 4 == 0)
    for first in first_pool:
        if any(
            pairwise_coprime((first,) + tail)
            for tail in combinations(tail_pool, 3)
        ):
            return True

    if 3 in values:
        second_pool = tuple(
            x // 3 for x in values if x != 3 and x % 6 == 3
        )
        last_pool = tuple(x // 6 for x in values if x % 6 == 0)
        for second in second_pool:
            if any(
                pairwise_coprime((second,) + tail)
                for tail in combinations(last_pool, 3)
            ):
                return True
    return False


def arithmetic_profiles(
    total_terms: int,
) -> tuple[int, tuple[tuple[int, ...], ...]]:
    survivors: list[tuple[int, ...]] = []
    stack = [(total_terms, 1, 1, 0, ())]
    nodes = 0

    while stack:
        nodes += 1
        left, numerator, denominator, previous, prefix = stack.pop()
        if left == 0:
            if numerator == 0:
                survivors.append(prefix)
            continue
        if numerator == 0:
            continue

        lower = max(previous + 1, (denominator + numerator - 1) // numerator)
        upper = left * denominator // numerator
        if not prefix:
            lower = max(lower, 3)

        for value in range(upper, lower - 1, -1):
            if any(gcd(value, old) == 1 for old in prefix):
                continue
            extended = prefix + (value,)
            if forbidden(extended):
                continue
            next_numerator = numerator * value - denominator
            next_denominator = denominator * value
            common = gcd(next_numerator, next_denominator)
            stack.append(
                (
                    left - 1,
                    next_numerator // common,
                    next_denominator // common,
                    value,
                    extended,
                )
            )

    return nodes, tuple(sorted(survivors))


def row_choices(anchor: int, index: int) -> tuple[tuple[int, int], ...]:
    result = []
    for mask in range(1, 1 << (anchor - 1)):
        support_size = bin(mask).count("1")
        if index * support_size % anchor == 0:
            result.append((mask, index * support_size // anchor))
    return tuple(result)


def labelled_transition_trace4(profile: tuple[int, ...]) -> dict[str, object]:
    """Independently replay the supplementary labelled state model.

    This intentionally does not reuse the bitset/memoized implementation in
    :func:`fiber_survives`.  It preserves the original row order and the
    sorted seen-index lists with multiplicity, and it deduplicates only
    literally equal three-column states.
    """

    if not profile or profile[0] != 4:
        fail("labelled trace requires an index-four profile", profile)
    rows = profile[1:]
    options = {index: row_choices(4, index) for index in rows}
    scale = 1
    for index in rows:
        for _mask, induced in options[index]:
            scale = lcm(scale, induced)

    empty = (0, ())
    states = {(empty, empty, empty)}
    layers = [1]
    attempted = 0
    admissible_count = 0
    steps = []
    for depth, index in enumerate(rows, 1):
        incoming = len(states)
        attempted_before = attempted
        admissible_before = admissible_count
        next_states = set()
        for state in states:
            for support_mask, induced in options[index]:
                attempted += 1
                if induced == 0 or scale % induced != 0:
                    continue
                increment = scale // induced
                columns = list(state)
                admissible = True
                for column in range(3):
                    if support_mask & (1 << column) == 0:
                        continue
                    filled, seen = columns[column]
                    if filled + increment > scale:
                        admissible = False
                        break
                    if any(gcd(induced, old) == 1 for old in seen):
                        admissible = False
                        break
                    columns[column] = (
                        filled + increment,
                        tuple(sorted((induced,) + seen)),
                    )
                if admissible:
                    admissible_count += 1
                    next_states.add(tuple(columns))
        successful = admissible_count - admissible_before
        steps.append(
            {
                "depth": depth,
                "index": index,
                "choice_count": len(options[index]),
                "incoming_distinct_states": incoming,
                "transition_attempt_count": attempted - attempted_before,
                "successful_transition_results_before_dedup": successful,
                "outgoing_distinct_states": len(next_states),
                "duplicate_results_removed": successful - len(next_states),
            }
        )
        states = next_states
        layers.append(len(states))

    accepted = sum(
        all(filled == scale for filled, _seen in state) for state in states
    )
    peak = max(layers)
    empty_step = next(
        (step for step in steps if step["outgoing_distinct_states"] == 0),
        None,
    )
    return {
        "rows_in_processing_order": list(rows),
        "processed_row_count": len(rows),
        "layer_distinct_state_counts": layers,
        "sum_distinct_layer_sizes": sum(layers),
        "expanded_distinct_state_count": sum(layers[:-1]),
        "peak_layer_size": peak,
        "peak_depth": layers.index(peak),
        "transition_attempt_count": attempted,
        "successful_transition_results_before_dedup": admissible_count,
        "first_empty_after_index": empty_step["index"] if empty_step else None,
        "final_distinct_state_count": layers[-1],
        "accepting_state_count": accepted,
        "sieve_result": accepted > 0,
        "steps": steps,
    }


def fiber_survives(profile: tuple[int, ...]) -> bool:
    anchor = profile[0]
    box_count = anchor - 1
    rows = profile[1:]
    options = {index: row_choices(anchor, index) for index in rows}
    if any(not choices for choices in options.values()):
        return False

    order = tuple(sorted(rows, key=lambda index: (len(options[index]), index)))
    induced_values = tuple(
        sorted({induced for index in order for _mask, induced in options[index]})
    )
    bit = {induced: 1 << position for position, induced in enumerate(induced_values)}
    incompatible = {
        induced: sum(
            bit[other]
            for other in induced_values
            if gcd(induced, other) == 1
        )
        for induced in induced_values
    }
    scale = 1
    for induced in induced_values:
        scale = lcm(scale, induced)

    remaining_max = [0] * (len(order) + 1)
    for position in range(len(order) - 1, -1, -1):
        row_max = max(scale // induced for _mask, induced in options[order[position]])
        remaining_max[position] = remaining_max[position + 1] + row_max

    @lru_cache(None)
    def visit(
        position: int,
        capacities: tuple[int, ...],
        seen: tuple[int, ...],
    ) -> bool:
        if position == len(order):
            return capacities == (scale,) * box_count

        index = order[position]
        for support_mask, induced in options[index]:
            increment = scale // induced
            next_capacities = list(capacities)
            next_seen = list(seen)
            admissible = True
            for column in range(box_count):
                if support_mask & (1 << column) == 0:
                    continue
                if next_seen[column] & incompatible[induced]:
                    admissible = False
                    break
                next_capacities[column] += increment
                if next_capacities[column] > scale:
                    admissible = False
                    break
                next_seen[column] |= bit[induced]
            if not admissible:
                continue
            if any(
                scale - filled > remaining_max[position + 1]
                for filled in next_capacities
            ):
                continue
            if visit(
                position + 1,
                tuple(next_capacities),
                tuple(next_seen),
            ):
                return True
        return False

    return visit(0, (0,) * box_count, (0,) * box_count)


def verify_length(
    length: int,
    artifact: dict[str, object],
) -> None:
    fixed = EXPECTED[length]
    row = artifact["results"][f"r{length}"]

    nodes, arithmetic = arithmetic_profiles(length)
    if nodes != fixed["nodes"]:
        fail(length, "arithmetic nodes", nodes, fixed["nodes"])
    if len(arithmetic) != fixed["arithmetic_count"]:
        fail(length, "arithmetic count", len(arithmetic), fixed["arithmetic_count"])
    arithmetic_hash = canonical_sha256(arithmetic)
    if arithmetic_hash != fixed["arithmetic_sha256"]:
        fail(length, "arithmetic hash", arithmetic_hash, fixed["arithmetic_sha256"])
    if row["arithmetic_candidate_count"] != fixed["arithmetic_count"]:
        fail(length, "artifact arithmetic count")
    if row["arithmetic_candidates_sha256"] != fixed["arithmetic_sha256"]:
        fail(length, "artifact arithmetic hash")

    survivors = tuple(profile for profile in arithmetic if fiber_survives(profile))
    if len(survivors) != fixed["fiber_count"]:
        fail(length, "fiber count", len(survivors), fixed["fiber_count"])
    survivor_hash = canonical_sha256(survivors)
    if survivor_hash != fixed["fiber_sha256"]:
        fail(length, "fiber hash", survivor_hash, fixed["fiber_sha256"])
    if row["fiber_survivor_count"] != fixed["fiber_count"]:
        fail(length, "artifact fiber count")
    if row["fiber_survivors_sha256"] != fixed["fiber_sha256"]:
        fail(length, "artifact fiber hash")
    if length == 17:
        audit = row.get("audit")
        if not isinstance(audit, list) or len(audit) != len(arithmetic):
            fail(length, "labelled trace audit rows")
        for profile, audit_row in zip(arithmetic, audit):
            if audit_row.get("profile_sha256") != canonical_sha256((profile,)):
                fail(length, "labelled trace profile identity", profile)
            expected_trace = labelled_transition_trace4(profile)
            if audit_row.get("labelled_python_transition_replay") != expected_trace:
                fail(length, "labelled transition trace", profile)
            if expected_trace["accepting_state_count"] != 0:
                fail(length, "labelled accepted state", profile)
    if length == 18:
        recorded = tuple(tuple(profile) for profile in row["fiber_survivors"])
        if survivors != recorded:
            fail(length, "recorded fiber survivors")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--extended",
        action="store_true",
        help="also reproduce the r=18 diagnostic survivor layer",
    )
    args = parser.parse_args()

    artifact = json.loads(ARTIFACT.read_text())
    if artifact.get("problem_id") != "E274":
        fail("problem id")
    if artifact.get("schema_version") != 3:
        fail("schema version")
    if artifact.get("first_fiber_survivor_r") != 18:
        fail("first fiber survivor length")

    lengths = (17, 18) if args.extended else (17,)
    for length in lengths:
        verify_length(length, artifact)
    rendered = ",".join(str(length) for length in lengths)
    print(f"verify_fiber_intersection_sieve: PASS (r={rendered})")


if __name__ == "__main__":
    main()
