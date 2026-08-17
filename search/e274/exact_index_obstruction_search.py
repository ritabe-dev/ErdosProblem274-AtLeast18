#!/usr/bin/env python3
"""Exact arithmetic search for the bounded E274 index obstruction.

The search enumerates strictly increasing Egyptian-fraction denominator lists
forced by a minimal counterexample to the Herzog--Schönheim conjecture.  It
uses exact ``Fraction`` arithmetic and only monotone pruning conditions.

This is computational evidence.  The completeness proof for the denominator
interval and the group-theoretic reduction are tracked separately.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from math import gcd
from pathlib import Path
from typing import Iterable


CORE_PROFILE = "p42_p43"
FULL_PROFILE = "p42_p43_p45_p47"

EXPECTED_CORE_R15_SHA256 = (
    "c246c57324c881e5b263b275290710682a8072027b2736a3b4c07e78ed735eec"
)
EXPECTED_FULL_R17 = (
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120),
    (4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96),
)
EXPECTED_FULL_R17_SHA256 = (
    "0244dcaa451200177fe26b8ea2b8ab53f3737817004129afbd9969e1bead2d57"
)

PUBLISHED_OBSTRUCTIONS = {
    "p42": "No subtuple (2*r1,2*r2,2*r3) with pairwise-coprime residuals.",
    "p43": "No subtuple (3*r1,3*r2,3*r3,3*r4) with pairwise-coprime residuals.",
    "p45": (
        "No subtuple (2*r1,4*r2,4*r3,4*r4) with r1 odd and "
        "pairwise-coprime residuals."
    ),
    "p47": (
        "No subtuple (3,3*r2,6*r3,6*r4,6*r5) with r2 odd and "
        "pairwise-coprime residuals."
    ),
}


def canonical_sha256(values: Iterable[tuple[int, ...]]) -> str:
    payload = json.dumps(tuple(sorted(values)), separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pairwise_coprime(values: tuple[int, ...]) -> bool:
    return all(gcd(a, b) == 1 for a, b in combinations(values, 2))


def contains_p42(values: tuple[int, ...]) -> bool:
    halves = tuple(x // 2 for x in values if x % 2 == 0)
    return any(pairwise_coprime(parts) for parts in combinations(halves, 3))


def contains_p43(values: tuple[int, ...]) -> bool:
    thirds = tuple(x // 3 for x in values if x % 3 == 0)
    return any(pairwise_coprime(parts) for parts in combinations(thirds, 4))


def contains_p45(values: tuple[int, ...]) -> bool:
    twice_odd = tuple(x // 2 for x in values if x % 4 == 2)
    quarters = tuple(x // 4 for x in values if x % 4 == 0)
    return any(
        pairwise_coprime((r1,) + parts)
        for r1 in twice_odd
        for parts in combinations(quarters, 3)
    )


def contains_p47(values: tuple[int, ...]) -> bool:
    if 3 not in values:
        return False
    three_times_odd = tuple(x // 3 for x in values if x != 3 and x % 6 == 3)
    sixths = tuple(x // 6 for x in values if x % 6 == 0)
    return any(
        pairwise_coprime((r2,) + parts)
        for r2 in three_times_odd
        for parts in combinations(sixths, 3)
    )


def contains_obstruction(values: tuple[int, ...], profile: str) -> bool:
    if contains_p42(values) or contains_p43(values):
        return True
    if profile == FULL_PROFILE:
        return contains_p45(values) or contains_p47(values)
    if profile != CORE_PROFILE:
        raise ValueError(f"unknown profile: {profile}")
    return False


def ceil_fraction(value: Fraction) -> int:
    return (value.denominator + value.numerator - 1) // value.numerator


def exact_search(total_terms: int, profile: str) -> tuple[int, tuple[tuple[int, ...], ...]]:
    """Return visited-node count and every surviving denominator list."""

    nodes = 0
    survivors: list[tuple[int, ...]] = []

    def visit(residual: Fraction, prefix: tuple[int, ...], left: int) -> None:
        nonlocal nodes
        nodes += 1
        if left == 0:
            if residual == 0:
                survivors.append(prefix)
            return
        if residual <= 0:
            return

        previous = prefix[-1] if prefix else 0
        lower = max(previous + 1, ceil_fraction(residual))
        upper = (left * residual.denominator) // residual.numerator
        if not prefix:
            lower = max(lower, 3)

        for denominator in range(lower, upper + 1):
            if any(gcd(denominator, old) == 1 for old in prefix):
                continue
            extended = prefix + (denominator,)
            if contains_obstruction(extended, profile):
                continue
            visit(residual - Fraction(1, denominator), extended, left - 1)

    visit(Fraction(1), (), total_terms)
    result = tuple(sorted(survivors))
    for values in result:
        assert len(values) == total_terms
        assert all(a < b for a, b in zip(values, values[1:]))
        assert values[0] > 2
        assert all(gcd(a, b) > 1 for a, b in combinations(values, 2))
        assert sum((Fraction(1, d) for d in values), Fraction()) == 1
        assert not contains_obstruction(values, profile)
    return nodes, result


def build_payload() -> dict[str, object]:
    profiles: dict[str, object] = {}
    for profile, final_r in ((CORE_PROFILE, 15), (FULL_PROFILE, 17)):
        rows = []
        final_survivors: tuple[tuple[int, ...], ...] = ()
        for r in range(2, final_r + 1):
            nodes, survivors = exact_search(r, profile)
            rows.append({"r": r, "nodes": nodes, "survivor_count": len(survivors)})
            if r == final_r:
                final_survivors = survivors
        entry = {
            "results": rows,
            "first_survivor_r": final_r,
            "first_survivor_count": len(final_survivors),
            "first_survivors_sha256": canonical_sha256(final_survivors),
        }
        if profile == FULL_PROFILE:
            entry["first_survivors"] = [list(values) for values in final_survivors]
        profiles[profile] = entry

    core = profiles[CORE_PROFILE]
    full = profiles[FULL_PROFILE]
    assert isinstance(core, dict) and isinstance(full, dict)
    assert all(row["survivor_count"] == 0 for row in core["results"][:-1])
    assert core["first_survivor_count"] == 28
    assert core["first_survivors_sha256"] == EXPECTED_CORE_R15_SHA256
    assert all(row["survivor_count"] == 0 for row in full["results"][:-1])
    assert full["first_survivor_count"] == 5
    assert tuple(tuple(row) for row in full["first_survivors"]) == EXPECTED_FULL_R17
    assert full["first_survivors_sha256"] == EXPECTED_FULL_R17_SHA256

    primary = Path(__file__).resolve()
    independent = primary.with_name("verify_index_obstruction_independent.py")
    return {
        "schema_version": 1,
        "problem_id": "E274",
        "provenance": {
            "primary_script_sha256": file_sha256(primary),
            "independent_script_sha256": file_sha256(independent),
        },
        "arithmetic_conditions": [
            "strictly increasing denominators greater than 2",
            "exact reciprocal sum one",
            "pairwise gcd greater than one",
        ],
        "published_obstructions": PUBLISHED_OBSTRUCTIONS,
        "profiles": profiles,
        "claim_boundary": (
            "Survivors are arithmetic index candidates only, not coset partitions. "
            "The group reduction, source-imported non-harmonic propositions, and "
            "search-completeness proof are separate dependencies."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    parser.add_argument("--output", type=Path, help="Write JSON to this path.")
    args = parser.parse_args()
    payload = build_payload()
    rendered: str
    if args.pretty:
        rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    else:
        rendered = json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
