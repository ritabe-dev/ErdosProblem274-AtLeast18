#!/usr/bin/env python3
"""Separately implemented verifier for the E274 bounded index search artifact.

Unlike the primary checker, this implementation stores the residual as a
reduced natural-number pair and explores an explicit stack rather than using
``Fraction`` recursion.  It deliberately imports no code, constants, hashing
helpers, or search bounds from the primary implementation. It shares the same
mathematical obstruction specification and is not an independent mathematical
proof.
"""

from __future__ import annotations

import hashlib
import json
from itertools import combinations
from math import gcd
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[2]
ARTIFACT = ROOT / "data" / "e274" / "index_obstruction_search.json"

CORE_PROFILE = "p42_p43"
FULL_PROFILE = "p42_p43_p45_p47"

PROFILE_BOUNDARIES = (
    (
        CORE_PROFILE,
        15,
        28,
        "c246c57324c881e5b263b275290710682a8072027b2736a3b4c07e78ed735eec",
    ),
    (
        FULL_PROFILE,
        17,
        5,
        "0244dcaa451200177fe26b8ea2b8ab53f3737817004129afbd9969e1bead2d57",
    ),
)


def fail(*details: object) -> None:
    raise SystemExit(f"verify_index_obstruction_independent: FAIL: {details!r}")


def canonical_sha256(values: Iterable[tuple[int, ...]]) -> str:
    payload = json.dumps(tuple(sorted(values)), separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def pairwise_one(values: tuple[int, ...]) -> bool:
    for i, a in enumerate(values):
        for b in values[i + 1 :]:
            if gcd(a, b) != 1:
                return False
    return True


def forbidden(values: tuple[int, ...], profile: str) -> bool:
    even = tuple(x // 2 for x in values if not x % 2)
    for subset in combinations(even, 3):
        if pairwise_one(subset):
            return True

    mult_three = tuple(x // 3 for x in values if not x % 3)
    for subset in combinations(mult_three, 4):
        if pairwise_one(subset):
            return True

    if profile == CORE_PROFILE:
        return False
    if profile != FULL_PROFILE:
        raise ValueError(profile)

    for first in (x // 2 for x in values if x % 4 == 2):
        for tail in combinations((x // 4 for x in values if x % 4 == 0), 3):
            if pairwise_one((first,) + tail):
                return True

    if 3 in values:
        for second in (x // 3 for x in values if x != 3 and x % 6 == 3):
            for tail in combinations((x // 6 for x in values if x % 6 == 0), 3):
                if pairwise_one((second,) + tail):
                    return True
    return False


def enumerate_integer_state(
    total_terms: int, profile: str
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
        upper = (left * denominator) // numerator
        if not prefix:
            lower = max(lower, 3)

        for d in range(upper, lower - 1, -1):
            if any(gcd(d, old) == 1 for old in prefix):
                continue
            extended = prefix + (d,)
            if forbidden(extended, profile):
                continue
            next_num = numerator * d - denominator
            next_den = denominator * d
            common = gcd(next_num, next_den)
            stack.append((left - 1, next_num // common, next_den // common, d, extended))

    return nodes, tuple(sorted(survivors))


def main() -> None:
    expected = json.loads(ARTIFACT.read_text())
    expected_profiles = {CORE_PROFILE, FULL_PROFILE}
    if set(expected.get("profiles", {})) != expected_profiles:
        fail("profile set", set(expected.get("profiles", {})), expected_profiles)

    for profile, final_r, first_count, first_sha256 in PROFILE_BOUNDARIES:
        profile_data = expected["profiles"][profile]
        rows = profile_data["results"]
        expected_lengths = list(range(2, final_r + 1))
        actual_lengths = [row["r"] for row in rows]
        if actual_lengths != expected_lengths:
            fail(profile, "length coverage", actual_lengths, expected_lengths)
        if profile_data["first_survivor_r"] != final_r:
            fail(profile, "first_survivor_r", profile_data["first_survivor_r"], final_r)
        if profile_data["first_survivor_count"] != first_count:
            fail(
                profile,
                "first_survivor_count",
                profile_data["first_survivor_count"],
                first_count,
            )
        if any(row["survivor_count"] != 0 for row in rows[:-1]):
            fail(profile, "survivor before boundary")
        if rows[-1]["survivor_count"] != first_count:
            fail(profile, "boundary survivor count", rows[-1]["survivor_count"], first_count)

        for row in rows:
            nodes, actual = enumerate_integer_state(row["r"], profile)
            if nodes != row["nodes"]:
                fail(profile, row["r"], "nodes", nodes, row["nodes"])
            if len(actual) != row["survivor_count"]:
                fail(profile, row["r"], "survivors", len(actual), row["survivor_count"])

        _nodes, final_actual = enumerate_integer_state(final_r, profile)
        if len(final_actual) != first_count:
            fail(profile, final_r, "computed first survivor count", len(final_actual), first_count)
        if "first_survivors" in profile_data:
            expected_final = tuple(tuple(row) for row in profile_data["first_survivors"])
            if final_actual != expected_final:
                fail(profile, final_r, "first_survivors")
        actual_sha256 = canonical_sha256(final_actual)
        if actual_sha256 != first_sha256:
            fail(profile, final_r, "computed sha256", actual_sha256, first_sha256)
        if profile_data["first_survivors_sha256"] != first_sha256:
            fail(
                profile,
                final_r,
                "artifact sha256",
                profile_data["first_survivors_sha256"],
                first_sha256,
            )
    print("verify_index_obstruction_independent: PASS")


if __name__ == "__main__":
    main()
