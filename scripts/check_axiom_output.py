#!/usr/bin/env python3
"""Audit the closed E274 theorem surface and ordinary axiom boundary."""

from __future__ import annotations

import re
import sys


ENDPOINTS = (
    "ErdosProblems.E274.checked_seventeen_survivors",
    "ErdosProblems.E274.localMargolisSchnabelFacts",
    "ErdosProblems.E274.kernelFiberDFS4_complete_of_orderedAssignment",
    "ErdosProblems.E274.seventeenIndexFourAssignmentObstruction_kernel",
    "ErdosProblems.E274.erdos274AtMostSeventeen",
)
FINAL = "ErdosProblems.E274.erdos274AtMostSeventeen"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def fail(message: str) -> None:
    raise SystemExit(f"check_axiom_output: FAIL: {message}")


def dependencies(text: str, name: str) -> set[str]:
    pattern = re.compile(
        rf"'{re.escape(name)}' depends on axioms:\s*\[(.*?)\]",
        re.DOTALL,
    )
    match = pattern.search(text)
    if not match:
        fail(f"missing axiom report for {name}")
    return {part.strip() for part in match.group(1).split(",") if part.strip()}


def signature_block(text: str, name: str) -> str:
    start = re.search(
        rf"^{re.escape(name)}(?:\.\{{[^}}]+\}})?(?=\s|\{{|\(|:)",
        text,
        re.MULTILINE,
    )
    if not start:
        fail(f"missing #check output for {name}")
    end = text.find(f"'{name}' depends on axioms:", start.end())
    if end < 0:
        fail(f"missing signature terminator for {name}")
    return text[start.start():end]


def main() -> None:
    text = sys.stdin.read()
    forbidden_fragments = (
        "sorryAx",
        "native_decide",
        "nativeEqTrue",
        "trustCompiler",
        "ofReduceBool",
    )
    for fragment in forbidden_fragments:
        if fragment in text:
            fail(f"forbidden dependency marker appears: {fragment}")

    for name in ENDPOINTS:
        signature_block(text, name)
        actual = dependencies(text, name)
        unexpected = actual - ALLOWED
        if unexpected:
            fail(f"unexpected dependency for {name}: {sorted(unexpected)}")

    final_signature = signature_block(text, FINAL)
    if "erdos274AtMostSeventeenTarget" not in final_signature:
        fail("final endpoint has the wrong target type")
    if "MargolisSchnabelFacts" in final_signature:
        fail("final endpoint still exposes the internal source interface")
    if re.search(r"\([^)]*:\s*[^)]*\)", final_signature):
        fail("final endpoint unexpectedly exposes an explicit argument")

    print("check_axiom_output: PASS")


if __name__ == "__main__":
    main()
