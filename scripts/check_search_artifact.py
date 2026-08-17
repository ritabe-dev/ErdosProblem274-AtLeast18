#!/usr/bin/env python3
"""Verify the supplementary E274 search artifacts and Python replays."""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SEARCH_DIR = ROOT / "search" / "e274"
INDEX_ARTIFACT = ROOT / "data" / "e274" / "index_obstruction_search.json"
FIBER_ARTIFACT = ROOT / "data" / "e274" / "fiber_intersection_sieve.json"

EXPECTED_INDEX_ARTIFACT_SHA256 = (
    "d2a0f76238e84ecee18bb982ee95171ca6b204072fdd2252b949f436d7dca63a"
)
EXPECTED_FIBER_ARTIFACT_SHA256 = (
    "212fdaf458244d6c1d0bf21ef3b565b55c838547f0c5b16bef7a92c1e11dc353"
)
EXPECTED_R17_ARITHMETIC_SHA256 = (
    "0244dcaa451200177fe26b8ea2b8ab53f3737817004129afbd9969e1bead2d57"
)
EXPECTED_R17_FIBER_SHA256 = (
    "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"
)
EXPECTED_R18_ARITHMETIC_SHA256 = (
    "93990cb52b62f08cd529081e76e72ffed2e01ef83f24a193302899322a22cd24"
)
EXPECTED_R18_FIBER_SHA256 = (
    "589513a618402b335e622356dc26ded1be17d1fd20c2c5bb627a60e41ddd7eb3"
)

sys.path.insert(0, str(SEARCH_DIR))
from exact_index_obstruction_search import build_payload as build_index_payload  # noqa: E402
from fiber_intersection_sieve import build_payload as build_fiber_payload  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"check_search_artifact: FAIL: {message}")


def audit_import_separation(path: Path, allowed_imports: set[str]) -> None:
    tree = ast.parse(path.read_text(), filename=str(path))
    imported_modules: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported_modules.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            if node.level != 0 or node.module is None:
                fail(f"{path.name} uses a relative import")
            if any(alias.name == "*" for alias in node.names):
                fail(f"{path.name} uses a star import")
            imported_modules.add(node.module.split(".", 1)[0])
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id in {
                "__import__",
                "eval",
                "exec",
                "compile",
            }:
                fail(f"{path.name} uses dynamic code loading: {node.func.id}")
            if isinstance(node.func, ast.Attribute) and node.func.attr in {
                "open",
                "read_bytes",
            }:
                fail(f"{path.name} reads an unapproved local source")
            if isinstance(node.func, ast.Attribute) and node.func.attr == "read_text":
                if not isinstance(node.func.value, ast.Name) or node.func.value.id != "ARTIFACT":
                    fail(f"{path.name} reads a file other than its frozen artifact")

    unexpected = imported_modules - allowed_imports
    if unexpected:
        fail(
            f"{path.name} imports non-standard modules: "
            + ", ".join(sorted(unexpected))
        )


def run_verifier(path: Path, marker: str, *args: str) -> None:
    result = subprocess.run(
        [sys.executable, "-I", str(path), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        fail(f"{path.name} failed")
    if marker not in result.stdout:
        fail(f"{path.name} emitted no PASS marker")


def main() -> None:
    index_stored = json.loads(INDEX_ARTIFACT.read_text())
    fiber_stored = json.loads(FIBER_ARTIFACT.read_text())

    if fiber_stored.get("schema_version") != 3:
        fail("unexpected fiber artifact schema")

    if sha256(INDEX_ARTIFACT) != EXPECTED_INDEX_ARTIFACT_SHA256:
        fail("index artifact SHA-256 differs from the reviewed candidate")
    if sha256(FIBER_ARTIFACT) != EXPECTED_FIBER_ARTIFACT_SHA256:
        fail("fiber artifact SHA-256 differs from the reviewed candidate")
    if index_stored != build_index_payload():
        fail("primary arithmetic regeneration differs from the frozen artifact")
    if fiber_stored != build_fiber_payload():
        fail("primary fiber regeneration differs from the frozen artifact")

    full = index_stored["profiles"]["p42_p43_p45_p47"]
    if any(row["survivor_count"] != 0 for row in full["results"] if row["r"] <= 16):
        fail("an arithmetic survivor appears at length at most sixteen")
    if full["first_survivor_r"] != 17 or full["first_survivor_count"] != 5:
        fail("unexpected arithmetic boundary")
    if full["first_survivors_sha256"] != EXPECTED_R17_ARITHMETIC_SHA256:
        fail("unexpected r=17 arithmetic survivor hash")

    r17 = fiber_stored["results"]["r17"]
    r18 = fiber_stored["results"]["r18"]
    if (
        r17["arithmetic_candidate_count"] != 5
        or r17["arithmetic_candidates_sha256"] != EXPECTED_R17_ARITHMETIC_SHA256
        or r17["fiber_survivor_count"] != 0
        or r17["fiber_survivors_sha256"] != EXPECTED_R17_FIBER_SHA256
    ):
        fail("unexpected r=17 fiber boundary")
    if (
        r18["arithmetic_candidate_count"] != 470
        or r18["arithmetic_candidates_sha256"] != EXPECTED_R18_ARITHMETIC_SHA256
        or r18["fiber_survivor_count"] != 39
        or r18["fiber_survivors_sha256"] != EXPECTED_R18_FIBER_SHA256
    ):
        fail("unexpected r=18 diagnostic boundary")
    if fiber_stored["first_fiber_survivor_r"] != 18:
        fail("unexpected first fiber-survivor length")

    arithmetic_primary = SEARCH_DIR / "exact_index_obstruction_search.py"
    arithmetic_independent = SEARCH_DIR / "verify_index_obstruction_independent.py"
    fiber_primary = SEARCH_DIR / "fiber_intersection_sieve.py"
    fiber_independent = SEARCH_DIR / "verify_fiber_intersection_sieve.py"

    audit_import_separation(
        arithmetic_independent,
        {"__future__", "hashlib", "itertools", "json", "math", "pathlib", "typing"},
    )
    audit_import_separation(
        fiber_independent,
        {"__future__", "argparse", "functools", "hashlib", "itertools", "json", "math", "pathlib"},
    )

    index_provenance = index_stored["provenance"]
    fiber_provenance = fiber_stored["provenance"]
    if index_provenance["primary_script_sha256"] != sha256(arithmetic_primary):
        fail("primary arithmetic script hash mismatch")
    if index_provenance["independent_script_sha256"] != sha256(arithmetic_independent):
        fail("independent arithmetic script hash mismatch")
    if fiber_provenance["primary_script_sha256"] != sha256(fiber_primary):
        fail("primary fiber script hash mismatch")
    if fiber_provenance["independent_script_sha256"] != sha256(fiber_independent):
        fail("independent fiber script hash mismatch")

    run_verifier(
        arithmetic_independent,
        "verify_index_obstruction_independent: PASS",
    )
    run_verifier(
        fiber_independent,
        "verify_fiber_intersection_sieve: PASS (r=17,18)",
        "--extended",
    )

    print("check_search_artifact: PASS")


if __name__ == "__main__":
    main()
