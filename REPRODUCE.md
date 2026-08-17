# Reproduction guide

## Pinned environment

- Lean: `leanprover/lean4:v4.30.0`
- mathlib input revision: `v4.30.0`
- exact transitive dependency revisions: `lake-manifest.json`
- Python: version 3.9 or later; only the standard library is used
- reference manuscript compiler: TeX Live 2026, `latexmk` 4.88, and
  pdfTeX 1.40.29

## One-command verification

From the repository root, run:

```bash
bash scripts/check_release.sh
```

The release check performs nine visible stages.

1. Verify the supplementary exact-search artifacts and their separately
   implemented Python replays.
2. Reproduce all 18 arithmetic kernel-certificate modules byte for byte.
3. Reproduce all 251 fiber kernel-certificate modules byte for byte.
4. Build the complete local Lean import closure with at most two concurrent
   modules.
5. Audit the exact theorem signatures and axiom dependencies.
6. Reject proof placeholders, custom primitives, unsafe declarations, and
   native/compiler evaluation in the theorem-facing Lean tree.
7. Verify source and manuscript SHA-256 manifests.
8. Verify the complete release-tree manifest.
9. Reject stale identifiers, local paths, secrets, and disallowed evaluation
   language from release-facing text.

The controlled build is used because the 174 generated fiber leaves are
independent and memory intensive. It computes the local import DAG and runs at
most two ready Lean modules concurrently.

## Mathematical and formal trust boundary

The final theorem is:

```lean
ErdosProblems.E274.erdos274AtMostSeventeen
```

Its type is:

```lean
ErdosProblems.E274.erdos274AtMostSeventeenTarget
```

It has no external theorem argument. The internal structure
`MargolisSchnabelFacts` is inhabited by
`localMargolisSchnabelFacts`, whose six fields are local Lean theorems:

- the reciprocal-sum identity;
- the pairwise-gcd consequence;
- detector corollaries corresponding to Margolis–Schnabel Propositions 4.2,
  4.3, 4.5, and 4.7.

The normal-core finite quotient, index preservation, harmonic subfamily
selection, detector semantics, and arbitrary-group transfers are also in the
local dependency chain. The source article is cited for provenance and
statement comparison; it is not imported as an unproved theorem parameter.

The theorem-facing closed computations are:

```lean
ErdosProblems.E274.checked_seventeen_survivors
ErdosProblems.E274.kernelFiberProfile1_unsat
ErdosProblems.E274.kernelFiberProfile2_unsat
ErdosProblems.E274.kernelFiberProfile3_unsat
ErdosProblems.E274.kernelFiberProfile4_unsat
ErdosProblems.E274.kernelFiberProfile5_unsat
```

They use checked-in split `decide +kernel` proofs. No `native_decide`,
`bv_decide`, or compiler-evaluation axiom occurs in the final dependency
chain. `AxiomAudit.lean` requires every public endpoint to depend on a subset
of `propext`, `Classical.choice`, and `Quot.sound`, and checks that the final
theorem type contains no `MargolisSchnabelFacts` parameter.

## Generated certificates

The arithmetic generator independently reconstructs the exact 1,052-state
search tree and writes 18 depth modules. The fiber generator reconstructs the
five exact mask-assignment trees and writes 251 modules:

- one fixed profile-data module;
- 174 leaf modules;
- 71 internal-node modules;
- five profile endpoint modules.

Each fiber leaf contains at most 6,000 visited DFS states and is discharged by
`decide +kernel`. An internal node unfolds exactly one DFS transition and
rewrites every successful child to its imported theorem. A missing child,
extra child, or altered transition therefore prevents the parent theorem from
type-checking. The generators select the split and reproduce the source, but
are not trusted proof premises.

## Supplementary Python diagnostics

The Python arithmetic and fiber programs retain the diagnostic boundary at
eighteen terms. They are separate from the theorem-facing Lean certificate
route. The primary arithmetic program uses exact rational recursion, while a
second implementation uses reduced integer states and an explicit stack. The
primary fiber diagnostic uses a symmetry-reduced layer search, while a second
implementation keeps all boxes labelled and uses memoized depth-first search.
They share one mathematical specification and are implementation-diverse, not
independent mathematical proofs.

## Manual commands

```bash
python3 scripts/check_search_artifact.py
python3 -I search/e274/generate_arithmetic_kernel_certificates.py --check
python3 -I search/e274/generate_fiber_kernel_dfs_certificates.py
python3 scripts/build_lean_controlled.py --jobs 2
lake env lean AxiomAudit.lean
```

To compile and record the manuscript:

```bash
bash scripts/build_pdf.sh --write
```

After an authorized candidate update, regenerate frozen hashes with:

```bash
bash scripts/update_manifests.sh
```

To compare a deterministic build with the committed PDF, use the reference
TeX Live toolchain listed above:

```bash
bash scripts/build_pdf.sh --check
```

A compatible but different TeX Live release may compile correctly while
producing different PDF bytes.

## Fresh-copy check

For a release decision, clone or extract the repository without `.lake/` and
run the one-command verification. After publication, the exact tag CI job
must assert that checkout `HEAD` equals `GITHUB_SHA` and retain the identity,
verification, and manuscript logs. Release notes must then state the full
commit SHA, CI run URL, source-archive SHA-256, and PDF SHA-256. Dependency
cache reuse is acceptable local evidence but is not an external reproduction.
