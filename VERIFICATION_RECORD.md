# Verification record

Candidate: `0.4.2-review-candidate`  
Prepared: `2026-08-17 JST (UTC+09:00)`  
Verification kind: local pre-release evidence. This record does not claim an
external reproduction, public tag CI, peer review, DOI, or public access.

## Fixed mathematical endpoint

The public theorem is:

```text
ErdosProblems.E274.erdos274AtMostSeventeen :
  ErdosProblems.E274.erdos274AtMostSeventeenTarget
```

It has no external theorem argument. The six consequences represented by the
internal `MargolisSchnabelFacts` structure are proved locally and assembled by
`localMargolisSchnabelFacts`.

## Completed canonical checks

Before packaging, the canonical project completed the following checks:

- all local Lemma 2.3, finite-quotient, P4.2, P4.3, P4.5, and P4.7 modules
  compiled;
- the arithmetic generator reproduced 18 certificate modules covering 1,052
  states and exactly five seventeen-term survivors;
- the fiber generator reproduced 251 certificate modules: one profile-data
  module, 174 kernel leaves, 71 internal nodes, and five profile endpoints;
- the final group-to-mask bridge, kernel-DFS completeness theorem, all five
  negative profile endpoints, and unconditional composition compiled;
- a direct axiom audit reported exactly the ordinary Lean axioms
  `propext`, `Classical.choice`, and `Quot.sound` for the public theorem and
  its four principal intermediate endpoints;
- a theorem-tree scan found no `sorry`, custom axiom, `native_decide`,
  `bv_decide`, compiler/native evaluation axiom, `unsafe`, `extern`, or
  `implemented_by` dependency.

The theorem-facing finite checks are split into checked-in proof modules.
Their closed leaves use `decide +kernel`; internal nodes unfold one transition
and rewrite with child theorems. The generators aid deterministic regeneration
but are not trusted premises of the Lean theorem.

## Candidate-tree checks

A fresh project build compiled all 305 local Lean modules with at most two
concurrent processes and reused no project output. It ran from
`2026-08-17 03:55:46 JST (UTC+09:00)` through
`2026-08-17 07:10:50 JST (UTC+09:00)` and exited 0. No Lean source changed
after that build. The complete nine-stage release check covers:

- supplementary exact-search artifacts: PASS;
- 18 arithmetic certificate modules, 1,052 states, five survivors: PASS;
- 251 fiber certificate modules: PASS;
- complete 305-module dependency closure: PASS;
- closed endpoint and ordinary-axiom audit: PASS;
- theorem-tree primitive scan: PASS;
- source, PDF, and complete-tree manifests: PASS;
- active-version, privacy, secret-pattern, claim-language, and cache scans:
  PASS.

The deterministic TeX Live 2026 build produced a 12-page PDF with SHA-256
`064e9be1d9e6ad0498ce6bb979f8178038be51d8044c1b9ac065d28027fe22c2`.
Every rendered page was inspected for clipping, overlap, broken references,
and unreadable text.

The exact finalized tree and extracted ZIP are checked during archive
assembly. Their release-check result, times, exit codes, and hashes are stored
beside the archive to avoid a self-referential verification record.

## Environment boundary

The local environment was:

- macOS 26.5, build 25F71, arm64;
- Python 3.9.6;
- Lean 4.30.0, commit
  `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- Lake 5.0.0;
- mathlib revision
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- TeX Live 2026, pdfTeX 1.40.29.

A previously fetched dependency cache at the revision pinned in
`lake-manifest.json` was reused, but all project `.olean` files were created
anew before the full build. The dependency cache is not part of the release
archive. This is not described as a network-fresh or independent reproduction.

## Publication identity boundary

No public commit, release tag, CI URL, release URL, or DOI is asserted here.
Those values must be recorded only after they exist for the exact unchanged
candidate. The ZIP hash is necessarily stored beside the ZIP rather than
inside it to avoid a circular checksum.
