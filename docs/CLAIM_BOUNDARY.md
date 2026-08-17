# Claim and trust boundary

## Candidate theorem

Every nontrivial exact coset partition of an arbitrary group into at most
seventeen left cosets of finite-index subgroups contains two subgroups with
equal index. Equivalently, every counterexample to the Herzog-Schönheim
conjecture requires at least eighteen cells.

## Relation to Erdős Problem 274

The maintained Erdős Problems page uses the arbitrary-group
Herzog-Schönheim conjecture as Problem 274. The historically asked abelian
special case is already known through the subnormal-subgroup case. This
project addresses only a bounded part of the maintained general-group
formulation.

## What Lean checks locally

- the exact bounded counterexample statement;
- index-two descent and minimality in the number of cells;
- reciprocal sum one and pairwise gcd greater than one;
- the normal-core finite quotient, partition descent, and index preservation;
- sorting and detector semantics;
- source-shaped finite proofs corresponding to Margolis–Schnabel
  Propositions 4.2, 4.3, 4.5, and 4.7;
- selected harmonic subfamilies and arbitrary-group detector transfers;
- semantic completeness of the arithmetic enumerator;
- the exact five arithmetic profiles at seventeen by split
  `decide +kernel` certificates;
- the index-four three-box construction, including `n*d = 4*e`, same-box
  gcd, and exact reciprocal capacity;
- assignment-to-DFS completeness;
- rejection of all five profiles by split `decide +kernel` DFS certificates;
- composition into the closed theorem with no external theorem parameter
  `erdos274AtMostSeventeen`.

`MargolisSchnabelFacts` is retained as an internal theorem-mapping structure.
`localMargolisSchnabelFacts` proves all six fields locally, so the structure is
not an external assumption of the final theorem.

## Kernel computation boundary

The arithmetic certificate family contains 18 depth modules covering 1,052
states. The fiber certificate family contains 251 generated modules: one data
module, 174 leaves, 71 internal nodes, and five profile endpoints. A leaf has
at most 6,000 visited DFS states and is checked by `decide +kernel`. A parent
unfolds one transition and rewrites every successful child theorem.

The audited final endpoint has no explicit argument and depends only on
`propext`, `Classical.choice`, and `Quot.sound`. The theorem-facing Lean tree
contains no `sorry`, custom axiom, `native_decide`, `bv_decide`, compiler
evaluation axiom, `unsafe`, `extern`, or `implemented_by` declaration.

The certificate generators are deterministic source-reproduction tools, not
proof premises.

## Source boundary

The local Lean proofs establish the source-shaped statements needed here; the
cited article supplies provenance and statement comparison. This is not a
line-by-line formal transcription of that article. The manuscript explicitly
records how the local P4.3 proof expands a compressed source inference and how
the P4.7 proof resolves a repeated vector in the printed presentation.

## Non-claims

- The unrestricted Herzog-Schönheim conjecture remains open.
- Eighteen-cell partitions are not excluded, and no eighteen-cell
  counterexample is asserted to exist.
- The 39 length-eighteen diagnostic survivors are necessary-condition
  profiles, not coset partitions or counterexamples.
- The project does not reopen or strengthen the known historical abelian
  special case.
- The project has not been peer reviewed or externally reproduced.
- The bounded literature search does not establish priority or bibliographic
  completeness.
