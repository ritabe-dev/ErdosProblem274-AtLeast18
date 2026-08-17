# The Herzog-Schönheim conjecture for coset partitions with at most seventeen cells

This repository is an unreviewed, computer-assisted review candidate for the
following bounded partial theorem.

Version: `0.4.2-review-candidate`, prepared 2026-08-17 JST (UTC+09:00).

> Let `G` be a group and let `g_i H_i`, for `1 <= i <= r`, be a nontrivial
> exact finite partition of `G` into left cosets of finite-index subgroups. If
> `r <= 17`, then `[G : H_i] = [G : H_j]` for some `i != j`.

Equivalently, any counterexample to the Herzog-Schönheim conjecture requires
at least eighteen cells.

The unrestricted conjecture remains open. The manuscript has not been peer
reviewed, and this repository makes no priority claim.

## Scope within Erdős Problem 274

The maintained Erdős Problems page presents the arbitrary-group
Herzog-Schönheim conjecture as Problem 274. The historical abelian special
case is already known through a result for subnormal subgroups. This candidate
concerns only the bounded cell-count statement above.

The proof takes a counterexample with the fewest cells, removes index two by a
descent argument, and turns the remaining subgroup indices into a strictly
increasing Egyptian-fraction profile. Four source-shaped harmonic
obstructions leave no arithmetic profile through sixteen cells and exactly
five profiles at seventeen cells. Every one of those five begins with index
four. An index-four cell forces a finite assignment to three non-anchor boxes:
for a row of ambient index `n`, support size `d`, and induced index `e`,
`n*d = 4*e`; each box has reciprocal capacity one; and induced indices that
share a box have gcd greater than one. A second complete finite check rejects
all five profiles.

At eighteen terms, the supplementary Python diagnostic has 470 arithmetic
profiles and its first-order one-anchor test leaves 39. Those lists satisfy
necessary conditions only. They are not coset partitions or counterexamples.

## Lean status and trust boundary

The public Lean endpoint is:

```lean
ErdosProblems.E274.erdos274AtMostSeventeen
```

Its type is `erdos274AtMostSeventeenTarget` and it has no external theorem
parameter. The theorem-facing dependency chain locally proves:

- index-two descent and the minimal-cell reduction;
- the reciprocal-sum and pairwise-gcd partition facts;
- the normal-core finite-quotient reduction and index-profile preservation;
- source-shaped finite forms of Margolis–Schnabel Propositions 4.2, 4.3,
  4.5, and 4.7, together with cell selection and arbitrary-group transfer;
- the exact arithmetic enumeration through seventeen cells;
- the index-four group-to-assignment bridge;
- assignment-to-DFS completeness and rejection of all five profiles.

`MargolisSchnabelFacts` remains as an internal theorem-mapping structure, but
`localMargolisSchnabelFacts` constructs all six fields inside Lean. It is not
an argument of the final theorem.

The two finite computations are split into checked-in proof-producing
`decide +kernel` certificates. The arithmetic tree has 1,052 states in 18
depth modules. The fiber computation has 251 generated modules: one shared
profile-data module, 174 bounded leaves, 71 internal nodes, and five profile
endpoints. Each leaf covers at most 6,000 visited DFS states; the internal
nodes unfold one transition and rewrite by all child theorems. The generators
are checked for byte-for-byte reproduction, but their execution is not a
proof premise.

The audited final endpoint depends only on:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, custom axiom, `native_decide`, `bv_decide`, compiler
evaluation axiom, `unsafe`, `extern`, or `implemented_by` declaration in the
theorem-facing first-party Lean tree.

This is a self-contained Lean formalization of the bounded theorem, not a
line-by-line transcription of the cited article. The article remains the
provenance for the obstruction statements and the manuscript explains where
the local formal proof expands or repairs compressed source steps.

## Reproduce

With Git, Python 3, `elan`, and a network connection for the first dependency
fetch:

```bash
bash scripts/check_release.sh
```

The command checks both generated-certificate families, builds the controlled
Lean dependency chain, audits the final theorem and its axioms, checks the
supplementary exact-search artifacts, and verifies the release manifests. See
[REPRODUCE.md](REPRODUCE.md) for the detailed commands.

## Main Lean endpoints

```lean
ErdosProblems.E274.checked_seventeen_survivors
ErdosProblems.E274.localMargolisSchnabelFacts
ErdosProblems.E274.kernelFiberDFS4_complete_of_orderedAssignment
ErdosProblems.E274.seventeenIndexFourAssignmentObstruction_kernel
ErdosProblems.E274.erdos274AtMostSeventeen
```

The dependency map is in [docs/THEOREM_MAP.md](docs/THEOREM_MAP.md), and the
exact claim boundary is in [docs/CLAIM_BOUNDARY.md](docs/CLAIM_BOUNDARY.md).

## Paper and review material

- [paper/main.tex](paper/main.tex) is the proof manuscript.
- The compiled manuscript is
  [output/pdf/e274_at_least_18_review_candidate.pdf](output/pdf/e274_at_least_18_review_candidate.pdf).
- [docs/review/ONE_PAGE_SUMMARY.md](docs/review/ONE_PAGE_SUMMARY.md) gives a
  compact proof outline.
- Mathematics, Lean, and literature review requests are under `docs/review/`.
- [VERIFICATION_RECORD.md](VERIFICATION_RECORD.md) records local verification
  evidence for this exact candidate.
- Short source records and their hashes are under `third_party/e274/`.

## Identifier status

This review tree is not yet tied to a public commit, public tag, CI run,
release URL, DOI, arXiv identifier, Zenodo record, or OSF record. Those fields
must be populated only from the exact externally reviewed tree after an
authorized publication and exact-tag CI run.

## Author and assistance disclosure

Rio Itabe is responsible for the manuscript, code, and release decisions.
LLMs accessed through ChatGPT Pro and OpenAI Codex, primarily GPT-5.6, were
used during proof exploration, Lean formalization, testing, literature
screening, and editing. LLM output was not treated as a proof, source, or
external review.

## License

Original code and text are available under the MIT License. Third-party source
records remain subject to their original terms. See
[third_party/NOTICE.md](third_party/NOTICE.md).
