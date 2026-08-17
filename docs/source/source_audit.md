# Source statement audit

Source audit and package review date: 2026-08-16 JST (UTC+09:00).

## Maintained problem statement

The maintained Erdős Problems page marks Problem 274 open and states the
Herzog-Schönheim conjecture for a nontrivial finite partition of a group into
left cosets of finite-index subgroups. It is a secondary status source and
does not establish priority.

In this package, “Erdős Problem 274” refers to that maintained arbitrary-group
formulation. The historically asked abelian special case is already known
through the subnormal-subgroup case. The theorem proved here concerns only
the bounded range `2 <= r <= 17`.

## Margolis-Schnabel provenance

Canonical publication:

Leo Margolis and Ofir Schnabel, “The Herzog-Schönheim Conjecture for Small
Groups and Harmonic Subgroups,” *Beiträge zur Algebra und Geometrie* 60
(2019), 399-418. DOI: `10.1007/s13366-018-0419-1`.

The publisher record gives publication date 2018-10-04 without a source time
zone. The arXiv version is `arXiv:1803.03569`, submitted
2018-03-09 15:39:43 UTC = 2018-03-10 00:39:43 JST.

The Lean development proves local source-shaped versions of the consequences
used from:

- Lemma 2.3(b): reciprocal sum one;
- Lemma 2.3(c): no coprime pair of ambient indices;
- Proposition 4.2: no harmonic `(2r_1,2r_2,2r_3)` pattern with
  pairwise-coprime residuals;
- Proposition 4.3: no corresponding four-term multiple-of-three pattern;
- Proposition 4.5: no `(2r_1,4r_2,4r_3,4r_4)` pattern when `r_1` is odd;
- Proposition 4.7: no `(3,3r_2,6r_3,6r_4,6r_5)` pattern when `r_2` is odd.

The cited article remains the provenance and statement-comparison source. It
is not an external premise of the public Lean theorem, and this package does
not claim to be a line-by-line transcription of the article.

## Source-presentation issues handled locally

Two printed passages require care.

- The last inference of Corollary 3.11 is too compressed to follow from the
  displayed inequality alone. `MargolisSchnabelP43.lean` replaces that step
  with an explicit parity and finite-cardinality argument.
- In the discussion following Lemma 4.6, a six-entry vector is printed twice.
  The local P4.7 proof distinguishes the penultimate configuration
  `(1,2,2,3,3,1)` from the final survivor `(1,2,2,3,1,1)`, as required by the
  preceding case list and the statement of the lemma.

These repairs are visible proof obligations in Lean rather than silent edits
to the cited text.

## Arbitrary ambient groups

For the finitely many finite-index subgroups `H_i`, let `N` be the
intersection of their normal cores. Then `N` is normal and finite index,
`N <= H_i`, and the partition descends to the finite group `G/N` while
preserving every cell and the complete index profile.

`FiniteQuotientBridge.lean` proves this reduction. The detector modules then
select the required distinct cells, prove that the selected subfamilies remain
harmonic, apply the local finite obstruction theorems, and transport the
result back to the arbitrary group. `LocalMargolisSchnabelFacts.lean` combines
all six consequences into the internal audit structure used by the final
composition.

## New index-four layer

The index-four group-to-fiber argument uses local elementary group facts and
the reciprocal-density theorem. The anchor subgroup need not be normal: its
four left cosets are used only as a finite set of boxes. Lean proves the
support relation, intersection-index identity, same-box gcd obstruction,
per-box cover inequality, double count, exact capacity, and the bridge from a
declarative assignment to the direct kernel DFS.

## Prior arbitrary-group cell bound

Füsun Akman and Papa A. Sissokho, “Transversal Coset Partitions of Groups,”
*Beiträge zur Algebra und Geometrie* 66 (2025), 417-441. DOI:
`10.1007/s13366-024-00748-9`.

Theorem 6 covers `2 <= r <= 7` distinct subgroups. The publisher record gives
online date 2024-04-25 without a source time zone. In a counterexample the
indices, hence the subgroups, are distinct, so the result gives the
corresponding seven-cell statement.

## Literature boundary

The recorded search found no published arbitrary-group cell-count theorem for
the range eight through seventeen. It was not exhaustive and does not
establish priority. Specialist confirmation, MathSciNet/zbMATH subscriber
checking, and review of unpublished or private circulation remain open.
