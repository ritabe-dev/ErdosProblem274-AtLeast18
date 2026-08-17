# Margolis--Schnabel arithmetic and harmonic obstructions

Retrieved: 2026-08-03 JST (UTC+09:00)

Paper: L. Margolis and O. Schnabel, *The Herzog--Schönheim Conjecture for
Small Groups and Harmonic Subgroups*.

Publication: *Beiträge zur Algebra und Geometrie* 60 (2019), 399--418.

DOI: https://doi.org/10.1007/s13366-018-0419-1

PDF: https://arxiv.org/pdf/1803.03569

The source dependencies used by the E274 bounded route are:

- Lemma 2.3(b,c): a coset partition without multiplicity has reciprocal sum
  one and pairwise gcd greater than one.  The local route does not import the
  minimal-order clause used elsewhere in that lemma; it proves a direct
  minimal-cell index-two descent instead.
- Proposition 4.2: `(2*r1,2*r2,2*r3)` is not `G`-harmonic when the three
  residuals are pairwise coprime.
- Proposition 4.3: `(3*r1,3*r2,3*r3,3*r4)` is not `G`-harmonic when the four
  residuals are pairwise coprime.
- Proposition 4.5: `(2*r1,4*r2,4*r3,4*r4)` is not `G`-harmonic when `r1` is
  odd and the four residuals are pairwise coprime.
- Proposition 4.7: `(3,3*r2,6*r3,6*r4,6*r5)` is not `G`-harmonic when `r2`
  is odd and `r2,...,r5` are pairwise coprime.

The local proof first passes an arbitrary finite-index coset partition to a
finite quotient by intersecting the normal cores of its subgroups.  The
quotient preserves the cells and all indices.  A selected subfamily is still
pairwise disjoint, so a matching index subtuple is harmonic and contradicts
the corresponding proposition.  `FiniteQuotientBridge.lean` proves the
finite-quotient transfer, `ObstructionSelection.lean` proves the selected
subfamily bridge, and the four `MargolisSchnabelP4*Detector.lean` modules
connect the executable detector witnesses to locally proved finite-group
obstructions.

## Exact detector audit

The primary PDF was reread at the statement level on 2026-08-03 JST:

- Proposition 4.2 states exactly that pairwise-coprime `r1,r2,r3` prohibit
  `(2*r1,2*r2,2*r3)`.
- Proposition 4.3 states exactly that pairwise-coprime `r1,...,r4` prohibit
  `(3*r1,3*r2,3*r3,3*r4)`.
- Proposition 4.5 states exactly that pairwise-coprime `r1,...,r4`, with `r1`
  odd, prohibit `(2*r1,4*r2,4*r3,4*r4)`.
- Proposition 4.7 states exactly that pairwise-coprime `r2,...,r5`, with `r2`
  odd, prohibit `(3,3*r2,6*r3,6*r4,6*r5)`.

These hypotheses match `containsP42`, `containsP43`, `containsP45`, and
`containsP47`.  Division after the congruence filters recovers the residual
`r_i`, and `pairwiseCoprime` checks precisely the cited pairwise-coprimality
condition.  Tuple order is immaterial because a harmonic family can be
permuted.  `containsP47` excludes the value `3` from its `3*r2` pool; this is
harmless on `IsArithmeticCandidate`, whose indices are strictly increasing,
because the distinguished leading `3` cannot occur twice.

Claim boundary: `MargolisSchnabelFacts` remains a six-field audit interface
for the two lemma consequences and four detector-level corollaries.
`LocalPartitionFacts.lean`, `FiniteQuotientBridge.lean`, the four local
finite-group obstruction modules, and their detector modules now prove all
six fields locally; `LocalMargolisSchnabelFacts.lean` constructs the complete
interface without an external theorem parameter.  These are source-shaped
local proofs, not a line-by-line formal transcription of the published paper.
