import ErdosProblems.E274.MargolisSchnabelImports
import ErdosProblems.E274.LocalPartitionFacts
import ErdosProblems.E274.MargolisSchnabelP42Detector
import ErdosProblems.E274.MargolisSchnabelP43Detector
import ErdosProblems.E274.MargolisSchnabelP45Detector
import ErdosProblems.E274.MargolisSchnabelP47Detector

/-!
# Local discharge of the six Margolis--Schnabel inputs

The original bounded theorem exposed six consequences of
Margolis--Schnabel as an explicit `MargolisSchnabelFacts` argument.  This file
constructs that argument from Lean proofs in the E274 lane itself:

* the reciprocal-sum and pairwise-gcd consequences of Lemma 2.3;
* the four executable-detector corollaries of Propositions 4.2, 4.3, 4.5,
  and 4.7, including the finite-quotient transfer for arbitrary groups.

The structure remains useful as a statement-level audit boundary, but it is
no longer an assumption of the unconditional endpoint.
-/

namespace ErdosProblems.E274

universe u

/-- All six formerly imported source consequences, proved locally in Lean. -/
theorem localMargolisSchnabelFacts : MargolisSchnabelFacts.{u} where
  lemma2_3b := by
    intro G _ n g H hpartition hfinite _hinjective
    exact hpartition.sum_inv_index_eq_one hfinite
  lemma2_3c := by
    intro G _ n g H hpartition hfinite _hinjective
    exact hpartition.gcd_index_gt_one hfinite
  prop4_2_detectorCorollary := by
    intro G _ n g H hpartition hfinite hinjective hdetector
    exact p42DetectorCorollary hpartition hfinite hinjective hdetector
  prop4_3_detectorCorollary := by
    intro G _ n g H hpartition hfinite hinjective hdetector
    exact p43DetectorCorollary hpartition hfinite hinjective hdetector
  prop4_5_detectorCorollary := by
    intro G _ n g H hpartition hfinite hinjective hdetector
    exact p45DetectorCorollary hpartition hfinite hinjective hdetector
  prop4_7_detectorCorollary := by
    intro G _ n g H hpartition hfinite hinjective hdetector
    exact p47DetectorCorollary hpartition hfinite hinjective hdetector

end ErdosProblems.E274
