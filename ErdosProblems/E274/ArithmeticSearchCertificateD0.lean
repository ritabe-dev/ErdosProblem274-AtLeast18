import ErdosProblems.E274.ArithmeticSearchCertificateD1

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD0_0 :
    searchIndexLists 17 1 1 0 [] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 3 15).flatMap (fun d =>
      if admissibleNext [] d then
        let rawNum := 1 * d - 1
        let rawDen := 1 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 16 (rawNum / common) (rawDen / common) d
          (d :: [])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 3 15).filter
        (admissibleNext []) =
        [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] := by
    decide +kernel
  rw [hfilter]
  norm_num

theorem checked_seventeen_survivors :
    candidateIndexLists 17 = seventeenSurvivors := by
  unfold candidateIndexLists
  rw [arithmeticCertD0_0]
  rfl

end ErdosProblems.E274
