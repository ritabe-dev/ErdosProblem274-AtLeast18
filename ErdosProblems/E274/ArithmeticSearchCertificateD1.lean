import ErdosProblems.E274.ArithmeticSearchCertificateD2

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_0 :
    searchIndexLists 16 2 3 3 [3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 4 21).flatMap (fun d =>
      if admissibleNext [3] d then
        let rawNum := 2 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 4 21).filter
        (admissibleNext [3]) =
        [6, 9, 12, 15, 18, 21, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_1 :
    searchIndexLists 16 3 4 4 [4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 5 17).flatMap (fun d =>
      if admissibleNext [4] d then
        let rawNum := 3 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 5 17).filter
        (admissibleNext [4]) =
        [6, 8, 10, 12, 14, 16, 18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_2 :
    searchIndexLists 16 4 5 5 [5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 6 15).flatMap (fun d =>
      if admissibleNext [5] d then
        let rawNum := 4 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 6 15).filter
        (admissibleNext [5]) =
        [10, 15, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_3 :
    searchIndexLists 16 5 6 6 [6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 7 13).flatMap (fun d =>
      if admissibleNext [6] d then
        let rawNum := 5 * d - 6
        let rawDen := 6 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 7 13).filter
        (admissibleNext [6]) =
        [8, 9, 10, 12, 14, 15, 16, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_4 :
    searchIndexLists 16 6 7 7 [7] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 8 11).flatMap (fun d =>
      if admissibleNext [7] d then
        let rawNum := 6 * d - 7
        let rawDen := 7 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [7])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 8 11).filter
        (admissibleNext [7]) =
        [14] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_5 :
    searchIndexLists 16 7 8 8 [8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 9 10).flatMap (fun d =>
      if admissibleNext [8] d then
        let rawNum := 7 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 9 10).filter
        (admissibleNext [8]) =
        [10, 12, 14, 16, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_6 :
    searchIndexLists 16 8 9 9 [9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 10 9).flatMap (fun d =>
      if admissibleNext [9] d then
        let rawNum := 8 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 10 9).filter
        (admissibleNext [9]) =
        [12, 15, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_7 :
    searchIndexLists 16 9 10 10 [10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 11 7).flatMap (fun d =>
      if admissibleNext [10] d then
        let rawNum := 9 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 11 7).filter
        (admissibleNext [10]) =
        [12, 14, 15, 16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_8 :
    searchIndexLists 16 10 11 11 [11] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 12 6).flatMap (fun d =>
      if admissibleNext [11] d then
        let rawNum := 10 * d - 11
        let rawDen := 11 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [11])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 12 6).filter
        (admissibleNext [11]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_9 :
    searchIndexLists 16 11 12 12 [12] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 5).flatMap (fun d =>
      if admissibleNext [12] d then
        let rawNum := 11 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [12])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 5).filter
        (admissibleNext [12]) =
        [14, 15, 16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_10 :
    searchIndexLists 16 12 13 13 [13] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 14 4).flatMap (fun d =>
      if admissibleNext [13] d then
        let rawNum := 12 * d - 13
        let rawDen := 13 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [13])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 14 4).filter
        (admissibleNext [13]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_11 :
    searchIndexLists 16 13 14 14 [14] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 3).flatMap (fun d =>
      if admissibleNext [14] d then
        let rawNum := 13 * d - 14
        let rawDen := 14 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [14])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 3).filter
        (admissibleNext [14]) =
        [16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_12 :
    searchIndexLists 16 14 15 15 [15] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 2).flatMap (fun d =>
      if admissibleNext [15] d then
        let rawNum := 14 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [15])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 2).filter
        (admissibleNext [15]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_13 :
    searchIndexLists 16 15 16 16 [16] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 1).flatMap (fun d =>
      if admissibleNext [16] d then
        let rawNum := 15 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [16])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 1).filter
        (admissibleNext [16]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD1_14 :
    searchIndexLists 16 16 17 17 [17] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 18 0).flatMap (fun d =>
      if admissibleNext [17] d then
        let rawNum := 16 * d - 17
        let rawDen := 17 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 15 (rawNum / common) (rawDen / common) d
          (d :: [17])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 18 0).filter
        (admissibleNext [17]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
