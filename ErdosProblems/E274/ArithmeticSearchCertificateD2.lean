import ErdosProblems.E274.ArithmeticSearchCertificateD3

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_0 :
    searchIndexLists 15 1 2 6 [6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 7 24).flatMap (fun d =>
      if admissibleNext [6, 3] d then
        let rawNum := 1 * d - 2
        let rawDen := 2 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 7 24).filter
        (admissibleNext [6, 3]) =
        [9, 12, 15, 18, 21, 24, 27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_1 :
    searchIndexLists 15 5 9 9 [9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 10 18).flatMap (fun d =>
      if admissibleNext [9, 3] d then
        let rawNum := 5 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 10 18).filter
        (admissibleNext [9, 3]) =
        [12, 15, 18, 21, 24, 27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_2 :
    searchIndexLists 15 7 12 12 [12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 13).flatMap (fun d =>
      if admissibleNext [12, 3] d then
        let rawNum := 7 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 13).filter
        (admissibleNext [12, 3]) =
        [15, 18, 21, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_3 :
    searchIndexLists 15 3 5 15 [15, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 10).flatMap (fun d =>
      if admissibleNext [15, 3] d then
        let rawNum := 3 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [15, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 10).filter
        (admissibleNext [15, 3]) =
        [18, 21, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_4 :
    searchIndexLists 15 11 18 18 [18, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 6).flatMap (fun d =>
      if admissibleNext [18, 3] d then
        let rawNum := 11 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [18, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 6).filter
        (admissibleNext [18, 3]) =
        [21, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_5 :
    searchIndexLists 15 13 21 21 [21, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 3).flatMap (fun d =>
      if admissibleNext [21, 3] d then
        let rawNum := 13 * d - 21
        let rawDen := 21 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [21, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 3).filter
        (admissibleNext [21, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_6 :
    searchIndexLists 15 5 8 24 [24, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 3] d then
        let rawNum := 5 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [24, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_7 :
    searchIndexLists 15 7 12 6 [6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 7 19).flatMap (fun d =>
      if admissibleNext [6, 4] d then
        let rawNum := 7 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 7 19).filter
        (admissibleNext [6, 4]) =
        [8, 12, 16, 18, 20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_8 :
    searchIndexLists 15 5 8 8 [8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 9 16).flatMap (fun d =>
      if admissibleNext [8, 4] d then
        let rawNum := 5 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 9 16).filter
        (admissibleNext [8, 4]) =
        [10, 12, 14, 16, 18, 20, 22, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_9 :
    searchIndexLists 15 13 20 10 [10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 11 13).flatMap (fun d =>
      if admissibleNext [10, 4] d then
        let rawNum := 13 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 11 13).filter
        (admissibleNext [10, 4]) =
        [12, 16, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_10 :
    searchIndexLists 15 2 3 12 [12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 10).flatMap (fun d =>
      if admissibleNext [12, 4] d then
        let rawNum := 2 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 10).filter
        (admissibleNext [12, 4]) =
        [14, 16, 18, 20, 22] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_11 :
    searchIndexLists 15 19 28 14 [14, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 8).flatMap (fun d =>
      if admissibleNext [14, 4] d then
        let rawNum := 19 * d - 28
        let rawDen := 28 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [14, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 8).filter
        (admissibleNext [14, 4]) =
        [16, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_12 :
    searchIndexLists 15 11 16 16 [16, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 5).flatMap (fun d =>
      if admissibleNext [16, 4] d then
        let rawNum := 11 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [16, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 5).filter
        (admissibleNext [16, 4]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_13 :
    searchIndexLists 15 25 36 18 [18, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 3).flatMap (fun d =>
      if admissibleNext [18, 4] d then
        let rawNum := 25 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [18, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 3).filter
        (admissibleNext [18, 4]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_14 :
    searchIndexLists 15 7 10 20 [20, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 4] d then
        let rawNum := 7 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [20, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_15 :
    searchIndexLists 15 7 10 10 [10, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 11 11).flatMap (fun d =>
      if admissibleNext [10, 5] d then
        let rawNum := 7 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [10, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 11 11).filter
        (admissibleNext [10, 5]) =
        [15, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_16 :
    searchIndexLists 15 11 15 15 [15, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 5).flatMap (fun d =>
      if admissibleNext [15, 5] d then
        let rawNum := 11 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [15, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 5).filter
        (admissibleNext [15, 5]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_17 :
    searchIndexLists 15 3 4 20 [20, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 5] d then
        let rawNum := 3 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [20, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 5]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_18 :
    searchIndexLists 15 17 24 8 [8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 9 13).flatMap (fun d =>
      if admissibleNext [8, 6] d then
        let rawNum := 17 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 9 13).filter
        (admissibleNext [8, 6]) =
        [12, 16, 18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_19 :
    searchIndexLists 15 13 18 9 [9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 10 11).flatMap (fun d =>
      if admissibleNext [9, 6] d then
        let rawNum := 13 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 10 11).filter
        (admissibleNext [9, 6]) =
        [12, 15, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_20 :
    searchIndexLists 15 11 15 10 [10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 11 10).flatMap (fun d =>
      if admissibleNext [10, 6] d then
        let rawNum := 11 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 11 10).filter
        (admissibleNext [10, 6]) =
        [12, 15, 18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_21 :
    searchIndexLists 15 3 4 12 [12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 8).flatMap (fun d =>
      if admissibleNext [12, 6] d then
        let rawNum := 3 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 8).filter
        (admissibleNext [12, 6]) =
        [14, 15, 16, 18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_22 :
    searchIndexLists 15 16 21 14 [14, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 5).flatMap (fun d =>
      if admissibleNext [14, 6] d then
        let rawNum := 16 * d - 21
        let rawDen := 21 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [14, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 5).filter
        (admissibleNext [14, 6]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_23 :
    searchIndexLists 15 23 30 15 [15, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 4).flatMap (fun d =>
      if admissibleNext [15, 6] d then
        let rawNum := 23 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [15, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 4).filter
        (admissibleNext [15, 6]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_24 :
    searchIndexLists 15 37 48 16 [16, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 3).flatMap (fun d =>
      if admissibleNext [16, 6] d then
        let rawNum := 37 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [16, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 3).filter
        (admissibleNext [16, 6]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_25 :
    searchIndexLists 15 7 9 18 [18, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 6] d then
        let rawNum := 7 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [18, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_26 :
    searchIndexLists 15 11 14 14 [14, 7] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 5).flatMap (fun d =>
      if admissibleNext [14, 7] d then
        let rawNum := 11 * d - 14
        let rawDen := 14 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [14, 7])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 5).filter
        (admissibleNext [14, 7]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_27 :
    searchIndexLists 15 31 40 10 [10, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 11 9).flatMap (fun d =>
      if admissibleNext [10, 8] d then
        let rawNum := 31 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [10, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 11 9).filter
        (admissibleNext [10, 8]) =
        [12, 16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_28 :
    searchIndexLists 15 19 24 12 [12, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 6).flatMap (fun d =>
      if admissibleNext [12, 8] d then
        let rawNum := 19 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [12, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 6).filter
        (admissibleNext [12, 8]) =
        [14, 16, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_29 :
    searchIndexLists 15 45 56 14 [14, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 4).flatMap (fun d =>
      if admissibleNext [14, 8] d then
        let rawNum := 45 * d - 56
        let rawDen := 56 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [14, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 4).filter
        (admissibleNext [14, 8]) =
        [16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_30 :
    searchIndexLists 15 13 16 16 [16, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 2).flatMap (fun d =>
      if admissibleNext [16, 8] d then
        let rawNum := 13 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [16, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 2).filter
        (admissibleNext [16, 8]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_31 :
    searchIndexLists 15 59 72 18 [18, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 8] d then
        let rawNum := 59 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [18, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_32 :
    searchIndexLists 15 29 36 12 [12, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 6).flatMap (fun d =>
      if admissibleNext [12, 9] d then
        let rawNum := 29 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [12, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 6).filter
        (admissibleNext [12, 9]) =
        [15, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_33 :
    searchIndexLists 15 37 45 15 [15, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 3).flatMap (fun d =>
      if admissibleNext [15, 9] d then
        let rawNum := 37 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [15, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 3).filter
        (admissibleNext [15, 9]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_34 :
    searchIndexLists 15 5 6 18 [18, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 9] d then
        let rawNum := 5 * d - 6
        let rawDen := 6 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [18, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 9]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_35 :
    searchIndexLists 15 49 60 12 [12, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 6).flatMap (fun d =>
      if admissibleNext [12, 10] d then
        let rawNum := 49 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [12, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 6).filter
        (admissibleNext [12, 10]) =
        [15, 16, 18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_36 :
    searchIndexLists 15 29 35 14 [14, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 4).flatMap (fun d =>
      if admissibleNext [14, 10] d then
        let rawNum := 29 * d - 35
        let rawDen := 35 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [14, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 4).filter
        (admissibleNext [14, 10]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_37 :
    searchIndexLists 15 5 6 15 [15, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 3).flatMap (fun d =>
      if admissibleNext [15, 10] d then
        let rawNum := 5 * d - 6
        let rawDen := 6 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [15, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 3).filter
        (admissibleNext [15, 10]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_38 :
    searchIndexLists 15 67 80 16 [16, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 1).flatMap (fun d =>
      if admissibleNext [16, 10] d then
        let rawNum := 67 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [16, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 1).filter
        (admissibleNext [16, 10]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_39 :
    searchIndexLists 15 71 84 14 [14, 12] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 3).flatMap (fun d =>
      if admissibleNext [14, 12] d then
        let rawNum := 71 * d - 84
        let rawDen := 84 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [14, 12])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 3).filter
        (admissibleNext [14, 12]) =
        [16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_40 :
    searchIndexLists 15 17 20 15 [15, 12] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 2).flatMap (fun d =>
      if admissibleNext [15, 12] d then
        let rawNum := 17 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [15, 12])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 2).filter
        (admissibleNext [15, 12]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_41 :
    searchIndexLists 15 41 48 16 [16, 12] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 1).flatMap (fun d =>
      if admissibleNext [16, 12] d then
        let rawNum := 41 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [16, 12])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 1).filter
        (admissibleNext [16, 12]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD2_42 :
    searchIndexLists 15 97 112 16 [16, 14] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 1).flatMap (fun d =>
      if admissibleNext [16, 14] d then
        let rawNum := 97 * d - 112
        let rawDen := 112 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 14 (rawNum / common) (rawDen / common) d
          (d :: [16, 14])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 1).filter
        (admissibleNext [16, 14]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
