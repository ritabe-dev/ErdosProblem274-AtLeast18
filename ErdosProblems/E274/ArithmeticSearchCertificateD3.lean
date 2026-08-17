import ErdosProblems.E274.ArithmeticSearchCertificateD4

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_0 :
    searchIndexLists 14 7 18 9 [9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 10 27).flatMap (fun d =>
      if admissibleNext [9, 6, 3] d then
        let rawNum := 7 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 10 27).filter
        (admissibleNext [9, 6, 3]) =
        [12, 18, 24, 27, 30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_1 :
    searchIndexLists 14 5 12 12 [12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 21).flatMap (fun d =>
      if admissibleNext [12, 6, 3] d then
        let rawNum := 5 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 21).filter
        (admissibleNext [12, 6, 3]) =
        [15, 18, 21, 24, 27, 30, 33] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_2 :
    searchIndexLists 14 13 30 15 [15, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 17).flatMap (fun d =>
      if admissibleNext [15, 6, 3] d then
        let rawNum := 13 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 17).filter
        (admissibleNext [15, 6, 3]) =
        [18, 24, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_3 :
    searchIndexLists 14 4 9 18 [18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 13).flatMap (fun d =>
      if admissibleNext [18, 6, 3] d then
        let rawNum := 4 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 13).filter
        (admissibleNext [18, 6, 3]) =
        [21, 24, 27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_4 :
    searchIndexLists 14 19 42 21 [21, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 9).flatMap (fun d =>
      if admissibleNext [21, 6, 3] d then
        let rawNum := 19 * d - 42
        let rawDen := 42 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [21, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 9).filter
        (admissibleNext [21, 6, 3]) =
        [24, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_5 :
    searchIndexLists 14 11 24 24 [24, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 6).flatMap (fun d =>
      if admissibleNext [24, 6, 3] d then
        let rawNum := 11 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 6).filter
        (admissibleNext [24, 6, 3]) =
        [27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_6 :
    searchIndexLists 14 25 54 27 [27, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 3).flatMap (fun d =>
      if admissibleNext [27, 6, 3] d then
        let rawNum := 25 * d - 54
        let rawDen := 54 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [27, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 3).filter
        (admissibleNext [27, 6, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_7 :
    searchIndexLists 14 7 15 30 [30, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 6, 3] d then
        let rawNum := 7 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [30, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_8 :
    searchIndexLists 14 17 36 12 [12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 17).flatMap (fun d =>
      if admissibleNext [12, 9, 3] d then
        let rawNum := 17 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 17).filter
        (admissibleNext [12, 9, 3]) =
        [18, 24, 27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_9 :
    searchIndexLists 14 22 45 15 [15, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 13).flatMap (fun d =>
      if admissibleNext [15, 9, 3] d then
        let rawNum := 22 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 13).filter
        (admissibleNext [15, 9, 3]) =
        [18, 27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_10 :
    searchIndexLists 14 1 2 18 [18, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 10).flatMap (fun d =>
      if admissibleNext [18, 9, 3] d then
        let rawNum := 1 * d - 2
        let rawDen := 2 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 10).filter
        (admissibleNext [18, 9, 3]) =
        [21, 24, 27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_11 :
    searchIndexLists 14 32 63 21 [21, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 6).flatMap (fun d =>
      if admissibleNext [21, 9, 3] d then
        let rawNum := 32 * d - 63
        let rawDen := 63 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [21, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 6).filter
        (admissibleNext [21, 9, 3]) =
        [27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_12 :
    searchIndexLists 14 37 72 24 [24, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 9, 3] d then
        let rawNum := 37 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 9, 3]) =
        [27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_13 :
    searchIndexLists 14 14 27 27 [27, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 0).flatMap (fun d =>
      if admissibleNext [27, 9, 3] d then
        let rawNum := 14 * d - 27
        let rawDen := 27 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [27, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 0).filter
        (admissibleNext [27, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_14 :
    searchIndexLists 14 31 60 15 [15, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 12).flatMap (fun d =>
      if admissibleNext [15, 12, 3] d then
        let rawNum := 31 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 12).filter
        (admissibleNext [15, 12, 3]) =
        [18, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_15 :
    searchIndexLists 14 19 36 18 [18, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 8).flatMap (fun d =>
      if admissibleNext [18, 12, 3] d then
        let rawNum := 19 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 8).filter
        (admissibleNext [18, 12, 3]) =
        [21, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_16 :
    searchIndexLists 14 15 28 21 [21, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 5).flatMap (fun d =>
      if admissibleNext [21, 12, 3] d then
        let rawNum := 15 * d - 28
        let rawDen := 28 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [21, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 5).filter
        (admissibleNext [21, 12, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_17 :
    searchIndexLists 14 13 24 24 [24, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 12, 3] d then
        let rawNum := 13 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 12, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_18 :
    searchIndexLists 14 49 90 18 [18, 15, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 7).flatMap (fun d =>
      if admissibleNext [18, 15, 3] d then
        let rawNum := 49 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 7).filter
        (admissibleNext [18, 15, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_19 :
    searchIndexLists 14 58 105 21 [21, 15, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 4).flatMap (fun d =>
      if admissibleNext [21, 15, 3] d then
        let rawNum := 58 * d - 105
        let rawDen := 105 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [21, 15, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 4).filter
        (admissibleNext [21, 15, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_20 :
    searchIndexLists 14 67 120 24 [24, 15, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 15, 3] d then
        let rawNum := 67 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 15, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 15, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_21 :
    searchIndexLists 14 71 126 21 [21, 18, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 3).flatMap (fun d =>
      if admissibleNext [21, 18, 3] d then
        let rawNum := 71 * d - 126
        let rawDen := 126 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [21, 18, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 3).filter
        (admissibleNext [21, 18, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_22 :
    searchIndexLists 14 41 72 24 [24, 18, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 18, 3] d then
        let rawNum := 41 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 18, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_23 :
    searchIndexLists 14 97 168 24 [24, 21, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 21, 3] d then
        let rawNum := 97 * d - 168
        let rawDen := 168 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 21, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 21, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_24 :
    searchIndexLists 14 11 24 8 [8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 9 22).flatMap (fun d =>
      if admissibleNext [8, 6, 4] d then
        let rawNum := 11 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 9 22).filter
        (admissibleNext [8, 6, 4]) =
        [12, 16, 18, 24, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_25 :
    searchIndexLists 14 1 2 12 [12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 16).flatMap (fun d =>
      if admissibleNext [12, 6, 4] d then
        let rawNum := 1 * d - 2
        let rawDen := 2 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 16).filter
        (admissibleNext [12, 6, 4]) =
        [16, 18, 20, 24, 28] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_26 :
    searchIndexLists 14 25 48 16 [16, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 10).flatMap (fun d =>
      if admissibleNext [16, 6, 4] d then
        let rawNum := 25 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 10).filter
        (admissibleNext [16, 6, 4]) =
        [18, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_27 :
    searchIndexLists 14 19 36 18 [18, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 8).flatMap (fun d =>
      if admissibleNext [18, 6, 4] d then
        let rawNum := 19 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 8).filter
        (admissibleNext [18, 6, 4]) =
        [20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_28 :
    searchIndexLists 14 8 15 20 [20, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 6).flatMap (fun d =>
      if admissibleNext [20, 6, 4] d then
        let rawNum := 8 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 6).filter
        (admissibleNext [20, 6, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_29 :
    searchIndexLists 14 13 24 24 [24, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 6, 4] d then
        let rawNum := 13 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_30 :
    searchIndexLists 14 21 40 10 [10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 11 16).flatMap (fun d =>
      if admissibleNext [10, 8, 4] d then
        let rawNum := 21 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 11 16).filter
        (admissibleNext [10, 8, 4]) =
        [16, 20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_31 :
    searchIndexLists 14 13 24 12 [12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 13).flatMap (fun d =>
      if admissibleNext [12, 8, 4] d then
        let rawNum := 13 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 13).filter
        (admissibleNext [12, 8, 4]) =
        [16, 18, 20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_32 :
    searchIndexLists 14 31 56 14 [14, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 11).flatMap (fun d =>
      if admissibleNext [14, 8, 4] d then
        let rawNum := 31 * d - 56
        let rawDen := 56 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [14, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 11).filter
        (admissibleNext [14, 8, 4]) =
        [16, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_33 :
    searchIndexLists 14 9 16 16 [16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 8).flatMap (fun d =>
      if admissibleNext [16, 8, 4] d then
        let rawNum := 9 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 8).filter
        (admissibleNext [16, 8, 4]) =
        [18, 20, 22, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_34 :
    searchIndexLists 14 41 72 18 [18, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 6).flatMap (fun d =>
      if admissibleNext [18, 8, 4] d then
        let rawNum := 41 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 6).filter
        (admissibleNext [18, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_35 :
    searchIndexLists 14 23 40 20 [20, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 4).flatMap (fun d =>
      if admissibleNext [20, 8, 4] d then
        let rawNum := 23 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 4).filter
        (admissibleNext [20, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_36 :
    searchIndexLists 14 51 88 22 [22, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 23 2).flatMap (fun d =>
      if admissibleNext [22, 8, 4] d then
        let rawNum := 51 * d - 88
        let rawDen := 88 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [22, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 23 2).filter
        (admissibleNext [22, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_37 :
    searchIndexLists 14 7 12 24 [24, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 8, 4] d then
        let rawNum := 7 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [24, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_38 :
    searchIndexLists 14 17 30 12 [12, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 12).flatMap (fun d =>
      if admissibleNext [12, 10, 4] d then
        let rawNum := 17 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 12).filter
        (admissibleNext [12, 10, 4]) =
        [20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_39 :
    searchIndexLists 14 47 80 16 [16, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 7).flatMap (fun d =>
      if admissibleNext [16, 10, 4] d then
        let rawNum := 47 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 7).filter
        (admissibleNext [16, 10, 4]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_40 :
    searchIndexLists 14 3 5 20 [20, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 3).flatMap (fun d =>
      if admissibleNext [20, 10, 4] d then
        let rawNum := 3 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 3).filter
        (admissibleNext [20, 10, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_41 :
    searchIndexLists 14 25 42 14 [14, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 9).flatMap (fun d =>
      if admissibleNext [14, 12, 4] d then
        let rawNum := 25 * d - 42
        let rawDen := 42 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [14, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 9).filter
        (admissibleNext [14, 12, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_42 :
    searchIndexLists 14 29 48 16 [16, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 7).flatMap (fun d =>
      if admissibleNext [16, 12, 4] d then
        let rawNum := 29 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 7).filter
        (admissibleNext [16, 12, 4]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_43 :
    searchIndexLists 14 11 18 18 [18, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 4).flatMap (fun d =>
      if admissibleNext [18, 12, 4] d then
        let rawNum := 11 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 4).filter
        (admissibleNext [18, 12, 4]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_44 :
    searchIndexLists 14 37 60 20 [20, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 12, 4] d then
        let rawNum := 37 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 12, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_45 :
    searchIndexLists 14 41 66 22 [22, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 23 0).flatMap (fun d =>
      if admissibleNext [22, 12, 4] d then
        let rawNum := 41 * d - 66
        let rawDen := 66 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [22, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 23 0).filter
        (admissibleNext [22, 12, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_46 :
    searchIndexLists 14 69 112 16 [16, 14, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 6).flatMap (fun d =>
      if admissibleNext [16, 14, 4] d then
        let rawNum := 69 * d - 112
        let rawDen := 112 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 14, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 6).filter
        (admissibleNext [16, 14, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_47 :
    searchIndexLists 14 22 35 20 [20, 14, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 14, 4] d then
        let rawNum := 22 * d - 35
        let rawDen := 35 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 14, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 14, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_48 :
    searchIndexLists 14 91 144 18 [18, 16, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 4).flatMap (fun d =>
      if admissibleNext [18, 16, 4] d then
        let rawNum := 91 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 4).filter
        (admissibleNext [18, 16, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_49 :
    searchIndexLists 14 51 80 20 [20, 16, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 16, 4] d then
        let rawNum := 51 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 16, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_50 :
    searchIndexLists 14 29 45 20 [20, 18, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 18, 4] d then
        let rawNum := 29 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 18, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_51 :
    searchIndexLists 14 19 30 15 [15, 10, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 7).flatMap (fun d =>
      if admissibleNext [15, 10, 5] d then
        let rawNum := 19 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 10, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 7).filter
        (admissibleNext [15, 10, 5]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_52 :
    searchIndexLists 14 13 20 20 [20, 10, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 10, 5] d then
        let rawNum := 13 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 10, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 10, 5]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_53 :
    searchIndexLists 14 41 60 20 [20, 15, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 15, 5] d then
        let rawNum := 41 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 15, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 15, 5]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_54 :
    searchIndexLists 14 5 8 12 [12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 10).flatMap (fun d =>
      if admissibleNext [12, 8, 6] d then
        let rawNum := 5 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 10).filter
        (admissibleNext [12, 8, 6]) =
        [16, 18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_55 :
    searchIndexLists 14 31 48 16 [16, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 5).flatMap (fun d =>
      if admissibleNext [16, 8, 6] d then
        let rawNum := 31 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 5).filter
        (admissibleNext [16, 8, 6]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_56 :
    searchIndexLists 14 47 72 18 [18, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 3).flatMap (fun d =>
      if admissibleNext [18, 8, 6] d then
        let rawNum := 47 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 3).filter
        (admissibleNext [18, 8, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_57 :
    searchIndexLists 14 79 120 20 [20, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 8, 6] d then
        let rawNum := 79 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_58 :
    searchIndexLists 14 23 36 12 [12, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 9).flatMap (fun d =>
      if admissibleNext [12, 9, 6] d then
        let rawNum := 23 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 9).filter
        (admissibleNext [12, 9, 6]) =
        [15, 18, 21] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_59 :
    searchIndexLists 14 59 90 15 [15, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 6).flatMap (fun d =>
      if admissibleNext [15, 9, 6] d then
        let rawNum := 59 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 6).filter
        (admissibleNext [15, 9, 6]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_60 :
    searchIndexLists 14 2 3 18 [18, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 3).flatMap (fun d =>
      if admissibleNext [18, 9, 6] d then
        let rawNum := 2 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 3).filter
        (admissibleNext [18, 9, 6]) =
        [21] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_61 :
    searchIndexLists 14 13 20 12 [12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 9).flatMap (fun d =>
      if admissibleNext [12, 10, 6] d then
        let rawNum := 13 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 9).filter
        (admissibleNext [12, 10, 6]) =
        [15, 18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_62 :
    searchIndexLists 14 2 3 15 [15, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 6).flatMap (fun d =>
      if admissibleNext [15, 10, 6] d then
        let rawNum := 2 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 6).filter
        (admissibleNext [15, 10, 6]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_63 :
    searchIndexLists 14 61 90 18 [18, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 2).flatMap (fun d =>
      if admissibleNext [18, 10, 6] d then
        let rawNum := 61 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 2).filter
        (admissibleNext [18, 10, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_64 :
    searchIndexLists 14 41 60 20 [20, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 10, 6] d then
        let rawNum := 41 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_65 :
    searchIndexLists 14 19 28 14 [14, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 6).flatMap (fun d =>
      if admissibleNext [14, 12, 6] d then
        let rawNum := 19 * d - 28
        let rawDen := 28 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [14, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 6).filter
        (admissibleNext [14, 12, 6]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_66 :
    searchIndexLists 14 41 60 15 [15, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 5).flatMap (fun d =>
      if admissibleNext [15, 12, 6] d then
        let rawNum := 41 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 5).filter
        (admissibleNext [15, 12, 6]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_67 :
    searchIndexLists 14 11 16 16 [16, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 4).flatMap (fun d =>
      if admissibleNext [16, 12, 6] d then
        let rawNum := 11 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 4).filter
        (admissibleNext [16, 12, 6]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_68 :
    searchIndexLists 14 25 36 18 [18, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 2).flatMap (fun d =>
      if admissibleNext [18, 12, 6] d then
        let rawNum := 25 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 2).filter
        (admissibleNext [18, 12, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_69 :
    searchIndexLists 14 7 10 20 [20, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 12, 6] d then
        let rawNum := 7 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_70 :
    searchIndexLists 14 89 126 18 [18, 14, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 14, 6] d then
        let rawNum := 89 * d - 126
        let rawDen := 126 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 14, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 14, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_71 :
    searchIndexLists 14 32 45 18 [18, 15, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 15, 6] d then
        let rawNum := 32 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 15, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_72 :
    searchIndexLists 14 103 144 18 [18, 16, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 16, 6] d then
        let rawNum := 103 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 16, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_73 :
    searchIndexLists 14 83 120 12 [12, 10, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 8).flatMap (fun d =>
      if admissibleNext [12, 10, 8] d then
        let rawNum := 83 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [12, 10, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 8).filter
        (admissibleNext [12, 10, 8]) =
        [16, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_74 :
    searchIndexLists 14 57 80 16 [16, 10, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 3).flatMap (fun d =>
      if admissibleNext [16, 10, 8] d then
        let rawNum := 57 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 10, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 3).filter
        (admissibleNext [16, 10, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_75 :
    searchIndexLists 14 121 168 14 [14, 12, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 15 5).flatMap (fun d =>
      if admissibleNext [14, 12, 8] d then
        let rawNum := 121 * d - 168
        let rawDen := 168 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [14, 12, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 15 5).filter
        (admissibleNext [14, 12, 8]) =
        [16] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_76 :
    searchIndexLists 14 35 48 16 [16, 12, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 3).flatMap (fun d =>
      if admissibleNext [16, 12, 8] d then
        let rawNum := 35 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 3).filter
        (admissibleNext [16, 12, 8]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_77 :
    searchIndexLists 14 53 72 18 [18, 12, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 12, 8] d then
        let rawNum := 53 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 12, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_78 :
    searchIndexLists 14 83 112 16 [16, 14, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 2).flatMap (fun d =>
      if admissibleNext [16, 14, 8] d then
        let rawNum := 83 * d - 112
        let rawDen := 112 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 14, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 2).filter
        (admissibleNext [16, 14, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_79 :
    searchIndexLists 14 109 144 18 [18, 16, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 16, 8] d then
        let rawNum := 109 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 16, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_80 :
    searchIndexLists 14 133 180 15 [15, 12, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 3).flatMap (fun d =>
      if admissibleNext [15, 12, 9] d then
        let rawNum := 133 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 3).filter
        (admissibleNext [15, 12, 9]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_81 :
    searchIndexLists 14 3 4 18 [18, 12, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 12, 9] d then
        let rawNum := 3 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 12, 9]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_82 :
    searchIndexLists 14 23 30 18 [18, 15, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 15, 9] d then
        let rawNum := 23 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 15, 9]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_83 :
    searchIndexLists 14 3 4 15 [15, 12, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 3).flatMap (fun d =>
      if admissibleNext [15, 12, 10] d then
        let rawNum := 3 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 3).filter
        (admissibleNext [15, 12, 10]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_84 :
    searchIndexLists 14 181 240 16 [16, 12, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 2).flatMap (fun d =>
      if admissibleNext [16, 12, 10] d then
        let rawNum := 181 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 2).filter
        (admissibleNext [16, 12, 10]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_85 :
    searchIndexLists 14 137 180 18 [18, 12, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 12, 10] d then
        let rawNum := 137 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 12, 10]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_86 :
    searchIndexLists 14 7 9 18 [18, 15, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 15, 10] d then
        let rawNum := 7 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 15, 10]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD3_87 :
    searchIndexLists 14 263 336 16 [16, 14, 12] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 1).flatMap (fun d =>
      if admissibleNext [16, 14, 12] d then
        let rawNum := 263 * d - 336
        let rawDen := 336 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 13 (rawNum / common) (rawDen / common) d
          (d :: [16, 14, 12])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 1).filter
        (admissibleNext [16, 14, 12]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
