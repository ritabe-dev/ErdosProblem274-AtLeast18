import ErdosProblems.E274.ArithmeticSearchCertificateD5

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_0 :
    searchIndexLists 13 11 36 12 [12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 13 30).flatMap (fun d =>
      if admissibleNext [12, 9, 6, 3] d then
        let rawNum := 11 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 30).filter
        (admissibleNext [12, 9, 6, 3]) =
        [18, 24, 27, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_1 :
    searchIndexLists 13 1 3 18 [18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 21).flatMap (fun d =>
      if admissibleNext [18, 9, 6, 3] d then
        let rawNum := 1 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 21).filter
        (admissibleNext [18, 9, 6, 3]) =
        [24, 27, 30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_2 :
    searchIndexLists 13 25 72 24 [24, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 13).flatMap (fun d =>
      if admissibleNext [24, 9, 6, 3] d then
        let rawNum := 25 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 13).filter
        (admissibleNext [24, 9, 6, 3]) =
        [27, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_3 :
    searchIndexLists 13 19 54 27 [27, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 9).flatMap (fun d =>
      if admissibleNext [27, 9, 6, 3] d then
        let rawNum := 19 * d - 54
        let rawDen := 54 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 9).filter
        (admissibleNext [27, 9, 6, 3]) =
        [30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_4 :
    searchIndexLists 13 16 45 30 [30, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 6).flatMap (fun d =>
      if admissibleNext [30, 9, 6, 3] d then
        let rawNum := 16 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 6).filter
        (admissibleNext [30, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_5 :
    searchIndexLists 13 13 36 36 [36, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 9, 6, 3] d then
        let rawNum := 13 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [36, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_6 :
    searchIndexLists 13 7 20 15 [15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 22).flatMap (fun d =>
      if admissibleNext [15, 12, 6, 3] d then
        let rawNum := 7 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 22).filter
        (admissibleNext [15, 12, 6, 3]) =
        [24, 30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_7 :
    searchIndexLists 13 13 36 18 [18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 18).flatMap (fun d =>
      if admissibleNext [18, 12, 6, 3] d then
        let rawNum := 13 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 18).filter
        (admissibleNext [18, 12, 6, 3]) =
        [24, 27, 30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_8 :
    searchIndexLists 13 31 84 21 [21, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 14).flatMap (fun d =>
      if admissibleNext [21, 12, 6, 3] d then
        let rawNum := 31 * d - 84
        let rawDen := 84 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [21, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 14).filter
        (admissibleNext [21, 12, 6, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_9 :
    searchIndexLists 13 3 8 24 [24, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 10).flatMap (fun d =>
      if admissibleNext [24, 12, 6, 3] d then
        let rawNum := 3 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 10).filter
        (admissibleNext [24, 12, 6, 3]) =
        [27, 30, 33] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_10 :
    searchIndexLists 13 41 108 27 [27, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 7).flatMap (fun d =>
      if admissibleNext [27, 12, 6, 3] d then
        let rawNum := 41 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 7).filter
        (admissibleNext [27, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_11 :
    searchIndexLists 13 23 60 30 [30, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 3).flatMap (fun d =>
      if admissibleNext [30, 12, 6, 3] d then
        let rawNum := 23 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 3).filter
        (admissibleNext [30, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_12 :
    searchIndexLists 13 17 44 33 [33, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 34 0).flatMap (fun d =>
      if admissibleNext [33, 12, 6, 3] d then
        let rawNum := 17 * d - 44
        let rawDen := 44 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [33, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 34 0).filter
        (admissibleNext [33, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_13 :
    searchIndexLists 13 17 45 18 [18, 15, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 16).flatMap (fun d =>
      if admissibleNext [18, 15, 6, 3] d then
        let rawNum := 17 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 16).filter
        (admissibleNext [18, 15, 6, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_14 :
    searchIndexLists 13 47 120 24 [24, 15, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 9).flatMap (fun d =>
      if admissibleNext [24, 15, 6, 3] d then
        let rawNum := 47 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 15, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 9).filter
        (admissibleNext [24, 15, 6, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_15 :
    searchIndexLists 13 2 5 30 [30, 15, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 15, 6, 3] d then
        let rawNum := 2 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 15, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 15, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_16 :
    searchIndexLists 13 25 63 21 [21, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 11).flatMap (fun d =>
      if admissibleNext [21, 18, 6, 3] d then
        let rawNum := 25 * d - 63
        let rawDen := 63 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [21, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 11).filter
        (admissibleNext [21, 18, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_17 :
    searchIndexLists 13 29 72 24 [24, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 8).flatMap (fun d =>
      if admissibleNext [24, 18, 6, 3] d then
        let rawNum := 29 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 8).filter
        (admissibleNext [24, 18, 6, 3]) =
        [27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_18 :
    searchIndexLists 13 11 27 27 [27, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 4).flatMap (fun d =>
      if admissibleNext [27, 18, 6, 3] d then
        let rawNum := 11 * d - 27
        let rawDen := 27 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 4).filter
        (admissibleNext [27, 18, 6, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_19 :
    searchIndexLists 13 37 90 30 [30, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 18, 6, 3] d then
        let rawNum := 37 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 18, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_20 :
    searchIndexLists 13 23 56 24 [24, 21, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 7).flatMap (fun d =>
      if admissibleNext [24, 21, 6, 3] d then
        let rawNum := 23 * d - 56
        let rawDen := 56 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 21, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 7).filter
        (admissibleNext [24, 21, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_21 :
    searchIndexLists 13 44 105 30 [30, 21, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 21, 6, 3] d then
        let rawNum := 44 * d - 105
        let rawDen := 105 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 21, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 21, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_22 :
    searchIndexLists 13 91 216 27 [27, 24, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 3).flatMap (fun d =>
      if admissibleNext [27, 24, 6, 3] d then
        let rawNum := 91 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 3).filter
        (admissibleNext [27, 24, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_23 :
    searchIndexLists 13 17 40 30 [30, 24, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 24, 6, 3] d then
        let rawNum := 17 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 24, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_24 :
    searchIndexLists 13 58 135 30 [30, 27, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 27, 6, 3] d then
        let rawNum := 58 * d - 135
        let rawDen := 135 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 27, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_25 :
    searchIndexLists 13 5 12 18 [18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 13).flatMap (fun d =>
      if admissibleNext [18, 12, 9, 3] d then
        let rawNum := 5 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 13).filter
        (admissibleNext [18, 12, 9, 3]) =
        [24, 27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_26 :
    searchIndexLists 13 31 72 24 [24, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 6).flatMap (fun d =>
      if admissibleNext [24, 12, 9, 3] d then
        let rawNum := 31 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 6).filter
        (admissibleNext [24, 12, 9, 3]) =
        [27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_27 :
    searchIndexLists 13 47 108 27 [27, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 2).flatMap (fun d =>
      if admissibleNext [27, 12, 9, 3] d then
        let rawNum := 47 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 2).filter
        (admissibleNext [27, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_28 :
    searchIndexLists 13 13 30 18 [18, 15, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 12).flatMap (fun d =>
      if admissibleNext [18, 15, 9, 3] d then
        let rawNum := 13 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 12).filter
        (admissibleNext [18, 15, 9, 3]) =
        [27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_29 :
    searchIndexLists 13 61 135 27 [27, 15, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 1).flatMap (fun d =>
      if admissibleNext [27, 15, 9, 3] d then
        let rawNum := 61 * d - 135
        let rawDen := 135 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 15, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 1).filter
        (admissibleNext [27, 15, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_30 :
    searchIndexLists 13 19 42 21 [21, 18, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 7).flatMap (fun d =>
      if admissibleNext [21, 18, 9, 3] d then
        let rawNum := 19 * d - 42
        let rawDen := 42 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [21, 18, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 7).filter
        (admissibleNext [21, 18, 9, 3]) =
        [27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_31 :
    searchIndexLists 13 11 24 24 [24, 18, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 18, 9, 3] d then
        let rawNum := 11 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 18, 9, 3]) =
        [27] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_32 :
    searchIndexLists 13 25 54 27 [27, 18, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 1).flatMap (fun d =>
      if admissibleNext [27, 18, 9, 3] d then
        let rawNum := 25 * d - 54
        let rawDen := 54 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 1).filter
        (admissibleNext [27, 18, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_33 :
    searchIndexLists 13 89 189 27 [27, 21, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 0).flatMap (fun d =>
      if admissibleNext [27, 21, 9, 3] d then
        let rawNum := 89 * d - 189
        let rawDen := 189 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 21, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 0).filter
        (admissibleNext [27, 21, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_34 :
    searchIndexLists 13 103 216 27 [27, 24, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 0).flatMap (fun d =>
      if admissibleNext [27, 24, 9, 3] d then
        let rawNum := 103 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 0).filter
        (admissibleNext [27, 24, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_35 :
    searchIndexLists 13 83 180 18 [18, 15, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 10).flatMap (fun d =>
      if admissibleNext [18, 15, 12, 3] d then
        let rawNum := 83 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 10).filter
        (admissibleNext [18, 15, 12, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_36 :
    searchIndexLists 13 19 40 24 [24, 15, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 15, 12, 3] d then
        let rawNum := 19 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 15, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 15, 12, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_37 :
    searchIndexLists 13 121 252 21 [21, 18, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 6).flatMap (fun d =>
      if admissibleNext [21, 18, 12, 3] d then
        let rawNum := 121 * d - 252
        let rawDen := 252 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [21, 18, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 6).filter
        (admissibleNext [21, 18, 12, 3]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_38 :
    searchIndexLists 13 35 72 24 [24, 18, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 3] d then
        let rawNum := 35 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 18, 12, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_39 :
    searchIndexLists 13 83 168 24 [24, 21, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 21, 12, 3] d then
        let rawNum := 83 * d - 168
        let rawDen := 168 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 21, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 21, 12, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_40 :
    searchIndexLists 13 181 360 24 [24, 18, 15, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 18, 15, 3] d then
        let rawNum := 181 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 15, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 18, 15, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_41 :
    searchIndexLists 13 263 504 24 [24, 21, 18, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 21, 18, 3] d then
        let rawNum := 263 * d - 504
        let rawDen := 504 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 21, 18, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 21, 18, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_42 :
    searchIndexLists 13 3 8 12 [12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 13 22).flatMap (fun d =>
      if admissibleNext [12, 8, 6, 4] d then
        let rawNum := 3 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 13 22).filter
        (admissibleNext [12, 8, 6, 4]) =
        [16, 18, 24, 30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_43 :
    searchIndexLists 13 19 48 16 [16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 16).flatMap (fun d =>
      if admissibleNext [16, 8, 6, 4] d then
        let rawNum := 19 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 16).filter
        (admissibleNext [16, 8, 6, 4]) =
        [18, 24, 30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_44 :
    searchIndexLists 13 29 72 18 [18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 14).flatMap (fun d =>
      if admissibleNext [18, 8, 6, 4] d then
        let rawNum := 29 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 14).filter
        (admissibleNext [18, 8, 6, 4]) =
        [24, 30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_45 :
    searchIndexLists 13 5 12 24 [24, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 7).flatMap (fun d =>
      if admissibleNext [24, 8, 6, 4] d then
        let rawNum := 5 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 7).filter
        (admissibleNext [24, 8, 6, 4]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_46 :
    searchIndexLists 13 17 40 30 [30, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 8, 6, 4] d then
        let rawNum := 17 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [30, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_47 :
    searchIndexLists 13 7 16 16 [16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 13).flatMap (fun d =>
      if admissibleNext [16, 12, 6, 4] d then
        let rawNum := 7 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 13).filter
        (admissibleNext [16, 12, 6, 4]) =
        [18, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_48 :
    searchIndexLists 13 4 9 18 [18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 11).flatMap (fun d =>
      if admissibleNext [18, 12, 6, 4] d then
        let rawNum := 4 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 11).filter
        (admissibleNext [18, 12, 6, 4]) =
        [20, 24, 28] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_49 :
    searchIndexLists 13 9 20 20 [20, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 8).flatMap (fun d =>
      if admissibleNext [20, 12, 6, 4] d then
        let rawNum := 9 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 8).filter
        (admissibleNext [20, 12, 6, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_50 :
    searchIndexLists 13 11 24 24 [24, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 12, 6, 4] d then
        let rawNum := 11 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 12, 6, 4]) =
        [28] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_51 :
    searchIndexLists 13 13 28 28 [28, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 29 0).flatMap (fun d =>
      if admissibleNext [28, 12, 6, 4] d then
        let rawNum := 13 * d - 28
        let rawDen := 28 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [28, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 29 0).filter
        (admissibleNext [28, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_52 :
    searchIndexLists 13 67 144 18 [18, 16, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 9).flatMap (fun d =>
      if admissibleNext [18, 16, 6, 4] d then
        let rawNum := 67 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 9).filter
        (admissibleNext [18, 16, 6, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_53 :
    searchIndexLists 13 23 48 24 [24, 16, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 16, 6, 4] d then
        let rawNum := 23 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 16, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_54 :
    searchIndexLists 13 43 90 20 [20, 18, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 7).flatMap (fun d =>
      if admissibleNext [20, 18, 6, 4] d then
        let rawNum := 43 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 7).filter
        (admissibleNext [20, 18, 6, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_55 :
    searchIndexLists 13 35 72 24 [24, 18, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 18, 6, 4] d then
        let rawNum := 35 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 18, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_56 :
    searchIndexLists 13 59 120 24 [24, 20, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 20, 6, 4] d then
        let rawNum := 59 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 20, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_57 :
    searchIndexLists 13 37 80 16 [16, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 12).flatMap (fun d =>
      if admissibleNext [16, 10, 8, 4] d then
        let rawNum := 37 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 12).filter
        (admissibleNext [16, 10, 8, 4]) =
        [20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_58 :
    searchIndexLists 13 19 40 20 [20, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 7).flatMap (fun d =>
      if admissibleNext [20, 10, 8, 4] d then
        let rawNum := 19 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 7).filter
        (admissibleNext [20, 10, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_59 :
    searchIndexLists 13 29 60 24 [24, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 10, 8, 4] d then
        let rawNum := 29 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 10, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_60 :
    searchIndexLists 13 23 48 16 [16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 11).flatMap (fun d =>
      if admissibleNext [16, 12, 8, 4] d then
        let rawNum := 23 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 11).filter
        (admissibleNext [16, 12, 8, 4]) =
        [18, 20, 24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_61 :
    searchIndexLists 13 35 72 18 [18, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 8).flatMap (fun d =>
      if admissibleNext [18, 12, 8, 4] d then
        let rawNum := 35 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 8).filter
        (admissibleNext [18, 12, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_62 :
    searchIndexLists 13 59 120 20 [20, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 6).flatMap (fun d =>
      if admissibleNext [20, 12, 8, 4] d then
        let rawNum := 59 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 6).filter
        (admissibleNext [20, 12, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_63 :
    searchIndexLists 13 1 2 24 [24, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 12, 8, 4] d then
        let rawNum := 1 * d - 2
        let rawDen := 2 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 12, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_64 :
    searchIndexLists 13 55 112 16 [16, 14, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 10).flatMap (fun d =>
      if admissibleNext [16, 14, 8, 4] d then
        let rawNum := 55 * d - 112
        let rawDen := 112 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 14, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 10).filter
        (admissibleNext [16, 14, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_65 :
    searchIndexLists 13 43 84 24 [24, 14, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 14, 8, 4] d then
        let rawNum := 43 * d - 84
        let rawDen := 84 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 14, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 14, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_66 :
    searchIndexLists 13 73 144 18 [18, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 7).flatMap (fun d =>
      if admissibleNext [18, 16, 8, 4] d then
        let rawNum := 73 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 7).filter
        (admissibleNext [18, 16, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_67 :
    searchIndexLists 13 41 80 20 [20, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 5).flatMap (fun d =>
      if admissibleNext [20, 16, 8, 4] d then
        let rawNum := 41 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 5).filter
        (admissibleNext [20, 16, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_68 :
    searchIndexLists 13 91 176 22 [22, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 23 3).flatMap (fun d =>
      if admissibleNext [22, 16, 8, 4] d then
        let rawNum := 91 * d - 176
        let rawDen := 176 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [22, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 23 3).filter
        (admissibleNext [22, 16, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_69 :
    searchIndexLists 13 25 48 24 [24, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 16, 8, 4] d then
        let rawNum := 25 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 16, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_70 :
    searchIndexLists 13 19 36 24 [24, 18, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 18, 8, 4] d then
        let rawNum := 19 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 18, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_71 :
    searchIndexLists 13 8 15 24 [24, 20, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 20, 8, 4] d then
        let rawNum := 8 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 20, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_72 :
    searchIndexLists 13 71 132 24 [24, 22, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 22, 8, 4] d then
        let rawNum := 71 * d - 132
        let rawDen := 132 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 22, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 22, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_73 :
    searchIndexLists 13 31 60 20 [20, 12, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 5).flatMap (fun d =>
      if admissibleNext [20, 12, 10, 4] d then
        let rawNum := 31 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 5).filter
        (admissibleNext [20, 12, 10, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_74 :
    searchIndexLists 13 21 40 24 [24, 12, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 12, 10, 4] d then
        let rawNum := 21 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 12, 10, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_75 :
    searchIndexLists 13 43 80 20 [20, 16, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 4).flatMap (fun d =>
      if admissibleNext [20, 16, 10, 4] d then
        let rawNum := 43 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 4).filter
        (admissibleNext [20, 16, 10, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_76 :
    searchIndexLists 13 79 144 18 [18, 16, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 5).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 4] d then
        let rawNum := 79 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 5).filter
        (admissibleNext [18, 16, 12, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_77 :
    searchIndexLists 13 133 240 20 [20, 16, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 3).flatMap (fun d =>
      if admissibleNext [20, 16, 12, 4] d then
        let rawNum := 133 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 3).filter
        (admissibleNext [20, 16, 12, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_78 :
    searchIndexLists 13 101 180 20 [20, 18, 12, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 3).flatMap (fun d =>
      if admissibleNext [20, 18, 12, 4] d then
        let rawNum := 101 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 12, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 3).filter
        (admissibleNext [20, 18, 12, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_79 :
    searchIndexLists 13 7 12 20 [20, 15, 10, 5] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 15, 10, 5] d then
        let rawNum := 7 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 15, 10, 5])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 15, 10, 5]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_80 :
    searchIndexLists 13 9 16 16 [16, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 7).flatMap (fun d =>
      if admissibleNext [16, 12, 8, 6] d then
        let rawNum := 9 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 7).filter
        (admissibleNext [16, 12, 8, 6]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_81 :
    searchIndexLists 13 41 72 18 [18, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 4).flatMap (fun d =>
      if admissibleNext [18, 12, 8, 6] d then
        let rawNum := 41 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 4).filter
        (admissibleNext [18, 12, 8, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_82 :
    searchIndexLists 13 23 40 20 [20, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 12, 8, 6] d then
        let rawNum := 23 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 12, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_83 :
    searchIndexLists 13 85 144 18 [18, 16, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 4).flatMap (fun d =>
      if admissibleNext [18, 16, 8, 6] d then
        let rawNum := 85 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 4).filter
        (admissibleNext [18, 16, 8, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_84 :
    searchIndexLists 13 143 240 20 [20, 16, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 16, 8, 6] d then
        let rawNum := 143 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 16, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_85 :
    searchIndexLists 13 217 360 20 [20, 18, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 18, 8, 6] d then
        let rawNum := 217 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 18, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_86 :
    searchIndexLists 13 103 180 15 [15, 12, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 7).flatMap (fun d =>
      if admissibleNext [15, 12, 9, 6] d then
        let rawNum := 103 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 7).filter
        (admissibleNext [15, 12, 9, 6]) =
        [18] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_87 :
    searchIndexLists 13 7 12 18 [18, 12, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 4).flatMap (fun d =>
      if admissibleNext [18, 12, 9, 6] d then
        let rawNum := 7 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 4).filter
        (admissibleNext [18, 12, 9, 6]) =
        [21] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_88 :
    searchIndexLists 13 149 252 21 [21, 12, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 0).flatMap (fun d =>
      if admissibleNext [21, 12, 9, 6] d then
        let rawNum := 149 * d - 252
        let rawDen := 252 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [21, 12, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 0).filter
        (admissibleNext [21, 12, 9, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_89 :
    searchIndexLists 13 3 5 18 [18, 15, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 3).flatMap (fun d =>
      if admissibleNext [18, 15, 9, 6] d then
        let rawNum := 3 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 3).filter
        (admissibleNext [18, 15, 9, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_90 :
    searchIndexLists 13 13 21 21 [21, 18, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 0).flatMap (fun d =>
      if admissibleNext [21, 18, 9, 6] d then
        let rawNum := 13 * d - 21
        let rawDen := 21 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [21, 18, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 0).filter
        (admissibleNext [21, 18, 9, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_91 :
    searchIndexLists 13 7 12 15 [15, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 16 7).flatMap (fun d =>
      if admissibleNext [15, 12, 10, 6] d then
        let rawNum := 7 * d - 12
        let rawDen := 12 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [15, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 16 7).filter
        (admissibleNext [15, 12, 10, 6]) =
        [18, 20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_92 :
    searchIndexLists 13 107 180 18 [18, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 3).flatMap (fun d =>
      if admissibleNext [18, 12, 10, 6] d then
        let rawNum := 107 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 3).filter
        (admissibleNext [18, 12, 10, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_93 :
    searchIndexLists 13 3 5 20 [20, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 12, 10, 6] d then
        let rawNum := 3 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 12, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_94 :
    searchIndexLists 13 11 18 18 [18, 15, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 3).flatMap (fun d =>
      if admissibleNext [18, 15, 10, 6] d then
        let rawNum := 11 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 3).filter
        (admissibleNext [18, 15, 10, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_95 :
    searchIndexLists 13 37 60 20 [20, 15, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 15, 10, 6] d then
        let rawNum := 37 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 15, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 15, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_96 :
    searchIndexLists 13 113 180 20 [20, 18, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 18, 10, 6] d then
        let rawNum := 113 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 18, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_97 :
    searchIndexLists 13 157 252 18 [18, 14, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 2).flatMap (fun d =>
      if admissibleNext [18, 14, 12, 6] d then
        let rawNum := 157 * d - 252
        let rawDen := 252 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 14, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 2).filter
        (admissibleNext [18, 14, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_98 :
    searchIndexLists 13 113 180 18 [18, 15, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 2).flatMap (fun d =>
      if admissibleNext [18, 15, 12, 6] d then
        let rawNum := 113 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 2).filter
        (admissibleNext [18, 15, 12, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_99 :
    searchIndexLists 13 19 30 20 [20, 15, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 15, 12, 6] d then
        let rawNum := 19 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 15, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 15, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_100 :
    searchIndexLists 13 91 144 18 [18, 16, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 2).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 6] d then
        let rawNum := 91 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 2).filter
        (admissibleNext [18, 16, 12, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_101 :
    searchIndexLists 13 51 80 20 [20, 16, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 16, 12, 6] d then
        let rawNum := 51 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 16, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_102 :
    searchIndexLists 13 29 45 20 [20, 18, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 18, 12, 6] d then
        let rawNum := 29 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 18, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_103 :
    searchIndexLists 13 151 240 16 [16, 12, 10, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 4).flatMap (fun d =>
      if admissibleNext [16, 12, 10, 8] d then
        let rawNum := 151 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 10, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 4).filter
        (admissibleNext [16, 12, 10, 8]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_104 :
    searchIndexLists 13 77 120 20 [20, 12, 10, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 12, 10, 8] d then
        let rawNum := 77 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [20, 12, 10, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 12, 10, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_105 :
    searchIndexLists 13 221 336 16 [16, 14, 12, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 17 3).flatMap (fun d =>
      if admissibleNext [16, 14, 12, 8] d then
        let rawNum := 221 * d - 336
        let rawDen := 336 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [16, 14, 12, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 3).filter
        (admissibleNext [16, 14, 12, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_106 :
    searchIndexLists 13 97 144 18 [18, 16, 12, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 8] d then
        let rawNum := 97 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 16, 12, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_107 :
    searchIndexLists 13 41 60 18 [18, 15, 12, 9] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 1).flatMap (fun d =>
      if admissibleNext [18, 15, 12, 9] d then
        let rawNum := 41 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 12, 9])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 1).filter
        (admissibleNext [18, 15, 12, 9]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD4_108 :
    searchIndexLists 13 25 36 18 [18, 15, 12, 10] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 0).flatMap (fun d =>
      if admissibleNext [18, 15, 12, 10] d then
        let rawNum := 25 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 12 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 12, 10])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 0).filter
        (admissibleNext [18, 15, 12, 10]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
