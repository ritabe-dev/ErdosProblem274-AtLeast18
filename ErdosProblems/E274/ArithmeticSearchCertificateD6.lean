import ErdosProblems.E274.ArithmeticSearchCertificateD7

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_0 :
    searchIndexLists 11 5 24 24 [24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 28).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 9, 6, 3] d then
        let rawNum := 5 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 28).filter
        (admissibleNext [24, 18, 12, 9, 6, 3]) =
        [27, 36, 45, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_1 :
    searchIndexLists 11 23 108 27 [27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 24).flatMap (fun d =>
      if admissibleNext [27, 18, 12, 9, 6, 3] d then
        let rawNum := 23 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 24).filter
        (admissibleNext [27, 18, 12, 9, 6, 3]) =
        [36, 45, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_2 :
    searchIndexLists 11 2 9 36 [36, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 13).flatMap (fun d =>
      if admissibleNext [36, 18, 12, 9, 6, 3] d then
        let rawNum := 2 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 13).filter
        (admissibleNext [36, 18, 12, 9, 6, 3]) =
        [45, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_3 :
    searchIndexLists 11 41 180 45 [45, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 3).flatMap (fun d =>
      if admissibleNext [45, 18, 12, 9, 6, 3] d then
        let rawNum := 41 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [45, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 3).filter
        (admissibleNext [45, 18, 12, 9, 6, 3]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_4 :
    searchIndexLists 11 11 48 48 [48, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 18, 12, 9, 6, 3] d then
        let rawNum := 11 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [48, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_5 :
    searchIndexLists 11 49 216 27 [27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 21).flatMap (fun d =>
      if admissibleNext [27, 24, 12, 9, 6, 3] d then
        let rawNum := 49 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 21).filter
        (admissibleNext [27, 24, 12, 9, 6, 3]) =
        [36, 45, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_6 :
    searchIndexLists 11 17 72 36 [36, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 10).flatMap (fun d =>
      if admissibleNext [36, 24, 12, 9, 6, 3] d then
        let rawNum := 17 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 10).filter
        (admissibleNext [36, 24, 12, 9, 6, 3]) =
        [45] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_7 :
    searchIndexLists 11 29 120 45 [45, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 0).flatMap (fun d =>
      if admissibleNext [45, 24, 12, 9, 6, 3] d then
        let rawNum := 29 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [45, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 0).filter
        (admissibleNext [45, 24, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_8 :
    searchIndexLists 11 13 54 36 [36, 27, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 9).flatMap (fun d =>
      if admissibleNext [36, 27, 12, 9, 6, 3] d then
        let rawNum := 13 * d - 54
        let rawDen := 54 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 9).filter
        (admissibleNext [36, 27, 12, 9, 6, 3]) =
        [45] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_9 :
    searchIndexLists 11 55 216 27 [27, 24, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 16).flatMap (fun d =>
      if admissibleNext [27, 24, 18, 9, 6, 3] d then
        let rawNum := 55 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 16).filter
        (admissibleNext [27, 24, 18, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_10 :
    searchIndexLists 11 19 72 36 [36, 24, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 5).flatMap (fun d =>
      if admissibleNext [36, 24, 18, 9, 6, 3] d then
        let rawNum := 19 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 5).filter
        (admissibleNext [36, 24, 18, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_11 :
    searchIndexLists 11 71 270 30 [30, 27, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 11).flatMap (fun d =>
      if admissibleNext [30, 27, 18, 9, 6, 3] d then
        let rawNum := 71 * d - 270
        let rawDen := 270 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 11).filter
        (admissibleNext [30, 27, 18, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_12 :
    searchIndexLists 11 29 108 36 [36, 27, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 4).flatMap (fun d =>
      if admissibleNext [36, 27, 18, 9, 6, 3] d then
        let rawNum := 29 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 4).filter
        (admissibleNext [36, 27, 18, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_13 :
    searchIndexLists 11 49 180 36 [36, 30, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 4).flatMap (fun d =>
      if admissibleNext [36, 30, 18, 9, 6, 3] d then
        let rawNum := 49 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 4).filter
        (admissibleNext [36, 30, 18, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_14 :
    searchIndexLists 11 61 216 36 [36, 27, 24, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 27, 24, 9, 6, 3] d then
        let rawNum := 61 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 24, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 27, 24, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_15 :
    searchIndexLists 11 157 540 36 [36, 30, 27, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 30, 27, 9, 6, 3] d then
        let rawNum := 157 * d - 540
        let rawDen := 540 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 27, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 30, 27, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_16 :
    searchIndexLists 11 11 40 30 [30, 24, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 10).flatMap (fun d =>
      if admissibleNext [30, 24, 15, 12, 6, 3] d then
        let rawNum := 11 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 10).filter
        (admissibleNext [30, 24, 15, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_17 :
    searchIndexLists 11 101 360 36 [36, 24, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 3).flatMap (fun d =>
      if admissibleNext [36, 24, 15, 12, 6, 3] d then
        let rawNum := 101 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 3).filter
        (admissibleNext [36, 24, 15, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_18 :
    searchIndexLists 11 13 45 36 [36, 30, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 30, 15, 12, 6, 3] d then
        let rawNum := 13 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 30, 15, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_19 :
    searchIndexLists 11 61 216 27 [27, 24, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 11).flatMap (fun d =>
      if admissibleNext [27, 24, 18, 12, 6, 3] d then
        let rawNum := 61 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 11).filter
        (admissibleNext [27, 24, 18, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_20 :
    searchIndexLists 11 103 360 30 [30, 24, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 8).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 12, 6, 3] d then
        let rawNum := 103 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 8).filter
        (admissibleNext [30, 24, 18, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_21 :
    searchIndexLists 11 7 24 36 [36, 24, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 24, 18, 12, 6, 3] d then
        let rawNum := 7 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 24, 18, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_22 :
    searchIndexLists 11 8 27 36 [36, 27, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 27, 18, 12, 6, 3] d then
        let rawNum := 8 * d - 27
        let rawDen := 27 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 27, 18, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_23 :
    searchIndexLists 11 3 10 36 [36, 30, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 30, 18, 12, 6, 3] d then
        let rawNum := 3 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 30, 18, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_24 :
    searchIndexLists 11 151 504 36 [36, 24, 21, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 24, 21, 12, 6, 3] d then
        let rawNum := 151 * d - 504
        let rawDen := 504 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 21, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 24, 21, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_25 :
    searchIndexLists 11 73 216 27 [27, 24, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 5).flatMap (fun d =>
      if admissibleNext [27, 24, 18, 12, 9, 3] d then
        let rawNum := 73 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 5).filter
        (admissibleNext [27, 24, 18, 12, 9, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_26 :
    searchIndexLists 11 41 120 30 [30, 24, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 12, 9, 3] d then
        let rawNum := 41 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 24, 18, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_27 :
    searchIndexLists 11 187 540 30 [30, 27, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 27, 18, 12, 9, 3] d then
        let rawNum := 187 * d - 540
        let rawDen := 540 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 27, 18, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_28 :
    searchIndexLists 11 389 1080 30 [30, 27, 24, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 27, 24, 12, 9, 3] d then
        let rawNum := 389 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 24, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 27, 24, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_29 :
    searchIndexLists 11 49 135 30 [30, 27, 18, 15, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 27, 18, 15, 9, 3] d then
        let rawNum := 49 * d - 135
        let rawDen := 135 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 18, 15, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 27, 18, 15, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_30 :
    searchIndexLists 11 37 144 18 [18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 19 24).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 24).filter
        (admissibleNext [18, 16, 12, 8, 6, 4]) =
        [24, 30, 32, 36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_31 :
    searchIndexLists 11 13 48 24 [24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 16).flatMap (fun d =>
      if admissibleNext [24, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 16).filter
        (admissibleNext [24, 16, 12, 8, 6, 4]) =
        [30, 32, 36, 40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_32 :
    searchIndexLists 11 67 240 30 [30, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 9).flatMap (fun d =>
      if admissibleNext [30, 16, 12, 8, 6, 4] d then
        let rawNum := 67 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 9).filter
        (admissibleNext [30, 16, 12, 8, 6, 4]) =
        [32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_33 :
    searchIndexLists 11 9 32 32 [32, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 7).flatMap (fun d =>
      if admissibleNext [32, 16, 12, 8, 6, 4] d then
        let rawNum := 9 * d - 32
        let rawDen := 32 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 7).filter
        (admissibleNext [32, 16, 12, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_34 :
    searchIndexLists 11 41 144 36 [36, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 16, 12, 8, 6, 4] d then
        let rawNum := 41 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_35 :
    searchIndexLists 11 5 18 24 [24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 15).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 8, 6, 4] d then
        let rawNum := 5 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 15).filter
        (admissibleNext [24, 18, 12, 8, 6, 4]) =
        [30, 32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_36 :
    searchIndexLists 11 103 360 30 [30, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 8).flatMap (fun d =>
      if admissibleNext [30, 18, 12, 8, 6, 4] d then
        let rawNum := 103 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 8).filter
        (admissibleNext [30, 18, 12, 8, 6, 4]) =
        [32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_37 :
    searchIndexLists 11 83 288 32 [32, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 6).flatMap (fun d =>
      if admissibleNext [32, 18, 12, 8, 6, 4] d then
        let rawNum := 83 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 6).filter
        (admissibleNext [32, 18, 12, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_38 :
    searchIndexLists 11 7 24 36 [36, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 18, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_39 :
    searchIndexLists 11 3 10 30 [30, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 6).flatMap (fun d =>
      if admissibleNext [30, 24, 12, 8, 6, 4] d then
        let rawNum := 3 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 6).filter
        (admissibleNext [30, 24, 12, 8, 6, 4]) =
        [32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_40 :
    searchIndexLists 11 29 96 32 [32, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 4).flatMap (fun d =>
      if admissibleNext [32, 24, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 4).filter
        (admissibleNext [32, 24, 12, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_41 :
    searchIndexLists 11 11 36 36 [36, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 24, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 24, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_42 :
    searchIndexLists 11 149 480 32 [32, 30, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 3).flatMap (fun d =>
      if admissibleNext [32, 30, 12, 8, 6, 4] d then
        let rawNum := 149 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 3).filter
        (admissibleNext [32, 30, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_43 :
    searchIndexLists 11 43 144 24 [24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 12).flatMap (fun d =>
      if admissibleNext [24, 18, 16, 8, 6, 4] d then
        let rawNum := 43 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 12).filter
        (admissibleNext [24, 18, 16, 8, 6, 4]) =
        [30, 32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_44 :
    searchIndexLists 11 221 720 30 [30, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 5).flatMap (fun d =>
      if admissibleNext [30, 18, 16, 8, 6, 4] d then
        let rawNum := 221 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 5).filter
        (admissibleNext [30, 18, 16, 8, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_45 :
    searchIndexLists 11 89 288 32 [32, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 3).flatMap (fun d =>
      if admissibleNext [32, 18, 16, 8, 6, 4] d then
        let rawNum := 89 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 3).filter
        (admissibleNext [32, 18, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_46 :
    searchIndexLists 11 77 240 30 [30, 24, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 4).flatMap (fun d =>
      if admissibleNext [30, 24, 16, 8, 6, 4] d then
        let rawNum := 77 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 4).filter
        (admissibleNext [30, 24, 16, 8, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_47 :
    searchIndexLists 11 31 96 32 [32, 24, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 2).flatMap (fun d =>
      if admissibleNext [32, 24, 16, 8, 6, 4] d then
        let rawNum := 31 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 2).filter
        (admissibleNext [32, 24, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_48 :
    searchIndexLists 11 53 160 32 [32, 30, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 1).flatMap (fun d =>
      if admissibleNext [32, 30, 16, 8, 6, 4] d then
        let rawNum := 53 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 1).filter
        (admissibleNext [32, 30, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_49 :
    searchIndexLists 11 59 180 30 [30, 24, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 3).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 8, 6, 4] d then
        let rawNum := 59 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 3).filter
        (admissibleNext [30, 24, 18, 8, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_50 :
    searchIndexLists 11 95 288 32 [32, 24, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 1).flatMap (fun d =>
      if admissibleNext [32, 24, 18, 8, 6, 4] d then
        let rawNum := 95 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 1).filter
        (admissibleNext [32, 24, 18, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_51 :
    searchIndexLists 11 487 1440 32 [32, 30, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 0).flatMap (fun d =>
      if admissibleNext [32, 30, 18, 8, 6, 4] d then
        let rawNum := 487 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 0).filter
        (admissibleNext [32, 30, 18, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_52 :
    searchIndexLists 11 49 144 24 [24, 18, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 8).flatMap (fun d =>
      if admissibleNext [24, 18, 16, 12, 6, 4] d then
        let rawNum := 49 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 8).filter
        (admissibleNext [24, 18, 16, 12, 6, 4]) =
        [30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_53 :
    searchIndexLists 11 251 720 30 [30, 18, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 18, 16, 12, 6, 4] d then
        let rawNum := 251 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 18, 16, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_54 :
    searchIndexLists 11 29 80 30 [30, 24, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 24, 16, 12, 6, 4] d then
        let rawNum := 29 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 24, 16, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_55 :
    searchIndexLists 11 127 360 24 [24, 20, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 7).flatMap (fun d =>
      if admissibleNext [24, 20, 18, 12, 6, 4] d then
        let rawNum := 127 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 7).filter
        (admissibleNext [24, 20, 18, 12, 6, 4]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_56 :
    searchIndexLists 11 13 36 30 [30, 20, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 20, 18, 12, 6, 4] d then
        let rawNum := 13 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [30, 20, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 20, 18, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_57 :
    searchIndexLists 11 185 504 28 [28, 24, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 29 1).flatMap (fun d =>
      if admissibleNext [28, 24, 18, 12, 6, 4] d then
        let rawNum := 185 * d - 504
        let rawDen := 504 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [28, 24, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 29 1).filter
        (admissibleNext [28, 24, 18, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_58 :
    searchIndexLists 11 89 240 24 [24, 20, 16, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 5).flatMap (fun d =>
      if admissibleNext [24, 20, 16, 10, 8, 4] d then
        let rawNum := 89 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 16, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 5).filter
        (admissibleNext [24, 20, 16, 10, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_59 :
    searchIndexLists 11 55 144 24 [24, 18, 16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 18, 16, 12, 8, 4] d then
        let rawNum := 55 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 18, 16, 12, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_60 :
    searchIndexLists 11 31 80 24 [24, 20, 16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 20, 16, 12, 8, 4] d then
        let rawNum := 31 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 20, 16, 12, 8, 4]) =
        [28] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_61 :
    searchIndexLists 11 329 720 20 [20, 18, 16, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 4).flatMap (fun d =>
      if admissibleNext [20, 18, 16, 12, 8, 6] d then
        let rawNum := 329 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 16, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 4).filter
        (admissibleNext [20, 18, 16, 12, 8, 6]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD6_62 :
    searchIndexLists 11 43 90 20 [20, 18, 15, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 3).flatMap (fun d =>
      if admissibleNext [20, 18, 15, 12, 10, 6] d then
        let rawNum := 43 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 10 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 15, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 3).filter
        (admissibleNext [20, 18, 15, 12, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
