import ErdosProblems.E274.ArithmeticSearchCertificateD6

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_0 :
    searchIndexLists 12 1 4 18 [18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 30).flatMap (fun d =>
      if admissibleNext [18, 12, 9, 6, 3] d then
        let rawNum := 1 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 30).filter
        (admissibleNext [18, 12, 9, 6, 3]) =
        [24, 27, 36, 45, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_1 :
    searchIndexLists 12 19 72 24 [24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 21).flatMap (fun d =>
      if admissibleNext [24, 12, 9, 6, 3] d then
        let rawNum := 19 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 21).filter
        (admissibleNext [24, 12, 9, 6, 3]) =
        [27, 36, 45] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_2 :
    searchIndexLists 12 29 108 27 [27, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 17).flatMap (fun d =>
      if admissibleNext [27, 12, 9, 6, 3] d then
        let rawNum := 29 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 17).filter
        (admissibleNext [27, 12, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_3 :
    searchIndexLists 12 5 18 36 [36, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 7).flatMap (fun d =>
      if admissibleNext [36, 12, 9, 6, 3] d then
        let rawNum := 5 * d - 18
        let rawDen := 18 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 7).filter
        (admissibleNext [36, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_4 :
    searchIndexLists 12 7 24 24 [24, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 17).flatMap (fun d =>
      if admissibleNext [24, 18, 9, 6, 3] d then
        let rawNum := 7 * d - 24
        let rawDen := 24 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 17).filter
        (admissibleNext [24, 18, 9, 6, 3]) =
        [27, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_5 :
    searchIndexLists 12 8 27 27 [27, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 13).flatMap (fun d =>
      if admissibleNext [27, 18, 9, 6, 3] d then
        let rawNum := 8 * d - 27
        let rawDen := 27 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 13).filter
        (admissibleNext [27, 18, 9, 6, 3]) =
        [30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_6 :
    searchIndexLists 12 3 10 30 [30, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 10).flatMap (fun d =>
      if admissibleNext [30, 18, 9, 6, 3] d then
        let rawNum := 3 * d - 10
        let rawDen := 10 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 10).filter
        (admissibleNext [30, 18, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_7 :
    searchIndexLists 12 11 36 36 [36, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 3).flatMap (fun d =>
      if admissibleNext [36, 18, 9, 6, 3] d then
        let rawNum := 11 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 3).filter
        (admissibleNext [36, 18, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_8 :
    searchIndexLists 12 67 216 27 [27, 24, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 11).flatMap (fun d =>
      if admissibleNext [27, 24, 9, 6, 3] d then
        let rawNum := 67 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 11).filter
        (admissibleNext [27, 24, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_9 :
    searchIndexLists 12 23 72 36 [36, 24, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 24, 9, 6, 3] d then
        let rawNum := 23 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 24, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_10 :
    searchIndexLists 12 43 135 30 [30, 27, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 7).flatMap (fun d =>
      if admissibleNext [30, 27, 9, 6, 3] d then
        let rawNum := 43 * d - 135
        let rawDen := 135 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 7).filter
        (admissibleNext [30, 27, 9, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_11 :
    searchIndexLists 12 35 108 36 [36, 27, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 27, 9, 6, 3] d then
        let rawNum := 35 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 27, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_12 :
    searchIndexLists 12 59 180 36 [36, 30, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 30, 9, 6, 3] d then
        let rawNum := 59 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 30, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_13 :
    searchIndexLists 12 37 120 24 [24, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 14).flatMap (fun d =>
      if admissibleNext [24, 15, 12, 6, 3] d then
        let rawNum := 37 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 14).filter
        (admissibleNext [24, 15, 12, 6, 3]) =
        [30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_14 :
    searchIndexLists 12 19 60 30 [30, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 7).flatMap (fun d =>
      if admissibleNext [30, 15, 12, 6, 3] d then
        let rawNum := 19 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 7).filter
        (admissibleNext [30, 15, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_15 :
    searchIndexLists 12 29 90 36 [36, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 15, 12, 6, 3] d then
        let rawNum := 29 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 15, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_16 :
    searchIndexLists 12 23 72 24 [24, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 13).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 6, 3] d then
        let rawNum := 23 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 13).filter
        (admissibleNext [24, 18, 12, 6, 3]) =
        [27, 30, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_17 :
    searchIndexLists 12 35 108 27 [27, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 10).flatMap (fun d =>
      if admissibleNext [27, 18, 12, 6, 3] d then
        let rawNum := 35 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 10).filter
        (admissibleNext [27, 18, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_18 :
    searchIndexLists 12 59 180 30 [30, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 6).flatMap (fun d =>
      if admissibleNext [30, 18, 12, 6, 3] d then
        let rawNum := 59 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 6).filter
        (admissibleNext [30, 18, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_19 :
    searchIndexLists 12 1 3 36 [36, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 18, 12, 6, 3] d then
        let rawNum := 1 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [36, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 18, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_20 :
    searchIndexLists 12 55 168 24 [24, 21, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 12).flatMap (fun d =>
      if admissibleNext [24, 21, 12, 6, 3] d then
        let rawNum := 55 * d - 168
        let rawDen := 168 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 21, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 12).filter
        (admissibleNext [24, 21, 12, 6, 3]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_21 :
    searchIndexLists 12 73 216 27 [27, 24, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 8).flatMap (fun d =>
      if admissibleNext [27, 24, 12, 6, 3] d then
        let rawNum := 73 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 8).filter
        (admissibleNext [27, 24, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_22 :
    searchIndexLists 12 41 120 30 [30, 24, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 5).flatMap (fun d =>
      if admissibleNext [30, 24, 12, 6, 3] d then
        let rawNum := 41 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 5).filter
        (admissibleNext [30, 24, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_23 :
    searchIndexLists 12 91 264 33 [33, 24, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 34 1).flatMap (fun d =>
      if admissibleNext [33, 24, 12, 6, 3] d then
        let rawNum := 91 * d - 264
        let rawDen := 264 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [33, 24, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 34 1).filter
        (admissibleNext [33, 24, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_24 :
    searchIndexLists 12 31 90 30 [30, 18, 15, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 4).flatMap (fun d =>
      if admissibleNext [30, 18, 15, 6, 3] d then
        let rawNum := 31 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 15, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 4).filter
        (admissibleNext [30, 18, 15, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_25 :
    searchIndexLists 12 43 120 30 [30, 24, 15, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 3).flatMap (fun d =>
      if admissibleNext [30, 24, 15, 6, 3] d then
        let rawNum := 43 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 15, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 3).filter
        (admissibleNext [30, 24, 15, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_26 :
    searchIndexLists 12 79 216 27 [27, 24, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 5).flatMap (fun d =>
      if admissibleNext [27, 24, 18, 6, 3] d then
        let rawNum := 79 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 5).filter
        (admissibleNext [27, 24, 18, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_27 :
    searchIndexLists 12 133 360 30 [30, 24, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 6, 3] d then
        let rawNum := 133 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 24, 18, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_28 :
    searchIndexLists 12 101 270 30 [30, 27, 18, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 27, 18, 6, 3] d then
        let rawNum := 101 * d - 270
        let rawDen := 270 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 18, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 27, 18, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_29 :
    searchIndexLists 12 3 8 24 [24, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 8).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 9, 3] d then
        let rawNum := 3 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 8).filter
        (admissibleNext [24, 18, 12, 9, 3]) =
        [27, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_30 :
    searchIndexLists 12 41 108 27 [27, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 4).flatMap (fun d =>
      if admissibleNext [27, 18, 12, 9, 3] d then
        let rawNum := 41 * d - 108
        let rawDen := 108 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 4).filter
        (admissibleNext [27, 18, 12, 9, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_31 :
    searchIndexLists 12 23 60 30 [30, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 18, 12, 9, 3] d then
        let rawNum := 23 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 18, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_32 :
    searchIndexLists 12 85 216 27 [27, 24, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 3).flatMap (fun d =>
      if admissibleNext [27, 24, 12, 9, 3] d then
        let rawNum := 85 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 3).filter
        (admissibleNext [27, 24, 12, 9, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_33 :
    searchIndexLists 12 143 360 30 [30, 24, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 24, 12, 9, 3] d then
        let rawNum := 143 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 24, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_34 :
    searchIndexLists 12 107 270 27 [27, 18, 15, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 3).flatMap (fun d =>
      if admissibleNext [27, 18, 15, 9, 3] d then
        let rawNum := 107 * d - 270
        let rawDen := 270 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 18, 15, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 3).filter
        (admissibleNext [27, 18, 15, 9, 3]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_35 :
    searchIndexLists 12 2 5 30 [30, 18, 15, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 0).flatMap (fun d =>
      if admissibleNext [30, 18, 15, 9, 3] d then
        let rawNum := 2 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 15, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 0).filter
        (admissibleNext [30, 18, 15, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_36 :
    searchIndexLists 12 157 378 27 [27, 21, 18, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 1).flatMap (fun d =>
      if admissibleNext [27, 21, 18, 9, 3] d then
        let rawNum := 157 * d - 378
        let rawDen := 378 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 21, 18, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 1).filter
        (admissibleNext [27, 21, 18, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_37 :
    searchIndexLists 12 91 216 27 [27, 24, 18, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 1).flatMap (fun d =>
      if admissibleNext [27, 24, 18, 9, 3] d then
        let rawNum := 91 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 18, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 1).filter
        (admissibleNext [27, 24, 18, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_38 :
    searchIndexLists 12 151 360 24 [24, 18, 15, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 18, 15, 12, 3] d then
        let rawNum := 151 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 15, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 18, 15, 12, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_39 :
    searchIndexLists 12 221 504 24 [24, 21, 18, 12, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 21, 18, 12, 3] d then
        let rawNum := 221 * d - 504
        let rawDen := 504 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 21, 18, 12, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 21, 18, 12, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_40 :
    searchIndexLists 12 5 16 16 [16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 17 22).flatMap (fun d =>
      if admissibleNext [16, 12, 8, 6, 4] d then
        let rawNum := 5 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 17 22).filter
        (admissibleNext [16, 12, 8, 6, 4]) =
        [18, 24, 30, 32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_41 :
    searchIndexLists 12 23 72 18 [18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 19).flatMap (fun d =>
      if admissibleNext [18, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 19).filter
        (admissibleNext [18, 12, 8, 6, 4]) =
        [24, 30, 32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_42 :
    searchIndexLists 12 1 3 24 [24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 12).flatMap (fun d =>
      if admissibleNext [24, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 3
        let rawDen := 3 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 12).filter
        (admissibleNext [24, 12, 8, 6, 4]) =
        [30, 32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_43 :
    searchIndexLists 12 41 120 30 [30, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 5).flatMap (fun d =>
      if admissibleNext [30, 12, 8, 6, 4] d then
        let rawNum := 41 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 5).filter
        (admissibleNext [30, 12, 8, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_44 :
    searchIndexLists 12 11 32 32 [32, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 2).flatMap (fun d =>
      if admissibleNext [32, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 32
        let rawDen := 32 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [32, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 2).filter
        (admissibleNext [32, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_45 :
    searchIndexLists 12 49 144 18 [18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 17).flatMap (fun d =>
      if admissibleNext [18, 16, 8, 6, 4] d then
        let rawNum := 49 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 17).filter
        (admissibleNext [18, 16, 8, 6, 4]) =
        [24, 30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_46 :
    searchIndexLists 12 17 48 24 [24, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 9).flatMap (fun d =>
      if admissibleNext [24, 16, 8, 6, 4] d then
        let rawNum := 17 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 9).filter
        (admissibleNext [24, 16, 8, 6, 4]) =
        [30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_47 :
    searchIndexLists 12 29 80 30 [30, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 3).flatMap (fun d =>
      if admissibleNext [30, 16, 8, 6, 4] d then
        let rawNum := 29 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 3).filter
        (admissibleNext [30, 16, 8, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_48 :
    searchIndexLists 12 35 96 32 [32, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 0).flatMap (fun d =>
      if admissibleNext [32, 16, 8, 6, 4] d then
        let rawNum := 35 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [32, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 0).filter
        (admissibleNext [32, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_49 :
    searchIndexLists 12 13 36 24 [24, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 9).flatMap (fun d =>
      if admissibleNext [24, 18, 8, 6, 4] d then
        let rawNum := 13 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 9).filter
        (admissibleNext [24, 18, 8, 6, 4]) =
        [30, 32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_50 :
    searchIndexLists 12 133 360 30 [30, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 18, 8, 6, 4] d then
        let rawNum := 133 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 18, 8, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_51 :
    searchIndexLists 12 107 288 32 [32, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 0).flatMap (fun d =>
      if admissibleNext [32, 18, 8, 6, 4] d then
        let rawNum := 107 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [32, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 0).filter
        (admissibleNext [32, 18, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_52 :
    searchIndexLists 12 23 60 30 [30, 24, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 24, 8, 6, 4] d then
        let rawNum := 23 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 24, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_53 :
    searchIndexLists 12 55 144 18 [18, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 13).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 6, 4] d then
        let rawNum := 55 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 13).filter
        (admissibleNext [18, 16, 12, 6, 4]) =
        [24, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_54 :
    searchIndexLists 12 19 48 24 [24, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 6).flatMap (fun d =>
      if admissibleNext [24, 16, 12, 6, 4] d then
        let rawNum := 19 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 6).filter
        (admissibleNext [24, 16, 12, 6, 4]) =
        [30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_55 :
    searchIndexLists 12 71 180 20 [20, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 10).flatMap (fun d =>
      if admissibleNext [20, 18, 12, 6, 4] d then
        let rawNum := 71 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 10).filter
        (admissibleNext [20, 18, 12, 6, 4]) =
        [24, 30] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_56 :
    searchIndexLists 12 29 72 24 [24, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 5).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 6, 4] d then
        let rawNum := 29 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 5).filter
        (admissibleNext [24, 18, 12, 6, 4]) =
        [28] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_57 :
    searchIndexLists 12 103 252 28 [28, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 29 1).flatMap (fun d =>
      if admissibleNext [28, 18, 12, 6, 4] d then
        let rawNum := 103 * d - 252
        let rawDen := 252 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [28, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 29 1).filter
        (admissibleNext [28, 18, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_58 :
    searchIndexLists 12 49 120 24 [24, 20, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 5).flatMap (fun d =>
      if admissibleNext [24, 20, 12, 6, 4] d then
        let rawNum := 49 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 5).filter
        (admissibleNext [24, 20, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_59 :
    searchIndexLists 12 71 168 28 [28, 24, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 29 0).flatMap (fun d =>
      if admissibleNext [28, 24, 12, 6, 4] d then
        let rawNum := 71 * d - 168
        let rawDen := 168 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [28, 24, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 29 0).filter
        (admissibleNext [28, 24, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_60 :
    searchIndexLists 12 61 144 24 [24, 18, 16, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 18, 16, 6, 4] d then
        let rawNum := 61 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 16, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 18, 16, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_61 :
    searchIndexLists 12 157 360 24 [24, 20, 18, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 20, 18, 6, 4] d then
        let rawNum := 157 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 18, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 20, 18, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_62 :
    searchIndexLists 12 33 80 20 [20, 16, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 9).flatMap (fun d =>
      if admissibleNext [20, 16, 10, 8, 4] d then
        let rawNum := 33 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 9).filter
        (admissibleNext [20, 16, 10, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_63 :
    searchIndexLists 12 101 240 24 [24, 16, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 4).flatMap (fun d =>
      if admissibleNext [24, 16, 10, 8, 4] d then
        let rawNum := 101 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 4).filter
        (admissibleNext [24, 16, 10, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_64 :
    searchIndexLists 12 13 30 24 [24, 20, 10, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 20, 10, 8, 4] d then
        let rawNum := 13 * d - 30
        let rawDen := 30 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 10, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 20, 10, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_65 :
    searchIndexLists 12 61 144 18 [18, 16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 10).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 8, 4] d then
        let rawNum := 61 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 10).filter
        (admissibleNext [18, 16, 12, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_66 :
    searchIndexLists 12 103 240 20 [20, 16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 7).flatMap (fun d =>
      if admissibleNext [20, 16, 12, 8, 4] d then
        let rawNum := 103 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 7).filter
        (admissibleNext [20, 16, 12, 8, 4]) =
        [24] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_67 :
    searchIndexLists 12 7 16 24 [24, 16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 16, 12, 8, 4] d then
        let rawNum := 7 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 16, 12, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_68 :
    searchIndexLists 12 4 9 24 [24, 18, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 3).flatMap (fun d =>
      if admissibleNext [24, 18, 12, 8, 4] d then
        let rawNum := 4 * d - 9
        let rawDen := 9 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 3).filter
        (admissibleNext [24, 18, 12, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_69 :
    searchIndexLists 12 9 20 24 [24, 20, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 20, 12, 8, 4] d then
        let rawNum := 9 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 20, 12, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_70 :
    searchIndexLists 12 151 336 24 [24, 16, 14, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 2).flatMap (fun d =>
      if admissibleNext [24, 16, 14, 8, 4] d then
        let rawNum := 151 * d - 336
        let rawDen := 336 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 16, 14, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 2).filter
        (admissibleNext [24, 16, 14, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_71 :
    searchIndexLists 12 67 144 24 [24, 18, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 18, 16, 8, 4] d then
        let rawNum := 67 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 18, 16, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_72 :
    searchIndexLists 12 113 240 24 [24, 20, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 20, 16, 8, 4] d then
        let rawNum := 113 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 20, 16, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_73 :
    searchIndexLists 12 251 528 24 [24, 22, 16, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 22, 16, 8, 4] d then
        let rawNum := 251 * d - 528
        let rawDen := 528 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 22, 16, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 22, 16, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_74 :
    searchIndexLists 12 19 40 24 [24, 20, 12, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 1).flatMap (fun d =>
      if admissibleNext [24, 20, 12, 10, 4] d then
        let rawNum := 19 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 12, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 1).filter
        (admissibleNext [24, 20, 12, 10, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_75 :
    searchIndexLists 12 119 240 24 [24, 20, 16, 10, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 20, 16, 10, 4] d then
        let rawNum := 119 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 16, 10, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 20, 16, 10, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_76 :
    searchIndexLists 12 73 144 18 [18, 16, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 5).flatMap (fun d =>
      if admissibleNext [18, 16, 12, 8, 6] d then
        let rawNum := 73 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 16, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 5).filter
        (admissibleNext [18, 16, 12, 8, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_77 :
    searchIndexLists 12 41 80 20 [20, 16, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 3).flatMap (fun d =>
      if admissibleNext [20, 16, 12, 8, 6] d then
        let rawNum := 41 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 3).filter
        (admissibleNext [20, 16, 12, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_78 :
    searchIndexLists 12 187 360 20 [20, 18, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 3).flatMap (fun d =>
      if admissibleNext [20, 18, 12, 8, 6] d then
        let rawNum := 187 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 3).filter
        (admissibleNext [20, 18, 12, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_79 :
    searchIndexLists 12 389 720 20 [20, 18, 16, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 18, 16, 8, 6] d then
        let rawNum := 389 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 16, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 18, 16, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_80 :
    searchIndexLists 12 31 60 18 [18, 15, 12, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 5).flatMap (fun d =>
      if admissibleNext [18, 15, 12, 9, 6] d then
        let rawNum := 31 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 12, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 5).filter
        (admissibleNext [18, 15, 12, 9, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_81 :
    searchIndexLists 12 15 28 21 [21, 18, 12, 9, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 22 1).flatMap (fun d =>
      if admissibleNext [21, 18, 12, 9, 6] d then
        let rawNum := 15 * d - 28
        let rawDen := 28 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [21, 18, 12, 9, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 22 1).filter
        (admissibleNext [21, 18, 12, 9, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_82 :
    searchIndexLists 12 19 36 18 [18, 15, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 19 4).flatMap (fun d =>
      if admissibleNext [18, 15, 12, 10, 6] d then
        let rawNum := 19 * d - 36
        let rawDen := 36 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [18, 15, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 19 4).filter
        (admissibleNext [18, 15, 12, 10, 6]) =
        [20] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_83 :
    searchIndexLists 12 8 15 20 [20, 15, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 15, 12, 10, 6] d then
        let rawNum := 8 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 15, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 15, 12, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_84 :
    searchIndexLists 12 49 90 20 [20, 18, 12, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 2).flatMap (fun d =>
      if admissibleNext [20, 18, 12, 10, 6] d then
        let rawNum := 49 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 12, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 2).filter
        (admissibleNext [20, 18, 12, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_85 :
    searchIndexLists 12 101 180 20 [20, 18, 15, 10, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 1).flatMap (fun d =>
      if admissibleNext [20, 18, 15, 10, 6] d then
        let rawNum := 101 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 15, 10, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 1).filter
        (admissibleNext [20, 18, 15, 10, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_86 :
    searchIndexLists 12 26 45 20 [20, 18, 15, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 18, 15, 12, 6] d then
        let rawNum := 26 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 15, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 18, 15, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_87 :
    searchIndexLists 12 419 720 20 [20, 18, 16, 12, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 18, 16, 12, 6] d then
        let rawNum := 419 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 18, 16, 12, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 18, 16, 12, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD5_88 :
    searchIndexLists 12 139 240 20 [20, 16, 12, 10, 8] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 21 0).flatMap (fun d =>
      if admissibleNext [20, 16, 12, 10, 8] d then
        let rawNum := 139 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 11 (rawNum / common) (rawDen / common) d
          (d :: [20, 16, 12, 10, 8])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 21 0).filter
        (admissibleNext [20, 16, 12, 10, 8]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
