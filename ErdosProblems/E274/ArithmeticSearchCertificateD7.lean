import ErdosProblems.E274.ArithmeticSearchCertificateD8

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_0 :
    searchIndexLists 10 37 216 27 [27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 28 31).flatMap (fun d =>
      if admissibleNext [27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 37 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 28 31).filter
        (admissibleNext [27, 24, 18, 12, 9, 6, 3]) =
        [36, 45, 48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_1 :
    searchIndexLists 10 13 72 36 [36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 19).flatMap (fun d =>
      if admissibleNext [36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 13 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 19).filter
        (admissibleNext [36, 24, 18, 12, 9, 6, 3]) =
        [45, 48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_2 :
    searchIndexLists 10 67 360 45 [45, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 8).flatMap (fun d =>
      if admissibleNext [45, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 67 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [45, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 8).filter
        (admissibleNext [45, 24, 18, 12, 9, 6, 3]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_3 :
    searchIndexLists 10 3 16 48 [48, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 5).flatMap (fun d =>
      if admissibleNext [48, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 3 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [48, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 5).filter
        (admissibleNext [48, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_4 :
    searchIndexLists 10 5 27 36 [36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 18).flatMap (fun d =>
      if admissibleNext [36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 5 * d - 27
        let rawDen := 27 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 18).filter
        (admissibleNext [36, 27, 18, 12, 9, 6, 3]) =
        [45, 48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_5 :
    searchIndexLists 10 103 540 45 [45, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 7).flatMap (fun d =>
      if admissibleNext [45, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 103 * d - 540
        let rawDen := 540 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [45, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 7).filter
        (admissibleNext [45, 27, 18, 12, 9, 6, 3]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_6 :
    searchIndexLists 10 83 432 48 [48, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 4).flatMap (fun d =>
      if admissibleNext [48, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 83 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [48, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 4).filter
        (admissibleNext [48, 27, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_7 :
    searchIndexLists 10 1 5 45 [45, 36, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 5).flatMap (fun d =>
      if admissibleNext [45, 36, 18, 12, 9, 6, 3] d then
        let rawNum := 1 * d - 5
        let rawDen := 5 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 5).filter
        (admissibleNext [45, 36, 18, 12, 9, 6, 3]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_8 :
    searchIndexLists 10 29 144 48 [48, 36, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 1).flatMap (fun d =>
      if admissibleNext [48, 36, 18, 12, 9, 6, 3] d then
        let rawNum := 29 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 1).filter
        (admissibleNext [48, 36, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_9 :
    searchIndexLists 10 149 720 48 [48, 45, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 45, 18, 12, 9, 6, 3] d then
        let rawNum := 149 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 45, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_10 :
    searchIndexLists 10 43 216 36 [36, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 14).flatMap (fun d =>
      if admissibleNext [36, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 43 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 14).filter
        (admissibleNext [36, 27, 24, 12, 9, 6, 3]) =
        [45, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_11 :
    searchIndexLists 10 221 1080 45 [45, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 3).flatMap (fun d =>
      if admissibleNext [45, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 221 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [45, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 3).filter
        (admissibleNext [45, 27, 24, 12, 9, 6, 3]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_12 :
    searchIndexLists 10 89 432 48 [48, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 89 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [48, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 27, 24, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_13 :
    searchIndexLists 10 77 360 45 [45, 36, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 1).flatMap (fun d =>
      if admissibleNext [45, 36, 24, 12, 9, 6, 3] d then
        let rawNum := 77 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 1).filter
        (admissibleNext [45, 36, 24, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_14 :
    searchIndexLists 10 59 270 45 [45, 36, 27, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 0).flatMap (fun d =>
      if admissibleNext [45, 36, 27, 12, 9, 6, 3] d then
        let rawNum := 59 * d - 270
        let rawDen := 270 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 27, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 0).filter
        (admissibleNext [45, 36, 27, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_15 :
    searchIndexLists 10 49 216 36 [36, 27, 24, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 8).flatMap (fun d =>
      if admissibleNext [36, 27, 24, 18, 9, 6, 3] d then
        let rawNum := 49 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 24, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 8).filter
        (admissibleNext [36, 27, 24, 18, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_16 :
    searchIndexLists 10 127 540 36 [36, 30, 27, 18, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 6).flatMap (fun d =>
      if admissibleNext [36, 30, 27, 18, 9, 6, 3] d then
        let rawNum := 127 * d - 540
        let rawDen := 540 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 27, 18, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 6).filter
        (admissibleNext [36, 30, 27, 18, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_17 :
    searchIndexLists 10 89 360 36 [36, 30, 24, 15, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 4).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 15, 12, 6, 3] d then
        let rawNum := 89 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 15, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 4).filter
        (admissibleNext [36, 30, 24, 15, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_18 :
    searchIndexLists 10 55 216 36 [36, 27, 24, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 3).flatMap (fun d =>
      if admissibleNext [36, 27, 24, 18, 12, 6, 3] d then
        let rawNum := 55 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 24, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 3).filter
        (admissibleNext [36, 27, 24, 18, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_19 :
    searchIndexLists 10 31 120 36 [36, 30, 24, 18, 12, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 18, 12, 6, 3] d then
        let rawNum := 31 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 18, 12, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 30, 24, 18, 12, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_20 :
    searchIndexLists 10 329 1080 30 [30, 27, 24, 18, 12, 9, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 27, 24, 18, 12, 9, 3] d then
        let rawNum := 329 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 27, 24, 18, 12, 9, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 27, 24, 18, 12, 9, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_21 :
    searchIndexLists 10 31 144 24 [24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 25 22).flatMap (fun d =>
      if admissibleNext [24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 22).filter
        (admissibleNext [24, 18, 16, 12, 8, 6, 4]) =
        [30, 32, 36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_22 :
    searchIndexLists 10 161 720 30 [30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 14).flatMap (fun d =>
      if admissibleNext [30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 161 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 14).filter
        (admissibleNext [30, 18, 16, 12, 8, 6, 4]) =
        [32, 36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_23 :
    searchIndexLists 10 65 288 32 [32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 12).flatMap (fun d =>
      if admissibleNext [32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 65 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 12).filter
        (admissibleNext [32, 18, 16, 12, 8, 6, 4]) =
        [36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_24 :
    searchIndexLists 10 11 48 36 [36, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 7).flatMap (fun d =>
      if admissibleNext [36, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 7).filter
        (admissibleNext [36, 18, 16, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_25 :
    searchIndexLists 10 167 720 40 [40, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 3).flatMap (fun d =>
      if admissibleNext [40, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 167 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [40, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 3).filter
        (admissibleNext [40, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_26 :
    searchIndexLists 10 235 1008 42 [42, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 235 * d - 1008
        let rawDen := 1008 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [42, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_27 :
    searchIndexLists 10 19 80 30 [30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 12).flatMap (fun d =>
      if admissibleNext [30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 12).filter
        (admissibleNext [30, 24, 16, 12, 8, 6, 4]) =
        [32, 36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_28 :
    searchIndexLists 10 23 96 32 [32, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 9).flatMap (fun d =>
      if admissibleNext [32, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 9).filter
        (admissibleNext [32, 24, 16, 12, 8, 6, 4]) =
        [36, 40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_29 :
    searchIndexLists 10 35 144 36 [36, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 5).flatMap (fun d =>
      if admissibleNext [36, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 35 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 5).filter
        (admissibleNext [36, 24, 16, 12, 8, 6, 4]) =
        [40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_30 :
    searchIndexLists 10 59 240 40 [40, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 0).flatMap (fun d =>
      if admissibleNext [40, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 59 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [40, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 0).filter
        (admissibleNext [40, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_31 :
    searchIndexLists 10 119 480 32 [32, 30, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 8).flatMap (fun d =>
      if admissibleNext [32, 30, 16, 12, 8, 6, 4] d then
        let rawNum := 119 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 8).filter
        (admissibleNext [32, 30, 16, 12, 8, 6, 4]) =
        [36, 40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_32 :
    searchIndexLists 10 181 720 36 [36, 30, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 3).flatMap (fun d =>
      if admissibleNext [36, 30, 16, 12, 8, 6, 4] d then
        let rawNum := 181 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 3).filter
        (admissibleNext [36, 30, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_33 :
    searchIndexLists 10 73 288 36 [36, 32, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 3).flatMap (fun d =>
      if admissibleNext [36, 32, 16, 12, 8, 6, 4] d then
        let rawNum := 73 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 3).filter
        (admissibleNext [36, 32, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_34 :
    searchIndexLists 10 11 45 30 [30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 10).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 45
        let rawDen := 45 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 10).filter
        (admissibleNext [30, 24, 18, 12, 8, 6, 4]) =
        [32, 36, 40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_35 :
    searchIndexLists 10 71 288 32 [32, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 8).flatMap (fun d =>
      if admissibleNext [32, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 71 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 8).filter
        (admissibleNext [32, 24, 18, 12, 8, 6, 4]) =
        [36, 40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_36 :
    searchIndexLists 10 1 4 36 [36, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 4).flatMap (fun d =>
      if admissibleNext [36, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 4
        let rawDen := 4 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 4).filter
        (admissibleNext [36, 24, 18, 12, 8, 6, 4]) =
        [40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_37 :
    searchIndexLists 10 367 1440 32 [32, 30, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 7).flatMap (fun d =>
      if admissibleNext [32, 30, 18, 12, 8, 6, 4] d then
        let rawNum := 367 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 7).filter
        (admissibleNext [32, 30, 18, 12, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_38 :
    searchIndexLists 10 31 120 36 [36, 30, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 30, 18, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 30, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_39 :
    searchIndexLists 10 25 96 36 [36, 32, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 32, 18, 12, 8, 6, 4] d then
        let rawNum := 25 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 32, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_40 :
    searchIndexLists 10 43 160 32 [32, 30, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 5).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 12, 8, 6, 4] d then
        let rawNum := 43 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 5).filter
        (admissibleNext [32, 30, 24, 12, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_41 :
    searchIndexLists 10 49 180 36 [36, 30, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 30, 24, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_42 :
    searchIndexLists 10 79 288 36 [36, 32, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 32, 24, 12, 8, 6, 4] d then
        let rawNum := 79 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 32, 24, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_43 :
    searchIndexLists 10 191 720 30 [30, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 7).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 191 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 7).filter
        (admissibleNext [30, 24, 18, 16, 8, 6, 4]) =
        [32, 36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_44 :
    searchIndexLists 10 77 288 32 [32, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 5).flatMap (fun d =>
      if admissibleNext [32, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 77 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 5).filter
        (admissibleNext [32, 24, 18, 16, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_45 :
    searchIndexLists 10 13 48 36 [36, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 13 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 24, 18, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_46 :
    searchIndexLists 10 397 1440 32 [32, 30, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 4).flatMap (fun d =>
      if admissibleNext [32, 30, 18, 16, 8, 6, 4] d then
        let rawNum := 397 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 4).filter
        (admissibleNext [32, 30, 18, 16, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_47 :
    searchIndexLists 10 139 480 32 [32, 30, 24, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 2).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 16, 8, 6, 4] d then
        let rawNum := 139 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 2).filter
        (admissibleNext [32, 30, 24, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_48 :
    searchIndexLists 10 427 1440 32 [32, 30, 24, 18, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 1).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 18, 8, 6, 4] d then
        let rawNum := 427 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 18, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 1).filter
        (admissibleNext [32, 30, 24, 18, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_49 :
    searchIndexLists 10 221 720 30 [30, 24, 18, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 2).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 16, 12, 6, 4] d then
        let rawNum := 221 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 2).filter
        (admissibleNext [30, 24, 18, 16, 12, 6, 4]) =
        [32] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_50 :
    searchIndexLists 10 89 288 32 [32, 24, 18, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 0).flatMap (fun d =>
      if admissibleNext [32, 24, 18, 16, 12, 6, 4] d then
        let rawNum := 89 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 18, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 0).filter
        (admissibleNext [32, 24, 18, 16, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_51 :
    searchIndexLists 10 23 72 30 [30, 24, 20, 18, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 31 1).flatMap (fun d =>
      if admissibleNext [30, 24, 20, 18, 12, 6, 4] d then
        let rawNum := 23 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 20, 18, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 1).filter
        (admissibleNext [30, 24, 20, 18, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_52 :
    searchIndexLists 10 197 560 28 [28, 24, 20, 16, 12, 8, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 29 0).flatMap (fun d =>
      if admissibleNext [28, 24, 20, 16, 12, 8, 4] d then
        let rawNum := 197 * d - 560
        let rawDen := 560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [28, 24, 20, 16, 12, 8, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 29 0).filter
        (admissibleNext [28, 24, 20, 16, 12, 8, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD7_53 :
    searchIndexLists 10 299 720 24 [24, 20, 18, 16, 12, 8, 6] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 25 0).flatMap (fun d =>
      if admissibleNext [24, 20, 18, 16, 12, 8, 6] d then
        let rawNum := 299 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 9 (rawNum / common) (rawDen / common) d
          (d :: [24, 20, 18, 16, 12, 8, 6])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 25 0).filter
        (admissibleNext [24, 20, 18, 16, 12, 8, 6]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
