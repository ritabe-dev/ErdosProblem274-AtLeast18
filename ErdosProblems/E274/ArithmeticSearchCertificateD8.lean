import ErdosProblems.E274.ArithmeticSearchCertificateD9

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_0 :
    searchIndexLists 9 31 216 36 [36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 26).flatMap (fun d =>
      if admissibleNext [36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 31 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 26).filter
        (admissibleNext [36, 27, 24, 18, 12, 9, 6, 3]) =
        [45, 48, 54, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_1 :
    searchIndexLists 9 161 1080 45 [45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 15).flatMap (fun d =>
      if admissibleNext [45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 161 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 15).filter
        (admissibleNext [45, 27, 24, 18, 12, 9, 6, 3]) =
        [48, 54, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_2 :
    searchIndexLists 9 65 432 48 [48, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 11).flatMap (fun d =>
      if admissibleNext [48, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 65 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 11).filter
        (admissibleNext [48, 27, 24, 18, 12, 9, 6, 3]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_3 :
    searchIndexLists 9 11 72 54 [54, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 4).flatMap (fun d =>
      if admissibleNext [54, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 11 * d - 72
        let rawDen := 72 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [54, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 4).filter
        (admissibleNext [54, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_4 :
    searchIndexLists 9 19 120 45 [45, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 11).flatMap (fun d =>
      if admissibleNext [45, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 19 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 11).filter
        (admissibleNext [45, 36, 24, 18, 12, 9, 6, 3]) =
        [48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_5 :
    searchIndexLists 9 23 144 48 [48, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 8).flatMap (fun d =>
      if admissibleNext [48, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 23 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 8).filter
        (admissibleNext [48, 36, 24, 18, 12, 9, 6, 3]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_6 :
    searchIndexLists 9 35 216 54 [54, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 1).flatMap (fun d =>
      if admissibleNext [54, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 35 * d - 216
        let rawDen := 216 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [54, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 1).filter
        (admissibleNext [54, 36, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_7 :
    searchIndexLists 9 119 720 48 [48, 45, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 6).flatMap (fun d =>
      if admissibleNext [48, 45, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 119 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 6).filter
        (admissibleNext [48, 45, 24, 18, 12, 9, 6, 3]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_8 :
    searchIndexLists 9 22 135 45 [45, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 10).flatMap (fun d =>
      if admissibleNext [45, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 22 * d - 135
        let rawDen := 135 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 10).filter
        (admissibleNext [45, 36, 27, 18, 12, 9, 6, 3]) =
        [48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_9 :
    searchIndexLists 9 71 432 48 [48, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 6).flatMap (fun d =>
      if admissibleNext [48, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 71 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 6).filter
        (admissibleNext [48, 36, 27, 18, 12, 9, 6, 3]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_10 :
    searchIndexLists 9 1 6 54 [54, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 0).flatMap (fun d =>
      if admissibleNext [54, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 1 * d - 6
        let rawDen := 6 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [54, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 0).filter
        (admissibleNext [54, 36, 27, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_11 :
    searchIndexLists 9 367 2160 48 [48, 45, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 4).flatMap (fun d =>
      if admissibleNext [48, 45, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 367 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 4).filter
        (admissibleNext [48, 45, 27, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_12 :
    searchIndexLists 9 43 240 48 [48, 45, 36, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 45, 36, 18, 12, 9, 6, 3] d then
        let rawNum := 43 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 36, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 45, 36, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_13 :
    searchIndexLists 9 191 1080 45 [45, 36, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 5).flatMap (fun d =>
      if admissibleNext [45, 36, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 191 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 5).filter
        (admissibleNext [45, 36, 27, 24, 12, 9, 6, 3]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_14 :
    searchIndexLists 9 77 432 48 [48, 36, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 36, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 77 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 36, 27, 24, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_15 :
    searchIndexLists 9 397 2160 48 [48, 45, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 45, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 397 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 45, 27, 24, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_16 :
    searchIndexLists 9 131 720 30 [30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 31 19).flatMap (fun d =>
      if admissibleNext [30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 131 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 31 19).filter
        (admissibleNext [30, 24, 18, 16, 12, 8, 6, 4]) =
        [32, 36, 40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_17 :
    searchIndexLists 9 53 288 32 [32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 16).flatMap (fun d =>
      if admissibleNext [32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 53 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 16).filter
        (admissibleNext [32, 24, 18, 16, 12, 8, 6, 4]) =
        [36, 40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_18 :
    searchIndexLists 9 3 16 36 [36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 12).flatMap (fun d =>
      if admissibleNext [36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3 * d - 16
        let rawDen := 16 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 12).filter
        (admissibleNext [36, 24, 18, 16, 12, 8, 6, 4]) =
        [40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_19 :
    searchIndexLists 9 137 720 40 [40, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 7).flatMap (fun d =>
      if admissibleNext [40, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 137 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 7).filter
        (admissibleNext [40, 24, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_20 :
    searchIndexLists 9 193 1008 42 [42, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 5).flatMap (fun d =>
      if admissibleNext [42, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 193 * d - 1008
        let rawDen := 1008 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [42, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 5).filter
        (admissibleNext [42, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_21 :
    searchIndexLists 9 277 1440 32 [32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 14).flatMap (fun d =>
      if admissibleNext [32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 277 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 14).filter
        (admissibleNext [32, 30, 18, 16, 12, 8, 6, 4]) =
        [36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_22 :
    searchIndexLists 9 47 240 36 [36, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 9).flatMap (fun d =>
      if admissibleNext [36, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 9).filter
        (admissibleNext [36, 30, 18, 16, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_23 :
    searchIndexLists 9 143 720 40 [40, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 5).flatMap (fun d =>
      if admissibleNext [40, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 143 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 5).filter
        (admissibleNext [40, 30, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_24 :
    searchIndexLists 9 1007 5040 42 [42, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 3).flatMap (fun d =>
      if admissibleNext [42, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1007 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [42, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 3).filter
        (admissibleNext [42, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_25 :
    searchIndexLists 9 19 96 36 [36, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 9).flatMap (fun d =>
      if admissibleNext [36, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 9).filter
        (admissibleNext [36, 32, 18, 16, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_26 :
    searchIndexLists 9 289 1440 40 [40, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 4).flatMap (fun d =>
      if admissibleNext [40, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 289 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 4).filter
        (admissibleNext [40, 32, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_27 :
    searchIndexLists 9 407 2016 42 [42, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 2).flatMap (fun d =>
      if admissibleNext [42, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 407 * d - 2016
        let rawDen := 2016 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [42, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 2).filter
        (admissibleNext [42, 32, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_28 :
    searchIndexLists 9 49 240 40 [40, 36, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 4).flatMap (fun d =>
      if admissibleNext [40, 36, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 4).filter
        (admissibleNext [40, 36, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_29 :
    searchIndexLists 9 23 112 42 [42, 36, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 36, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 112
        let rawDen := 112 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 36, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_30 :
    searchIndexLists 9 1049 5040 42 [42, 40, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 40, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1049 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 40, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_31 :
    searchIndexLists 9 33 160 32 [32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 11).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 33 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 11).filter
        (admissibleNext [32, 30, 24, 16, 12, 8, 6, 4]) =
        [36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_32 :
    searchIndexLists 9 151 720 36 [36, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 6).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 151 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 6).filter
        (admissibleNext [36, 30, 24, 16, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_33 :
    searchIndexLists 9 17 80 40 [40, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 2).flatMap (fun d =>
      if admissibleNext [40, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 17 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 2).filter
        (admissibleNext [40, 30, 24, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_34 :
    searchIndexLists 9 359 1680 42 [42, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 359 * d - 1680
        let rawDen := 1680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [42, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_35 :
    searchIndexLists 9 61 288 36 [36, 32, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 6).flatMap (fun d =>
      if admissibleNext [36, 32, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 61 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 6).filter
        (admissibleNext [36, 32, 24, 16, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_36 :
    searchIndexLists 9 103 480 40 [40, 32, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 1).flatMap (fun d =>
      if admissibleNext [40, 32, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 103 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 1).filter
        (admissibleNext [40, 32, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_37 :
    searchIndexLists 9 157 720 40 [40, 36, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 1).flatMap (fun d =>
      if admissibleNext [40, 36, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 157 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 1).filter
        (admissibleNext [40, 36, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_38 :
    searchIndexLists 9 317 1440 36 [36, 32, 30, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 4).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 16, 12, 8, 6, 4] d then
        let rawNum := 317 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 4).filter
        (admissibleNext [36, 32, 30, 16, 12, 8, 6, 4]) =
        [40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_39 :
    searchIndexLists 9 107 480 40 [40, 32, 30, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 0).flatMap (fun d =>
      if admissibleNext [40, 32, 30, 16, 12, 8, 6, 4] d then
        let rawNum := 107 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 30, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 0).filter
        (admissibleNext [40, 32, 30, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_40 :
    searchIndexLists 9 307 1440 32 [32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 10).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 307 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 10).filter
        (admissibleNext [32, 30, 24, 18, 12, 8, 6, 4]) =
        [36, 40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_41 :
    searchIndexLists 9 13 60 36 [36, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 5).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 60
        let rawDen := 60 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 5).filter
        (admissibleNext [36, 30, 24, 18, 12, 8, 6, 4]) =
        [40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_42 :
    searchIndexLists 9 79 360 40 [40, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 1).flatMap (fun d =>
      if admissibleNext [40, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 79 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 1).filter
        (admissibleNext [40, 30, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_43 :
    searchIndexLists 9 7 32 36 [36, 32, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 5).flatMap (fun d =>
      if admissibleNext [36, 32, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 32
        let rawDen := 32 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 5).filter
        (admissibleNext [36, 32, 24, 18, 12, 8, 6, 4]) =
        [40] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_44 :
    searchIndexLists 9 319 1440 40 [40, 32, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 0).flatMap (fun d =>
      if admissibleNext [40, 32, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 319 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 0).filter
        (admissibleNext [40, 32, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_45 :
    searchIndexLists 9 9 40 40 [40, 36, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 0).flatMap (fun d =>
      if admissibleNext [40, 36, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 9 * d - 40
        let rawDen := 40 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 0).filter
        (admissibleNext [40, 36, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_46 :
    searchIndexLists 9 109 480 36 [36, 32, 30, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 3).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 18, 12, 8, 6, 4] d then
        let rawNum := 109 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 3).filter
        (admissibleNext [36, 32, 30, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_47 :
    searchIndexLists 9 347 1440 36 [36, 32, 30, 24, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 24, 12, 8, 6, 4] d then
        let rawNum := 347 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 24, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 32, 30, 24, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_48 :
    searchIndexLists 9 337 1440 32 [32, 30, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 6).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 337 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 6).filter
        (admissibleNext [32, 30, 24, 18, 16, 8, 6, 4]) =
        [36] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_49 :
    searchIndexLists 9 19 80 36 [36, 30, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 19 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 30, 24, 18, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_50 :
    searchIndexLists 9 23 96 36 [36, 32, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 1).flatMap (fun d =>
      if admissibleNext [36, 32, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 23 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 1).filter
        (admissibleNext [36, 32, 24, 18, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_51 :
    searchIndexLists 9 119 480 36 [36, 32, 30, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 0).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 18, 16, 8, 6, 4] d then
        let rawNum := 119 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 0).filter
        (admissibleNext [36, 32, 30, 18, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD8_52 :
    searchIndexLists 9 397 1440 32 [32, 30, 24, 18, 16, 12, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 33 0).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 18, 16, 12, 6, 4] d then
        let rawNum := 397 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 8 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 18, 16, 12, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 0).filter
        (admissibleNext [32, 30, 24, 18, 16, 12, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
