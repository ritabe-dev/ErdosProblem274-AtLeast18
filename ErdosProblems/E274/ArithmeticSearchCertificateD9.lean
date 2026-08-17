import ErdosProblems.E274.ArithmeticSearchCertificateD10

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_0 :
    searchIndexLists 8 131 1080 45 [45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 46 20).flatMap (fun d =>
      if admissibleNext [45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 131 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 46 20).filter
        (admissibleNext [45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [48, 54, 60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_1 :
    searchIndexLists 8 53 432 48 [48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 17).flatMap (fun d =>
      if admissibleNext [48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 53 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 17).filter
        (admissibleNext [48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [54, 60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_2 :
    searchIndexLists 8 1 8 54 [54, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 10).flatMap (fun d =>
      if admissibleNext [54, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 1 * d - 8
        let rawDen := 8 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 10).filter
        (admissibleNext [54, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_3 :
    searchIndexLists 8 137 1080 60 [60, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 3).flatMap (fun d =>
      if admissibleNext [60, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 137 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [60, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 3).filter
        (admissibleNext [60, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_4 :
    searchIndexLists 8 277 2160 48 [48, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 14).flatMap (fun d =>
      if admissibleNext [48, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 277 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 14).filter
        (admissibleNext [48, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [54, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_5 :
    searchIndexLists 8 47 360 54 [54, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 7).flatMap (fun d =>
      if admissibleNext [54, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 47 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 7).filter
        (admissibleNext [54, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_6 :
    searchIndexLists 8 143 1080 60 [60, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 0).flatMap (fun d =>
      if admissibleNext [60, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 143 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [60, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 0).filter
        (admissibleNext [60, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_7 :
    searchIndexLists 8 19 144 54 [54, 48, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 6).flatMap (fun d =>
      if admissibleNext [54, 48, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 19 * d - 144
        let rawDen := 144 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 6).filter
        (admissibleNext [54, 48, 27, 24, 18, 12, 9, 6, 3]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_8 :
    searchIndexLists 8 11 80 48 [48, 45, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 10).flatMap (fun d =>
      if admissibleNext [48, 45, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 11 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 10).filter
        (admissibleNext [48, 45, 36, 24, 18, 12, 9, 6, 3]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_9 :
    searchIndexLists 8 151 1080 54 [54, 45, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 3).flatMap (fun d =>
      if admissibleNext [54, 45, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 151 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 45, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 3).filter
        (admissibleNext [54, 45, 36, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_10 :
    searchIndexLists 8 61 432 54 [54, 48, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 2).flatMap (fun d =>
      if admissibleNext [54, 48, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 61 * d - 432
        let rawDen := 432 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 2).filter
        (admissibleNext [54, 48, 36, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_11 :
    searchIndexLists 8 317 2160 54 [54, 48, 45, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 0).flatMap (fun d =>
      if admissibleNext [54, 48, 45, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 317 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 45, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 0).filter
        (admissibleNext [54, 48, 45, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_12 :
    searchIndexLists 8 307 2160 48 [48, 45, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 8).flatMap (fun d =>
      if admissibleNext [48, 45, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 307 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 8).filter
        (admissibleNext [48, 45, 36, 27, 18, 12, 9, 6, 3]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_13 :
    searchIndexLists 8 13 90 54 [54, 45, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 1).flatMap (fun d =>
      if admissibleNext [54, 45, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 13 * d - 90
        let rawDen := 90 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 45, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 1).filter
        (admissibleNext [54, 45, 36, 27, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_14 :
    searchIndexLists 8 7 48 54 [54, 48, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 0).flatMap (fun d =>
      if admissibleNext [54, 48, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 7 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 0).filter
        (admissibleNext [54, 48, 36, 27, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_15 :
    searchIndexLists 8 337 2160 48 [48, 45, 36, 27, 24, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 3).flatMap (fun d =>
      if admissibleNext [48, 45, 36, 27, 24, 12, 9, 6, 3] d then
        let rawNum := 337 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 36, 27, 24, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 3).filter
        (admissibleNext [48, 45, 36, 27, 24, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_16 :
    searchIndexLists 8 217 1440 32 [32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 33 21).flatMap (fun d =>
      if admissibleNext [32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 217 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 33 21).filter
        (admissibleNext [32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [36, 40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_17 :
    searchIndexLists 8 37 240 36 [36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 15).flatMap (fun d =>
      if admissibleNext [36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 15).filter
        (admissibleNext [36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_18 :
    searchIndexLists 8 113 720 40 [40, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 10).flatMap (fun d =>
      if admissibleNext [40, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 113 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 10).filter
        (admissibleNext [40, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_19 :
    searchIndexLists 8 797 5040 42 [42, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 8).flatMap (fun d =>
      if admissibleNext [42, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 797 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 8).filter
        (admissibleNext [42, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_20 :
    searchIndexLists 8 29 180 48 [48, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 1).flatMap (fun d =>
      if admissibleNext [48, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 180
        let rawDen := 180 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 1).filter
        (admissibleNext [48, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_21 :
    searchIndexLists 8 5 32 36 [36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 15).flatMap (fun d =>
      if admissibleNext [36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 5 * d - 32
        let rawDen := 32 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 15).filter
        (admissibleNext [36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_22 :
    searchIndexLists 8 229 1440 40 [40, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 10).flatMap (fun d =>
      if admissibleNext [40, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 229 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 10).filter
        (admissibleNext [40, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_23 :
    searchIndexLists 8 323 2016 42 [42, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 7).flatMap (fun d =>
      if admissibleNext [42, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 323 * d - 2016
        let rawDen := 2016 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 7).filter
        (admissibleNext [42, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_24 :
    searchIndexLists 8 47 288 48 [48, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 1).flatMap (fun d =>
      if admissibleNext [48, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 288
        let rawDen := 288 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 1).filter
        (admissibleNext [48, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_25 :
    searchIndexLists 8 13 80 40 [40, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 9).flatMap (fun d =>
      if admissibleNext [40, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 9).filter
        (admissibleNext [40, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_26 :
    searchIndexLists 8 55 336 42 [42, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 6).flatMap (fun d =>
      if admissibleNext [42, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 55 * d - 336
        let rawDen := 336 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 6).filter
        (admissibleNext [42, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_27 :
    searchIndexLists 8 1 6 48 [48, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 6
        let rawDen := 6 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_28 :
    searchIndexLists 8 839 5040 42 [42, 40, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 6).flatMap (fun d =>
      if admissibleNext [42, 40, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 839 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 6).filter
        (admissibleNext [42, 40, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_29 :
    searchIndexLists 8 79 480 36 [36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 12).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 79 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 12).filter
        (admissibleNext [36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [40, 42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_30 :
    searchIndexLists 8 241 1440 40 [40, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 7).flatMap (fun d =>
      if admissibleNext [40, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 241 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 7).filter
        (admissibleNext [40, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_31 :
    searchIndexLists 8 1699 10080 42 [42, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 5).flatMap (fun d =>
      if admissibleNext [42, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1699 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 5).filter
        (admissibleNext [42, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_32 :
    searchIndexLists 8 41 240 40 [40, 36, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 6).flatMap (fun d =>
      if admissibleNext [40, 36, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 41 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 6).filter
        (admissibleNext [40, 36, 30, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_33 :
    searchIndexLists 8 289 1680 42 [42, 36, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 4).flatMap (fun d =>
      if admissibleNext [42, 36, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 289 * d - 1680
        let rawDen := 1680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 4).filter
        (admissibleNext [42, 36, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_34 :
    searchIndexLists 8 881 5040 42 [42, 40, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 3).flatMap (fun d =>
      if admissibleNext [42, 40, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 881 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 3).filter
        (admissibleNext [42, 40, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_35 :
    searchIndexLists 8 83 480 40 [40, 36, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 6).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 83 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 6).filter
        (admissibleNext [40, 36, 32, 18, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_36 :
    searchIndexLists 8 39 224 42 [42, 36, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 3).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 39 * d - 224
        let rawDen := 224 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 3).filter
        (admissibleNext [42, 36, 32, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_37 :
    searchIndexLists 8 1783 10080 42 [42, 40, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 3).flatMap (fun d =>
      if admissibleNext [42, 40, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1783 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 3).filter
        (admissibleNext [42, 40, 32, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_38 :
    searchIndexLists 8 101 560 42 [42, 40, 36, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 2).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 101 * d - 560
        let rawDen := 560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 2).filter
        (admissibleNext [42, 40, 36, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_39 :
    searchIndexLists 8 257 1440 36 [36, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 8).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 257 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 8).filter
        (admissibleNext [36, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_40 :
    searchIndexLists 8 29 160 40 [40, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 4).flatMap (fun d =>
      if admissibleNext [40, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 4).filter
        (admissibleNext [40, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_41 :
    searchIndexLists 8 613 3360 42 [42, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 613 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_42 :
    searchIndexLists 8 133 720 40 [40, 36, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 3).flatMap (fun d =>
      if admissibleNext [40, 36, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 133 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 3).filter
        (admissibleNext [40, 36, 30, 24, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_43 :
    searchIndexLists 8 937 5040 42 [42, 36, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 36, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 937 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 36, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_44 :
    searchIndexLists 8 317 1680 42 [42, 40, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 40, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 317 * d - 1680
        let rawDen := 1680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 40, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_45 :
    searchIndexLists 8 269 1440 40 [40, 36, 32, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 2).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 269 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 2).filter
        (admissibleNext [40, 36, 32, 24, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_46 :
    searchIndexLists 8 379 2016 42 [42, 36, 32, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 379 * d - 2016
        let rawDen := 2016 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 36, 32, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_47 :
    searchIndexLists 8 281 1440 40 [40, 36, 32, 30, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 0).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 30, 16, 12, 8, 6, 4] d then
        let rawNum := 281 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 30, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 0).filter
        (admissibleNext [40, 36, 32, 30, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_48 :
    searchIndexLists 8 89 480 36 [36, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 7).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 89 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 7).filter
        (admissibleNext [36, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [40, 42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_49 :
    searchIndexLists 8 271 1440 40 [40, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 2).flatMap (fun d =>
      if admissibleNext [40, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 271 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 2).filter
        (admissibleNext [40, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_50 :
    searchIndexLists 8 1909 10080 42 [42, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 1909 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [42, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_51 :
    searchIndexLists 8 23 120 40 [40, 36, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 1).flatMap (fun d =>
      if admissibleNext [40, 36, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 1).filter
        (admissibleNext [40, 36, 30, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_52 :
    searchIndexLists 8 31 160 40 [40, 36, 32, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 1).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 1).filter
        (admissibleNext [40, 36, 32, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD9_53 :
    searchIndexLists 8 33 160 36 [36, 32, 30, 24, 18, 16, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 37 2).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 24, 18, 16, 8, 6, 4] d then
        let rawNum := 33 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 7 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 24, 18, 16, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 2).filter
        (admissibleNext [36, 32, 30, 24, 18, 16, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
