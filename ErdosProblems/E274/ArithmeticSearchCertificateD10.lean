import ErdosProblems.E274.ArithmeticSearchCertificateD11

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_0 :
    searchIndexLists 7 217 2160 48 [48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 21).flatMap (fun d =>
      if admissibleNext [48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 217 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 21).filter
        (admissibleNext [48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [54, 60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_1 :
    searchIndexLists 7 37 360 54 [54, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 14).flatMap (fun d =>
      if admissibleNext [54, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 37 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [54, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 14).filter
        (admissibleNext [54, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_2 :
    searchIndexLists 7 113 1080 60 [60, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 6).flatMap (fun d =>
      if admissibleNext [60, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 113 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [60, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 6).filter
        (admissibleNext [60, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_3 :
    searchIndexLists 7 797 7560 63 [63, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 3).flatMap (fun d =>
      if admissibleNext [63, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 797 * d - 7560
        let rawDen := 7560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [63, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 3).filter
        (admissibleNext [63, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_4 :
    searchIndexLists 7 5 48 54 [54, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 13).flatMap (fun d =>
      if admissibleNext [54, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 5 * d - 48
        let rawDen := 48 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 13).filter
        (admissibleNext [54, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_5 :
    searchIndexLists 7 229 2160 60 [60, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 6).flatMap (fun d =>
      if admissibleNext [60, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 229 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 6).filter
        (admissibleNext [60, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_6 :
    searchIndexLists 7 323 3024 63 [63, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 2).flatMap (fun d =>
      if admissibleNext [63, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 323 * d - 3024
        let rawDen := 3024 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [63, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 2).filter
        (admissibleNext [63, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_7 :
    searchIndexLists 7 13 120 60 [60, 54, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 4).flatMap (fun d =>
      if admissibleNext [60, 54, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 13 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 4).filter
        (admissibleNext [60, 54, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_8 :
    searchIndexLists 7 55 504 63 [63, 54, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 1).flatMap (fun d =>
      if admissibleNext [63, 54, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 55 * d - 504
        let rawDen := 504 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [63, 54, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 1).filter
        (admissibleNext [63, 54, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_9 :
    searchIndexLists 7 839 7560 63 [63, 60, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 0).flatMap (fun d =>
      if admissibleNext [63, 60, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 839 * d - 7560
        let rawDen := 7560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 0).filter
        (admissibleNext [63, 60, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_10 :
    searchIndexLists 7 79 720 54 [54, 48, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 9).flatMap (fun d =>
      if admissibleNext [54, 48, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 79 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 9).filter
        (admissibleNext [54, 48, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [60, 63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_11 :
    searchIndexLists 7 241 2160 60 [60, 48, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 2).flatMap (fun d =>
      if admissibleNext [60, 48, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 241 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 2).filter
        (admissibleNext [60, 48, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_12 :
    searchIndexLists 7 41 360 60 [60, 54, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 1).flatMap (fun d =>
      if admissibleNext [60, 54, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 41 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 1).filter
        (admissibleNext [60, 54, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_13 :
    searchIndexLists 7 83 720 60 [60, 54, 48, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 0).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 83 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 0).filter
        (admissibleNext [60, 54, 48, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_14 :
    searchIndexLists 7 257 2160 54 [54, 48, 45, 36, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 4).flatMap (fun d =>
      if admissibleNext [54, 48, 45, 36, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 257 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 45, 36, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 4).filter
        (admissibleNext [54, 48, 45, 36, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_15 :
    searchIndexLists 7 89 720 54 [54, 48, 45, 36, 27, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 2).flatMap (fun d =>
      if admissibleNext [54, 48, 45, 36, 27, 18, 12, 9, 6, 3] d then
        let rawNum := 89 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 45, 36, 27, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 2).filter
        (admissibleNext [54, 48, 45, 36, 27, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_16 :
    searchIndexLists 7 59 480 36 [36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 37 20).flatMap (fun d =>
      if admissibleNext [36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 59 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 37 20).filter
        (admissibleNext [36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [40, 42, 48, 54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_17 :
    searchIndexLists 7 181 1440 40 [40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 15).flatMap (fun d =>
      if admissibleNext [40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 181 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 15).filter
        (admissibleNext [40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_18 :
    searchIndexLists 7 1279 10080 42 [42, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 13).flatMap (fun d =>
      if admissibleNext [42, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1279 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 13).filter
        (admissibleNext [42, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_19 :
    searchIndexLists 7 187 1440 48 [48, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 5).flatMap (fun d =>
      if admissibleNext [48, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 187 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 5).filter
        (admissibleNext [48, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_20 :
    searchIndexLists 7 31 240 40 [40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 14).flatMap (fun d =>
      if admissibleNext [40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 240
        let rawDen := 240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 14).filter
        (admissibleNext [40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_21 :
    searchIndexLists 7 73 560 42 [42, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 11).flatMap (fun d =>
      if admissibleNext [42, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 73 * d - 560
        let rawDen := 560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 11).filter
        (admissibleNext [42, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_22 :
    searchIndexLists 7 2 15 48 [48, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 4).flatMap (fun d =>
      if admissibleNext [48, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 4).filter
        (admissibleNext [48, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_23 :
    searchIndexLists 7 671 5040 42 [42, 40, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 10).flatMap (fun d =>
      if admissibleNext [42, 40, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 671 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 10).filter
        (admissibleNext [42, 40, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_24 :
    searchIndexLists 7 49 360 48 [48, 40, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 3).flatMap (fun d =>
      if admissibleNext [48, 40, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 3).filter
        (admissibleNext [48, 40, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_25 :
    searchIndexLists 7 173 1260 48 [48, 42, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 42, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 173 * d - 1260
        let rawDen := 1260 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 42, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_26 :
    searchIndexLists 7 21 160 40 [40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 13).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 21 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 13).filter
        (admissibleNext [40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_27 :
    searchIndexLists 7 89 672 42 [42, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 10).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 89 * d - 672
        let rawDen := 672 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 10).filter
        (admissibleNext [42, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_28 :
    searchIndexLists 7 13 96 48 [48, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 3).flatMap (fun d =>
      if admissibleNext [48, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 3).filter
        (admissibleNext [48, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_29 :
    searchIndexLists 7 1363 10080 42 [42, 40, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 9).flatMap (fun d =>
      if admissibleNext [42, 40, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1363 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 9).filter
        (admissibleNext [42, 40, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_30 :
    searchIndexLists 7 199 1440 48 [48, 40, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 40, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 199 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 40, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_31 :
    searchIndexLists 7 281 2016 48 [48, 42, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 42, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 281 * d - 2016
        let rawDen := 2016 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 42, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_32 :
    searchIndexLists 7 233 1680 42 [42, 40, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 8).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 233 * d - 1680
        let rawDen := 1680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 8).filter
        (admissibleNext [42, 40, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_33 :
    searchIndexLists 7 17 120 48 [48, 40, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 1).flatMap (fun d =>
      if admissibleNext [48, 40, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 17 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 1).filter
        (admissibleNext [48, 40, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_34 :
    searchIndexLists 7 1 7 48 [48, 42, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 1).flatMap (fun d =>
      if admissibleNext [48, 42, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 7
        let rawDen := 7 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 1).filter
        (admissibleNext [48, 42, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_35 :
    searchIndexLists 7 367 2520 48 [48, 42, 40, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 367 * d - 2520
        let rawDen := 2520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 42, 40, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_36 :
    searchIndexLists 7 67 480 40 [40, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 10).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 67 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 10).filter
        (admissibleNext [40, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [42, 48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_37 :
    searchIndexLists 7 473 3360 42 [42, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 7).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 473 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 7).filter
        (admissibleNext [42, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_38 :
    searchIndexLists 7 23 160 48 [48, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_39 :
    searchIndexLists 7 1447 10080 42 [42, 40, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 6).flatMap (fun d =>
      if admissibleNext [42, 40, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1447 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 6).filter
        (admissibleNext [42, 40, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_40 :
    searchIndexLists 7 247 1680 42 [42, 40, 36, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 5).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 247 * d - 1680
        let rawDen := 1680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 5).filter
        (admissibleNext [42, 40, 36, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_41 :
    searchIndexLists 7 167 1120 42 [42, 40, 36, 32, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 4).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 167 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 4).filter
        (admissibleNext [42, 40, 36, 32, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_42 :
    searchIndexLists 7 221 1440 40 [40, 36, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 5).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 221 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 5).filter
        (admissibleNext [40, 36, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_43 :
    searchIndexLists 7 1559 10080 42 [42, 36, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 3).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 1559 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 3).filter
        (admissibleNext [42, 36, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_44 :
    searchIndexLists 7 529 3360 42 [42, 40, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 2).flatMap (fun d =>
      if admissibleNext [42, 40, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 529 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 2).filter
        (admissibleNext [42, 40, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_45 :
    searchIndexLists 7 811 5040 42 [42, 40, 36, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 811 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 40, 36, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_46 :
    searchIndexLists 7 1643 10080 42 [42, 40, 36, 32, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 1643 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 40, 36, 32, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_47 :
    searchIndexLists 7 77 480 40 [40, 36, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 41 3).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 77 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 3).filter
        (admissibleNext [40, 36, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [42] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_48 :
    searchIndexLists 7 181 1120 42 [42, 36, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 181 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 36, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD10_49 :
    searchIndexLists 7 1657 10080 42 [42, 40, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 0).flatMap (fun d =>
      if admissibleNext [42, 40, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 1657 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 6 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 0).filter
        (admissibleNext [42, 40, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
