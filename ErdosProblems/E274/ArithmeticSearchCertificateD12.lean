import ErdosProblems.E274.ArithmeticSearchCertificateD13

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_0 :
    searchIndexLists 5 47 720 60 [60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 16).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 47 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 16).filter
        (admissibleNext [60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_1 :
    searchIndexLists 5 37 560 63 [63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 12).flatMap (fun d =>
      if admissibleNext [63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 37 * d - 560
        let rawDen := 560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 12).filter
        (admissibleNext [63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_2 :
    searchIndexLists 5 49 720 72 [72, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 1).flatMap (fun d =>
      if admissibleNext [72, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 49 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [72, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 1).filter
        (admissibleNext [72, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_3 :
    searchIndexLists 5 1027 15120 63 [63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 10).flatMap (fun d =>
      if admissibleNext [63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 1027 * d - 15120
        let rawDen := 15120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 10).filter
        (admissibleNext [63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_4 :
    searchIndexLists 5 59 840 63 [63, 60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 8).flatMap (fun d =>
      if admissibleNext [63, 60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 59 * d - 840
        let rawDen := 840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 8).filter
        (admissibleNext [63, 60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_5 :
    searchIndexLists 5 361 5040 63 [63, 60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 6).flatMap (fun d =>
      if admissibleNext [63, 60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 361 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 6).filter
        (admissibleNext [63, 60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_6 :
    searchIndexLists 5 389 5040 63 [63, 60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 1).flatMap (fun d =>
      if admissibleNext [63, 60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 389 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 1).filter
        (admissibleNext [63, 60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_7 :
    searchIndexLists 5 83 1120 42 [42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 43 25).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 83 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 25).filter
        (admissibleNext [42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48, 54, 56, 60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_8 :
    searchIndexLists 5 37 480 48 [48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 16).flatMap (fun d =>
      if admissibleNext [48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 16).filter
        (admissibleNext [48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56, 60, 64] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_9 :
    searchIndexLists 5 343 4320 54 [54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 8).flatMap (fun d =>
      if admissibleNext [54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 343 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 8).filter
        (admissibleNext [54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_10 :
    searchIndexLists 5 269 3360 56 [56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 6).flatMap (fun d =>
      if admissibleNext [56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 269 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 6).filter
        (admissibleNext [56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_11 :
    searchIndexLists 5 13 160 60 [60, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 1).flatMap (fun d =>
      if admissibleNext [60, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [60, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 1).filter
        (admissibleNext [60, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_12 :
    searchIndexLists 5 263 3360 48 [48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 15).flatMap (fun d =>
      if admissibleNext [48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 263 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 15).filter
        (admissibleNext [48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_13 :
    searchIndexLists 5 2437 30240 54 [54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 8).flatMap (fun d =>
      if admissibleNext [54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2437 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 8).filter
        (admissibleNext [54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_14 :
    searchIndexLists 5 13 160 56 [56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 5).flatMap (fun d =>
      if admissibleNext [56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 5).filter
        (admissibleNext [56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_15 :
    searchIndexLists 5 277 3360 60 [60, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 0).flatMap (fun d =>
      if admissibleNext [60, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 277 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [60, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 0).filter
        (admissibleNext [60, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_16 :
    searchIndexLists 5 361 4320 54 [54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 5).flatMap (fun d =>
      if admissibleNext [54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 361 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 5).filter
        (admissibleNext [54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_17 :
    searchIndexLists 5 283 3360 56 [56, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 3).flatMap (fun d =>
      if admissibleNext [56, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 283 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 3).filter
        (admissibleNext [56, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_18 :
    searchIndexLists 5 2617 30240 56 [56, 54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 1).flatMap (fun d =>
      if admissibleNext [56, 54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2617 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 1).filter
        (admissibleNext [56, 54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_19 :
    searchIndexLists 5 817 10080 48 [48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 13).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 817 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 13).filter
        (admissibleNext [48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_20 :
    searchIndexLists 5 2521 30240 54 [54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 5).flatMap (fun d =>
      if admissibleNext [54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2521 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 5).filter
        (admissibleNext [54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_21 :
    searchIndexLists 5 121 1440 56 [56, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 3).flatMap (fun d =>
      if admissibleNext [56, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 121 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 3).filter
        (admissibleNext [56, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_22 :
    searchIndexLists 5 373 4320 54 [54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 3).flatMap (fun d =>
      if admissibleNext [54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 373 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 3).filter
        (admissibleNext [54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_23 :
    searchIndexLists 5 877 10080 56 [56, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 1).flatMap (fun d =>
      if admissibleNext [56, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 877 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 1).filter
        (admissibleNext [56, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_24 :
    searchIndexLists 5 2647 30240 54 [54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 3).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2647 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 3).filter
        (admissibleNext [54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_25 :
    searchIndexLists 5 127 1440 56 [56, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 0).flatMap (fun d =>
      if admissibleNext [56, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 127 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 0).filter
        (admissibleNext [56, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_26 :
    searchIndexLists 5 71 840 48 [48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 11).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 71 * d - 840
        let rawDen := 840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 11).filter
        (admissibleNext [48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_27 :
    searchIndexLists 5 1313 15120 54 [54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 3).flatMap (fun d =>
      if admissibleNext [54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1313 * d - 15120
        let rawDen := 15120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 3).filter
        (admissibleNext [54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_28 :
    searchIndexLists 5 7 80 56 [56, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 1).flatMap (fun d =>
      if admissibleNext [56, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [56, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 1).filter
        (admissibleNext [56, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_29 :
    searchIndexLists 5 97 1080 54 [54, 48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 1).flatMap (fun d =>
      if admissibleNext [54, 48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 97 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 1).filter
        (admissibleNext [54, 48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_30 :
    searchIndexLists 5 86 945 54 [54, 48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 0).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 86 * d - 945
        let rawDen := 945 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 0).filter
        (admissibleNext [54, 48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_31 :
    searchIndexLists 5 97 1120 48 [48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 9).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 97 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 9).filter
        (admissibleNext [48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_32 :
    searchIndexLists 5 2689 30240 54 [54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 2).flatMap (fun d =>
      if admissibleNext [54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2689 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 2).filter
        (admissibleNext [54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_33 :
    searchIndexLists 5 397 4320 54 [54, 48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 0).flatMap (fun d =>
      if admissibleNext [54, 48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 397 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 0).filter
        (admissibleNext [54, 48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD12_34 :
    searchIndexLists 5 319 3360 48 [48, 42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 4).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 319 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 4 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 4).filter
        (admissibleNext [48, 42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
