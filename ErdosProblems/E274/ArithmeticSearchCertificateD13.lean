import ErdosProblems.E274.ArithmeticSearchCertificateD14

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_0 :
    searchIndexLists 4 83 1680 63 [63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 17).flatMap (fun d =>
      if admissibleNext [63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 83 * d - 1680
        let rawDen := 1680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 17).filter
        (admissibleNext [63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_1 :
    searchIndexLists 4 37 720 72 [72, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 5).flatMap (fun d =>
      if admissibleNext [72, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 37 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 5).filter
        (admissibleNext [72, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_2 :
    searchIndexLists 4 263 5040 72 [72, 63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 4).flatMap (fun d =>
      if admissibleNext [72, 63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 263 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [72, 63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 4).filter
        (admissibleNext [72, 63, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_3 :
    searchIndexLists 4 817 15120 72 [72, 63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 2).flatMap (fun d =>
      if admissibleNext [72, 63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 817 * d - 15120
        let rawDen := 15120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [72, 63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 2).filter
        (admissibleNext [72, 63, 60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_4 :
    searchIndexLists 4 179 3360 48 [48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 49 27).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 179 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 27).filter
        (admissibleNext [48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56, 60, 64, 66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_5 :
    searchIndexLists 4 1681 30240 54 [54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 17).flatMap (fun d =>
      if admissibleNext [54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1681 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 17).filter
        (admissibleNext [54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_6 :
    searchIndexLists 4 9 160 56 [56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 15).flatMap (fun d =>
      if admissibleNext [56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 15).filter
        (admissibleNext [56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_7 :
    searchIndexLists 4 193 3360 60 [60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 9).flatMap (fun d =>
      if admissibleNext [60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 193 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 9).filter
        (admissibleNext [60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_8 :
    searchIndexLists 4 131 2240 64 [64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 4).flatMap (fun d =>
      if admissibleNext [64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 131 * d - 2240
        let rawDen := 2240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 4).filter
        (admissibleNext [64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_9 :
    searchIndexLists 4 2179 36960 66 [66, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 1).flatMap (fun d =>
      if admissibleNext [66, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2179 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [66, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 1).filter
        (admissibleNext [66, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_10 :
    searchIndexLists 4 253 4320 54 [54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 14).flatMap (fun d =>
      if admissibleNext [54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 253 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 14).filter
        (admissibleNext [54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_11 :
    searchIndexLists 4 199 3360 56 [56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 11).flatMap (fun d =>
      if admissibleNext [56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 199 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 11).filter
        (admissibleNext [56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_12 :
    searchIndexLists 4 29 480 60 [60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 6).flatMap (fun d =>
      if admissibleNext [60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 6).filter
        (admissibleNext [60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_13 :
    searchIndexLists 4 59 960 64 [64, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 1).flatMap (fun d =>
      if admissibleNext [64, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 59 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [64, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 1).filter
        (admissibleNext [64, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_14 :
    searchIndexLists 4 1861 30240 56 [56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 8).flatMap (fun d =>
      if admissibleNext [56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1861 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 8).filter
        (admissibleNext [56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_15 :
    searchIndexLists 4 271 4320 60 [60, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 3).flatMap (fun d =>
      if admissibleNext [60, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 271 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 3).filter
        (admissibleNext [60, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_16 :
    searchIndexLists 4 71 1120 60 [60, 56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 3).flatMap (fun d =>
      if admissibleNext [60, 56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 71 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 3).filter
        (admissibleNext [60, 56, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_17 :
    searchIndexLists 4 1807 30240 54 [54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 12).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1807 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 12).filter
        (admissibleNext [54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_18 :
    searchIndexLists 4 29 480 56 [56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 10).flatMap (fun d =>
      if admissibleNext [56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 10).filter
        (admissibleNext [56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_19 :
    searchIndexLists 4 69 1120 60 [60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 4).flatMap (fun d =>
      if admissibleNext [60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 69 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 4).filter
        (admissibleNext [60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_20 :
    searchIndexLists 4 271 4320 56 [56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 7).flatMap (fun d =>
      if admissibleNext [56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 271 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 7).filter
        (admissibleNext [56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_21 :
    searchIndexLists 4 1933 30240 60 [60, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 2).flatMap (fun d =>
      if admissibleNext [60, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1933 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 2).filter
        (admissibleNext [60, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_22 :
    searchIndexLists 4 31 480 60 [60, 56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 1).flatMap (fun d =>
      if admissibleNext [60, 56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 1).filter
        (admissibleNext [60, 56, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_23 :
    searchIndexLists 4 1987 30240 56 [56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 4).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1987 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 4).filter
        (admissibleNext [56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_24 :
    searchIndexLists 4 1891 30240 54 [54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 9).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1891 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 9).filter
        (admissibleNext [54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_25 :
    searchIndexLists 4 91 1440 56 [56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 7).flatMap (fun d =>
      if admissibleNext [56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 91 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 7).filter
        (admissibleNext [56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_26 :
    searchIndexLists 4 649 10080 60 [60, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 2).flatMap (fun d =>
      if admissibleNext [60, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 649 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 2).filter
        (admissibleNext [60, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_27 :
    searchIndexLists 4 283 4320 56 [56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 5).flatMap (fun d =>
      if admissibleNext [56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 283 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 5).filter
        (admissibleNext [56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_28 :
    searchIndexLists 4 2071 30240 56 [56, 54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 2).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2071 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 2).filter
        (admissibleNext [56, 54, 48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_29 :
    searchIndexLists 4 301 4320 56 [56, 54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 1).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 301 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 1).filter
        (admissibleNext [56, 54, 48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_30 :
    searchIndexLists 4 499 7560 54 [54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 6).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 499 * d - 7560
        let rawDen := 7560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 6).filter
        (admissibleNext [54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_31 :
    searchIndexLists 4 1 15 56 [56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 4).flatMap (fun d =>
      if admissibleNext [56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 15
        let rawDen := 15 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 4).filter
        (admissibleNext [56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_32 :
    searchIndexLists 4 149 2160 56 [56, 54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 1).flatMap (fun d =>
      if admissibleNext [56, 54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 149 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 1).filter
        (admissibleNext [56, 54, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_33 :
    searchIndexLists 4 2059 30240 54 [54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 4).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2059 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 4).filter
        (admissibleNext [54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_34 :
    searchIndexLists 4 11 160 56 [56, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 2).flatMap (fun d =>
      if admissibleNext [56, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 2).filter
        (admissibleNext [56, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD13_35 :
    searchIndexLists 4 307 4320 56 [56, 54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 0).flatMap (fun d =>
      if admissibleNext [56, 54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 307 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 3 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 0).filter
        (admissibleNext [56, 54, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
