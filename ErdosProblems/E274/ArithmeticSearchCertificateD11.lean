import ErdosProblems.E274.ArithmeticSearchCertificateD12

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_0 :
    searchIndexLists 6 59 720 54 [54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 19).flatMap (fun d =>
      if admissibleNext [54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 59 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 19).filter
        (admissibleNext [54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [60, 63, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_1 :
    searchIndexLists 6 181 2160 60 [60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 11).flatMap (fun d =>
      if admissibleNext [60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 181 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 11).filter
        (admissibleNext [60, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_2 :
    searchIndexLists 6 1279 15120 63 [63, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 7).flatMap (fun d =>
      if admissibleNext [63, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 1279 * d - 15120
        let rawDen := 15120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 7).filter
        (admissibleNext [63, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_3 :
    searchIndexLists 6 31 360 60 [60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 9).flatMap (fun d =>
      if admissibleNext [60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 31 * d - 360
        let rawDen := 360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 9).filter
        (admissibleNext [60, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_4 :
    searchIndexLists 6 73 840 63 [63, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 6).flatMap (fun d =>
      if admissibleNext [63, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 73 * d - 840
        let rawDen := 840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 6).filter
        (admissibleNext [63, 54, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_5 :
    searchIndexLists 6 671 7560 63 [63, 60, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 4).flatMap (fun d =>
      if admissibleNext [63, 60, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 671 * d - 7560
        let rawDen := 7560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 4).filter
        (admissibleNext [63, 60, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_6 :
    searchIndexLists 6 7 80 60 [60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 8).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 7 * d - 80
        let rawDen := 80 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 8).filter
        (admissibleNext [60, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_7 :
    searchIndexLists 6 89 1008 63 [63, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 4).flatMap (fun d =>
      if admissibleNext [63, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 89 * d - 1008
        let rawDen := 1008 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 4).filter
        (admissibleNext [63, 54, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_8 :
    searchIndexLists 6 1363 15120 63 [63, 60, 48, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 3).flatMap (fun d =>
      if admissibleNext [63, 60, 48, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 1363 * d - 15120
        let rawDen := 15120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 48, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 3).filter
        (admissibleNext [63, 60, 48, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_9 :
    searchIndexLists 6 233 2520 63 [63, 60, 54, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 1).flatMap (fun d =>
      if admissibleNext [63, 60, 54, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 233 * d - 2520
        let rawDen := 2520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 60, 54, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 1).filter
        (admissibleNext [63, 60, 54, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_10 :
    searchIndexLists 6 67 720 60 [60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 4).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 67 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 4).filter
        (admissibleNext [60, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [63] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_11 :
    searchIndexLists 6 473 5040 63 [63, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 64 0).flatMap (fun d =>
      if admissibleNext [63, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 473 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [63, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 64 0).filter
        (admissibleNext [63, 54, 48, 45, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_12 :
    searchIndexLists 6 47 480 40 [40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 41 21).flatMap (fun d =>
      if admissibleNext [40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 41 21).filter
        (admissibleNext [40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [42, 48, 54, 56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_13 :
    searchIndexLists 6 111 1120 42 [42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 18).flatMap (fun d =>
      if admissibleNext [42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 111 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 18).filter
        (admissibleNext [42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48, 54, 56, 60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_14 :
    searchIndexLists 6 49 480 48 [48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 10).flatMap (fun d =>
      if admissibleNext [48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 10).filter
        (admissibleNext [48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_15 :
    searchIndexLists 6 451 4320 54 [54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 3).flatMap (fun d =>
      if admissibleNext [54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 451 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 3).filter
        (admissibleNext [54, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_16 :
    searchIndexLists 6 353 3360 56 [56, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 1).flatMap (fun d =>
      if admissibleNext [56, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 353 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [56, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 1).filter
        (admissibleNext [56, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_17 :
    searchIndexLists 6 1027 10080 42 [42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 16).flatMap (fun d =>
      if admissibleNext [42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1027 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 16).filter
        (admissibleNext [42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48, 54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_18 :
    searchIndexLists 6 151 1440 48 [48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 9).flatMap (fun d =>
      if admissibleNext [48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 151 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 9).filter
        (admissibleNext [48, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_19 :
    searchIndexLists 6 463 4320 54 [54, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 1).flatMap (fun d =>
      if admissibleNext [54, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 463 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [54, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 1).filter
        (admissibleNext [54, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_20 :
    searchIndexLists 6 1069 10080 48 [48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 8).flatMap (fun d =>
      if admissibleNext [48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1069 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 8).filter
        (admissibleNext [48, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_21 :
    searchIndexLists 6 3277 30240 54 [54, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 1).flatMap (fun d =>
      if admissibleNext [54, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3277 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [54, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 1).filter
        (admissibleNext [54, 42, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_22 :
    searchIndexLists 6 59 560 42 [42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 14).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 59 * d - 560
        let rawDen := 560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 14).filter
        (admissibleNext [42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [48, 54, 56] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_23 :
    searchIndexLists 6 13 120 48 [48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 7).flatMap (fun d =>
      if admissibleNext [48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 7).filter
        (admissibleNext [48, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_24 :
    searchIndexLists 6 239 2160 54 [54, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 55 0).flatMap (fun d =>
      if admissibleNext [54, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 239 * d - 2160
        let rawDen := 2160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [54, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 0).filter
        (admissibleNext [54, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_25 :
    searchIndexLists 6 23 210 48 [48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 6).flatMap (fun d =>
      if admissibleNext [48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 210
        let rawDen := 210 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 6).filter
        (admissibleNext [48, 42, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_26 :
    searchIndexLists 6 283 2520 48 [48, 42, 40, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 5).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 283 * d - 2520
        let rawDen := 2520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 5).filter
        (admissibleNext [48, 42, 40, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_27 :
    searchIndexLists 6 361 3360 42 [42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 13).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 361 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 13).filter
        (admissibleNext [42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [48, 54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_28 :
    searchIndexLists 6 53 480 48 [48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 6).flatMap (fun d =>
      if admissibleNext [48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 53 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 6).filter
        (admissibleNext [48, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [54] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_29 :
    searchIndexLists 6 25 224 48 [48, 42, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 5).flatMap (fun d =>
      if admissibleNext [48, 42, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 25 * d - 224
        let rawDen := 224 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 5).filter
        (admissibleNext [48, 42, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_30 :
    searchIndexLists 6 1153 10080 48 [48, 42, 40, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 4).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1153 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 4).filter
        (admissibleNext [48, 42, 40, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_31 :
    searchIndexLists 6 33 280 48 [48, 42, 40, 36, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 36, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 33 * d - 280
        let rawDen := 280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 36, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 42, 40, 36, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_32 :
    searchIndexLists 6 389 3360 42 [42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 9).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 389 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 9).filter
        (admissibleNext [42, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [48] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_33 :
    searchIndexLists 6 19 160 48 [48, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 40, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_34 :
    searchIndexLists 6 403 3360 48 [48, 42, 36, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 2).flatMap (fun d =>
      if admissibleNext [48, 42, 36, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 403 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 36, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 2).filter
        (admissibleNext [48, 42, 36, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_35 :
    searchIndexLists 6 1237 10080 48 [48, 42, 40, 32, 30, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 49 0).flatMap (fun d =>
      if admissibleNext [48, 42, 40, 32, 30, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1237 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [48, 42, 40, 32, 30, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 49 0).filter
        (admissibleNext [48, 42, 40, 32, 30, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_36 :
    searchIndexLists 6 1307 10080 42 [42, 40, 36, 32, 30, 24, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 4).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 30, 24, 16, 12, 8, 6, 4] d then
        let rawNum := 1307 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 30, 24, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 4).filter
        (admissibleNext [42, 40, 36, 32, 30, 24, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD11_37 :
    searchIndexLists 6 153 1120 42 [42, 40, 36, 32, 30, 24, 18, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 43 1).flatMap (fun d =>
      if admissibleNext [42, 40, 36, 32, 30, 24, 18, 12, 8, 6, 4] d then
        let rawNum := 153 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 5 (rawNum / common) (rawDen / common) d
          (d :: [42, 40, 36, 32, 30, 24, 18, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 43 1).filter
        (admissibleNext [42, 40, 36, 32, 30, 24, 18, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
