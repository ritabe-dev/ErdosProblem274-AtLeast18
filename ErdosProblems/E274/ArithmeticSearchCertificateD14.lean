import ErdosProblems.E274.ArithmeticSearchCertificateD15

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_0 :
    searchIndexLists 3 179 5040 72 [72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 12).flatMap (fun d =>
      if admissibleNext [72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 179 * d - 5040
        let rawDen := 5040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 12).filter
        (admissibleNext [72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [81, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_1 :
    searchIndexLists 3 1051 30240 54 [54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]] := by
  rw [searchIndexLists]
  change
    (List.range' 55 32).flatMap (fun d =>
      if admissibleNext [54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1051 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 55 32).filter
        (admissibleNext [54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [56, 60, 64, 66, 72, 78, 80, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_2 :
    searchIndexLists 3 17 480 56 [56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 57 28).flatMap (fun d =>
      if admissibleNext [56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 17 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 28).filter
        (admissibleNext [56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66, 72, 78, 80, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_3 :
    searchIndexLists 3 41 1120 60 [60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 21).flatMap (fun d =>
      if admissibleNext [60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 41 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 21).filter
        (admissibleNext [60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72, 78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_4 :
    searchIndexLists 3 253 6720 64 [64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 15).flatMap (fun d =>
      if admissibleNext [64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 253 * d - 6720
        let rawDen := 6720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 15).filter
        (admissibleNext [64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_5 :
    searchIndexLists 3 1409 36960 66 [66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 12).flatMap (fun d =>
      if admissibleNext [66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1409 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 12).filter
        (admissibleNext [66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_6 :
    searchIndexLists 3 397 10080 72 [72, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 4).flatMap (fun d =>
      if admissibleNext [72, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 397 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [72, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 4).filter
        (admissibleNext [72, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_7 :
    searchIndexLists 3 163 4320 56 [56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 23).flatMap (fun d =>
      if admissibleNext [56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 163 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 23).filter
        (admissibleNext [56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66, 72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_8 :
    searchIndexLists 3 1177 30240 60 [60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 17).flatMap (fun d =>
      if admissibleNext [60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1177 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 17).filter
        (admissibleNext [60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_9 :
    searchIndexLists 3 2417 60480 64 [64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 11).flatMap (fun d =>
      if admissibleNext [64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2417 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 11).filter
        (admissibleNext [64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_10 :
    searchIndexLists 3 13451 332640 66 [66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 8).flatMap (fun d =>
      if admissibleNext [66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13451 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 8).filter
        (admissibleNext [66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_11 :
    searchIndexLists 3 19 480 60 [60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 15).flatMap (fun d =>
      if admissibleNext [60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 15).filter
        (admissibleNext [60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_12 :
    searchIndexLists 3 13 320 64 [64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 9).flatMap (fun d =>
      if admissibleNext [64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 320
        let rawDen := 320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 9).filter
        (admissibleNext [64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_13 :
    searchIndexLists 3 217 5280 66 [66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 6).flatMap (fun d =>
      if admissibleNext [66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 217 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 6).filter
        (admissibleNext [66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_14 :
    searchIndexLists 3 281 6720 64 [64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 7).flatMap (fun d =>
      if admissibleNext [64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 281 * d - 6720
        let rawDen := 6720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 7).filter
        (admissibleNext [64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_15 :
    searchIndexLists 3 521 12320 66 [66, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 4).flatMap (fun d =>
      if admissibleNext [66, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 521 * d - 12320
        let rawDen := 12320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 4).filter
        (admissibleNext [66, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_16 :
    searchIndexLists 3 3203 73920 66 [66, 64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 3).flatMap (fun d =>
      if admissibleNext [66, 64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3203 * d - 73920
        let rawDen := 73920 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 3).filter
        (admissibleNext [66, 64, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_17 :
    searchIndexLists 3 1231 30240 56 [56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 17).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1231 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 17).filter
        (admissibleNext [56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_18 :
    searchIndexLists 3 181 4320 60 [60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 11).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 181 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 11).filter
        (admissibleNext [60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_19 :
    searchIndexLists 3 371 8640 64 [64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 5).flatMap (fun d =>
      if admissibleNext [64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 371 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 5).filter
        (admissibleNext [64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_20 :
    searchIndexLists 3 2063 47520 66 [66, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 3).flatMap (fun d =>
      if admissibleNext [66, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2063 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 3).filter
        (admissibleNext [66, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_21 :
    searchIndexLists 3 143 3360 60 [60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 10).flatMap (fun d =>
      if admissibleNext [60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 143 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 10).filter
        (admissibleNext [60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_22 :
    searchIndexLists 3 293 6720 64 [64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 4).flatMap (fun d =>
      if admissibleNext [64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 293 * d - 6720
        let rawDen := 6720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 4).filter
        (admissibleNext [64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_23 :
    searchIndexLists 3 543 12320 66 [66, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 2).flatMap (fun d =>
      if admissibleNext [66, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 543 * d - 12320
        let rawDen := 12320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 2).filter
        (admissibleNext [66, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_24 :
    searchIndexLists 3 43 960 64 [64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 2).flatMap (fun d =>
      if admissibleNext [64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 43 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 2).filter
        (admissibleNext [64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_25 :
    searchIndexLists 3 239 5280 66 [66, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 0).flatMap (fun d =>
      if admissibleNext [66, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 239 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 0).filter
        (admissibleNext [66, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_26 :
    searchIndexLists 3 1357 30240 60 [60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 6).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1357 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 6).filter
        (admissibleNext [60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_27 :
    searchIndexLists 3 2777 60480 64 [64, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 1).flatMap (fun d =>
      if admissibleNext [64, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2777 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 1).filter
        (admissibleNext [64, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_28 :
    searchIndexLists 3 181 4320 56 [56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 15).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 181 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 15).filter
        (admissibleNext [56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_29 :
    searchIndexLists 3 1303 30240 60 [60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 9).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1303 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 9).filter
        (admissibleNext [60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_30 :
    searchIndexLists 3 2669 60480 64 [64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 3).flatMap (fun d =>
      if admissibleNext [64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2669 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 3).filter
        (admissibleNext [64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_31 :
    searchIndexLists 3 14837 332640 66 [66, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 1).flatMap (fun d =>
      if admissibleNext [66, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 14837 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 1).filter
        (admissibleNext [66, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_32 :
    searchIndexLists 3 7 160 60 [60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 8).flatMap (fun d =>
      if admissibleNext [60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 8).filter
        (admissibleNext [60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_33 :
    searchIndexLists 3 43 960 64 [64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 2).flatMap (fun d =>
      if admissibleNext [64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 43 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 2).filter
        (admissibleNext [64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_34 :
    searchIndexLists 3 239 5280 66 [66, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 0).flatMap (fun d =>
      if admissibleNext [66, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 239 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 0).filter
        (admissibleNext [66, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_35 :
    searchIndexLists 3 103 2240 64 [64, 60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 1).flatMap (fun d =>
      if admissibleNext [64, 60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 103 * d - 2240
        let rawDen := 2240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 1).filter
        (admissibleNext [64, 60, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_36 :
    searchIndexLists 3 199 4320 60 [60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 5).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 199 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 5).filter
        (admissibleNext [60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_37 :
    searchIndexLists 3 1483 30240 60 [60, 56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 1).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1483 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 1).filter
        (admissibleNext [60, 56, 54, 48, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_38 :
    searchIndexLists 3 193 4320 56 [56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 11).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 193 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 11).filter
        (admissibleNext [56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_39 :
    searchIndexLists 3 1387 30240 60 [60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 5).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1387 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 5).filter
        (admissibleNext [60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_40 :
    searchIndexLists 3 67 1440 60 [60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 4).flatMap (fun d =>
      if admissibleNext [60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 67 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 4).filter
        (admissibleNext [60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_41 :
    searchIndexLists 3 211 4320 60 [60, 56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 1).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 211 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 1).filter
        (admissibleNext [60, 56, 54, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_42 :
    searchIndexLists 3 13 270 56 [56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 6).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 270
        let rawDen := 270 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 6).filter
        (admissibleNext [56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_43 :
    searchIndexLists 3 373 7560 60 [60, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 0).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 373 * d - 7560
        let rawDen := 7560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 0).filter
        (admissibleNext [60, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_44 :
    searchIndexLists 3 1 20 60 [60, 56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 0).flatMap (fun d =>
      if admissibleNext [60, 56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 20
        let rawDen := 20 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 0).filter
        (admissibleNext [60, 56, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD14_45 :
    searchIndexLists 3 217 4320 56 [56, 54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 57 3).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 217 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 2 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 57 3).filter
        (admissibleNext [56, 54, 48, 42, 40, 36, 32, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
