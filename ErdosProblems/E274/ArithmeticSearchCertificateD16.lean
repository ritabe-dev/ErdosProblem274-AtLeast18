import ErdosProblems.E274.ArithmeticSearchCertificateD17

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_0 :
    searchIndexLists 1 73 6480 84 [84, 81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [84, 81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 73 * d - 6480
        let rawDen := 6480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [84, 81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_1 :
    searchIndexLists 1 1 4320 60 [60, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]] := by
  rw [searchIndexLists]
  change
    (List.range' 4320 1).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 4320 1).filter
        (admissibleNext [60, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [4320] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_2 :
    searchIndexLists 1 11 8640 64 [64, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 786 0).flatMap (fun d =>
      if admissibleNext [64, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 786 0).filter
        (admissibleNext [64, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_3 :
    searchIndexLists 1 83 47520 66 [66, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 573 0).flatMap (fun d =>
      if admissibleNext [66, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 83 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 573 0).filter
        (admissibleNext [66, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_4 :
    searchIndexLists 1 13 4320 72 [72, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 333 0).flatMap (fun d =>
      if admissibleNext [72, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 333 0).filter
        (admissibleNext [72, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_5 :
    searchIndexLists 1 229 56160 78 [78, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 246 0).flatMap (fun d =>
      if admissibleNext [78, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 229 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 246 0).filter
        (admissibleNext [78, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_6 :
    searchIndexLists 1 19 4320 80 [80, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 228 0).flatMap (fun d =>
      if admissibleNext [80, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 228 0).filter
        (admissibleNext [80, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_7 :
    searchIndexLists 1 151 30240 84 [84, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 201 0).flatMap (fun d =>
      if admissibleNext [84, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 151 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 201 0).filter
        (admissibleNext [84, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_8 :
    searchIndexLists 1 263 47520 88 [88, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 181 0).flatMap (fun d =>
      if admissibleNext [88, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 263 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 181 0).filter
        (admissibleNext [88, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_9 :
    searchIndexLists 1 5 864 90 [90, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 173 0).flatMap (fun d =>
      if admissibleNext [90, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 5 * d - 864
        let rawDen := 864 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 173 0).filter
        (admissibleNext [90, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_10 :
    searchIndexLists 1 7 1080 96 [96, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 155 0).flatMap (fun d =>
      if admissibleNext [96, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 1080
        let rawDen := 1080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 155 0).filter
        (admissibleNext [96, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_11 :
    searchIndexLists 1 521 73440 102 [102, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 141 0).flatMap (fun d =>
      if admissibleNext [102, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 521 * d - 73440
        let rawDen := 73440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [102, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 141 0).filter
        (admissibleNext [102, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_12 :
    searchIndexLists 1 409 56160 104 [104, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 138 0).flatMap (fun d =>
      if admissibleNext [104, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 409 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [104, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 138 0).filter
        (admissibleNext [104, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_13 :
    searchIndexLists 1 11 1440 108 [108, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 131 0).flatMap (fun d =>
      if admissibleNext [108, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [108, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 131 0).filter
        (admissibleNext [108, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_14 :
    searchIndexLists 1 241 30240 112 [112, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 126 0).flatMap (fun d =>
      if admissibleNext [112, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 241 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [112, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 126 0).filter
        (admissibleNext [112, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_15 :
    searchIndexLists 1 667 82080 114 [114, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 124 0).flatMap (fun d =>
      if admissibleNext [114, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 667 * d - 82080
        let rawDen := 82080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [114, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 124 0).filter
        (admissibleNext [114, 56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_16 :
    searchIndexLists 1 149 60480 64 [64, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 406 0).flatMap (fun d =>
      if admissibleNext [64, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 149 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 406 0).filter
        (admissibleNext [64, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_17 :
    searchIndexLists 1 977 332640 66 [66, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 341 0).flatMap (fun d =>
      if admissibleNext [66, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 977 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 341 0).filter
        (admissibleNext [66, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_18 :
    searchIndexLists 1 127 30240 72 [72, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 239 0).flatMap (fun d =>
      if admissibleNext [72, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 127 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 239 0).filter
        (admissibleNext [72, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_19 :
    searchIndexLists 1 2071 393120 78 [78, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 190 0).flatMap (fun d =>
      if admissibleNext [78, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2071 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 190 0).filter
        (admissibleNext [78, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_20 :
    searchIndexLists 1 169 30240 80 [80, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 179 0).flatMap (fun d =>
      if admissibleNext [80, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 169 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 179 0).filter
        (admissibleNext [80, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_21 :
    searchIndexLists 1 187 30240 84 [84, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 162 0).flatMap (fun d =>
      if admissibleNext [84, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 187 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 162 0).filter
        (admissibleNext [84, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_22 :
    searchIndexLists 1 2237 332640 88 [88, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 149 0).flatMap (fun d =>
      if admissibleNext [88, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2237 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 149 0).filter
        (admissibleNext [88, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_23 :
    searchIndexLists 1 211 30240 90 [90, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 144 0).flatMap (fun d =>
      if admissibleNext [90, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 211 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 144 0).filter
        (admissibleNext [90, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_24 :
    searchIndexLists 1 29 3780 96 [96, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 131 0).flatMap (fun d =>
      if admissibleNext [96, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 3780
        let rawDen := 3780 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 131 0).filter
        (admissibleNext [96, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_25 :
    searchIndexLists 1 4259 514080 102 [102, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 121 0).flatMap (fun d =>
      if admissibleNext [102, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 4259 * d - 514080
        let rawDen := 514080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [102, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 121 0).filter
        (admissibleNext [102, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_26 :
    searchIndexLists 1 3331 393120 104 [104, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 119 0).flatMap (fun d =>
      if admissibleNext [104, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3331 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [104, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 119 0).filter
        (admissibleNext [104, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_27 :
    searchIndexLists 1 89 10080 108 [108, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 114 0).flatMap (fun d =>
      if admissibleNext [108, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 89 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [108, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 114 0).filter
        (admissibleNext [108, 60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_28 :
    searchIndexLists 1 2647 665280 66 [66, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 252 0).flatMap (fun d =>
      if admissibleNext [66, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2647 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 252 0).filter
        (admissibleNext [66, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_29 :
    searchIndexLists 1 317 60480 72 [72, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 191 0).flatMap (fun d =>
      if admissibleNext [72, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 317 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 191 0).filter
        (admissibleNext [72, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_30 :
    searchIndexLists 1 4961 786240 78 [78, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 159 0).flatMap (fun d =>
      if admissibleNext [78, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 4961 * d - 786240
        let rawDen := 786240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 159 0).filter
        (admissibleNext [78, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_31 :
    searchIndexLists 1 401 60480 80 [80, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 151 0).flatMap (fun d =>
      if admissibleNext [80, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 401 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 151 0).filter
        (admissibleNext [80, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_32 :
    searchIndexLists 1 437 60480 84 [84, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 139 0).flatMap (fun d =>
      if admissibleNext [84, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 437 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 139 0).filter
        (admissibleNext [84, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_33 :
    searchIndexLists 1 5167 665280 88 [88, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 129 0).flatMap (fun d =>
      if admissibleNext [88, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 5167 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 129 0).filter
        (admissibleNext [88, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_34 :
    searchIndexLists 1 97 12096 90 [90, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 125 0).flatMap (fun d =>
      if admissibleNext [90, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 97 * d - 12096
        let rawDen := 12096 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 125 0).filter
        (admissibleNext [90, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_35 :
    searchIndexLists 1 527 60480 96 [96, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 115 0).flatMap (fun d =>
      if admissibleNext [96, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 527 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 115 0).filter
        (admissibleNext [96, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_36 :
    searchIndexLists 1 9589 1028160 102 [102, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 108 0).flatMap (fun d =>
      if admissibleNext [102, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9589 * d - 1028160
        let rawDen := 1028160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [102, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 108 0).filter
        (admissibleNext [102, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_37 :
    searchIndexLists 1 7481 786240 104 [104, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 106 0).flatMap (fun d =>
      if admissibleNext [104, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7481 * d - 786240
        let rawDen := 786240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [104, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 106 0).filter
        (admissibleNext [104, 64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_38 :
    searchIndexLists 1 1901 332640 72 [72, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 175 0).flatMap (fun d =>
      if admissibleNext [72, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1901 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 175 0).filter
        (admissibleNext [72, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_39 :
    searchIndexLists 1 29333 4324320 78 [78, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 148 0).flatMap (fun d =>
      if admissibleNext [78, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29333 * d - 4324320
        let rawDen := 4324320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 148 0).filter
        (admissibleNext [78, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_40 :
    searchIndexLists 1 2363 332640 80 [80, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 141 0).flatMap (fun d =>
      if admissibleNext [80, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2363 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 141 0).filter
        (admissibleNext [80, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_41 :
    searchIndexLists 1 2561 332640 84 [84, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 130 0).flatMap (fun d =>
      if admissibleNext [84, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2561 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 130 0).filter
        (admissibleNext [84, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_42 :
    searchIndexLists 1 2741 332640 88 [88, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 122 0).flatMap (fun d =>
      if admissibleNext [88, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2741 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 122 0).filter
        (admissibleNext [88, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_43 :
    searchIndexLists 1 565 66528 90 [90, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 118 0).flatMap (fun d =>
      if admissibleNext [90, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 565 * d - 66528
        let rawDen := 66528 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 118 0).filter
        (admissibleNext [90, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_44 :
    searchIndexLists 1 191 20790 96 [96, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 109 0).flatMap (fun d =>
      if admissibleNext [96, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 191 * d - 20790
        let rawDen := 20790 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 109 0).filter
        (admissibleNext [96, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_45 :
    searchIndexLists 1 55417 5654880 102 [102, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 103 0).flatMap (fun d =>
      if admissibleNext [102, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 55417 * d - 5654880
        let rawDen := 5654880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [102, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 103 0).filter
        (admissibleNext [102, 66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_46 :
    searchIndexLists 1 3163 393120 78 [78, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 125 0).flatMap (fun d =>
      if admissibleNext [78, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3163 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 125 0).filter
        (admissibleNext [78, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_47 :
    searchIndexLists 1 253 30240 80 [80, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 120 0).flatMap (fun d =>
      if admissibleNext [80, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 253 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 120 0).filter
        (admissibleNext [80, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_48 :
    searchIndexLists 1 271 30240 84 [84, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 112 0).flatMap (fun d =>
      if admissibleNext [84, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 271 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 112 0).filter
        (admissibleNext [84, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_49 :
    searchIndexLists 1 3161 332640 88 [88, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 106 0).flatMap (fun d =>
      if admissibleNext [88, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3161 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 106 0).filter
        (admissibleNext [88, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_50 :
    searchIndexLists 1 59 6048 90 [90, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 103 0).flatMap (fun d =>
      if admissibleNext [90, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 59 * d - 6048
        let rawDen := 6048 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 103 0).filter
        (admissibleNext [90, 72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_51 :
    searchIndexLists 1 3709 393120 80 [80, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 106 0).flatMap (fun d =>
      if admissibleNext [80, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3709 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 106 0).filter
        (admissibleNext [80, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_52 :
    searchIndexLists 1 3943 393120 84 [84, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 100 0).flatMap (fun d =>
      if admissibleNext [84, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3943 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 100 0).filter
        (admissibleNext [84, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_53 :
    searchIndexLists 1 45713 4324320 88 [88, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 95 0).flatMap (fun d =>
      if admissibleNext [88, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 45713 * d - 4324320
        let rawDen := 4324320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 95 0).filter
        (admissibleNext [88, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_54 :
    searchIndexLists 1 851 78624 90 [90, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 93 0).flatMap (fun d =>
      if admissibleNext [90, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 851 * d - 78624
        let rawDen := 78624 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 93 0).filter
        (admissibleNext [90, 78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_55 :
    searchIndexLists 1 313 30240 84 [84, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 97 0).flatMap (fun d =>
      if admissibleNext [84, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 313 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 97 0).filter
        (admissibleNext [84, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_56 :
    searchIndexLists 1 3623 332640 88 [88, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 92 0).flatMap (fun d =>
      if admissibleNext [88, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3623 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 92 0).filter
        (admissibleNext [88, 80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_57 :
    searchIndexLists 1 1 320 64 [64, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]] := by
  rw [searchIndexLists]
  change
    (List.range' 320 1).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 320
        let rawDen := 320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 320 1).filter
        (admissibleNext [64, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [320] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_58 :
    searchIndexLists 1 19 5280 66 [66, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 278 0).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 278 0).filter
        (admissibleNext [66, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_59 :
    searchIndexLists 1 7 1440 72 [72, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 206 0).flatMap (fun d =>
      if admissibleNext [72, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 206 0).filter
        (admissibleNext [72, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_60 :
    searchIndexLists 1 37 6240 78 [78, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 169 0).flatMap (fun d =>
      if admissibleNext [78, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 6240
        let rawDen := 6240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 169 0).filter
        (admissibleNext [78, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_61 :
    searchIndexLists 1 1 160 80 [80, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]] := by
  rw [searchIndexLists]
  change
    (List.range' 160 1).flatMap (fun d =>
      if admissibleNext [80, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 160 1).filter
        (admissibleNext [80, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [160] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_62 :
    searchIndexLists 1 23 3360 84 [84, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 147 0).flatMap (fun d =>
      if admissibleNext [84, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 147 0).filter
        (admissibleNext [84, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_63 :
    searchIndexLists 1 13 1760 88 [88, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 136 0).flatMap (fun d =>
      if admissibleNext [88, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 1760
        let rawDen := 1760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 136 0).filter
        (admissibleNext [88, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_64 :
    searchIndexLists 1 11 1440 90 [90, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 131 0).flatMap (fun d =>
      if admissibleNext [90, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 131 0).filter
        (admissibleNext [90, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_65 :
    searchIndexLists 1 1 120 96 [96, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]] := by
  rw [searchIndexLists]
  change
    (List.range' 120 1).flatMap (fun d =>
      if admissibleNext [96, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 120
        let rawDen := 120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 120 1).filter
        (admissibleNext [96, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [120] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_66 :
    searchIndexLists 1 73 8160 102 [102, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 112 0).flatMap (fun d =>
      if admissibleNext [102, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 73 * d - 8160
        let rawDen := 8160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [102, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 112 0).filter
        (admissibleNext [102, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_67 :
    searchIndexLists 1 19 2080 104 [104, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 110 0).flatMap (fun d =>
      if admissibleNext [104, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 2080
        let rawDen := 2080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [104, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 110 0).filter
        (admissibleNext [104, 60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_68 :
    searchIndexLists 1 49 10560 66 [66, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 216 0).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 10560
        let rawDen := 10560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 216 0).filter
        (admissibleNext [66, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_69 :
    searchIndexLists 1 17 2880 72 [72, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 170 0).flatMap (fun d =>
      if admissibleNext [72, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 17 * d - 2880
        let rawDen := 2880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 170 0).filter
        (admissibleNext [72, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_70 :
    searchIndexLists 1 29 4160 78 [78, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 144 0).flatMap (fun d =>
      if admissibleNext [78, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 4160
        let rawDen := 4160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 144 0).filter
        (admissibleNext [78, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_71 :
    searchIndexLists 1 7 960 80 [80, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 138 0).flatMap (fun d =>
      if admissibleNext [80, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 138 0).filter
        (admissibleNext [80, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_72 :
    searchIndexLists 1 53 6720 84 [84, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 127 0).flatMap (fun d =>
      if admissibleNext [84, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 53 * d - 6720
        let rawDen := 6720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 127 0).filter
        (admissibleNext [84, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_73 :
    searchIndexLists 1 89 10560 88 [88, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 119 0).flatMap (fun d =>
      if admissibleNext [88, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 89 * d - 10560
        let rawDen := 10560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 119 0).filter
        (admissibleNext [88, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_74 :
    searchIndexLists 1 5 576 90 [90, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 116 0).flatMap (fun d =>
      if admissibleNext [90, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 5 * d - 576
        let rawDen := 576 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 116 0).filter
        (admissibleNext [90, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_75 :
    searchIndexLists 1 3 320 96 [96, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 107 0).flatMap (fun d =>
      if admissibleNext [96, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3 * d - 320
        let rawDen := 320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 107 0).filter
        (admissibleNext [96, 64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_76 :
    searchIndexLists 1 101 15840 72 [72, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 157 0).flatMap (fun d =>
      if admissibleNext [72, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 101 * d - 15840
        let rawDen := 15840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 157 0).filter
        (admissibleNext [72, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_77 :
    searchIndexLists 1 511 68640 78 [78, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 135 0).flatMap (fun d =>
      if admissibleNext [78, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 511 * d - 68640
        let rawDen := 68640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 135 0).filter
        (admissibleNext [78, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_78 :
    searchIndexLists 1 41 5280 80 [80, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 129 0).flatMap (fun d =>
      if admissibleNext [80, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 41 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 129 0).filter
        (admissibleNext [80, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_79 :
    searchIndexLists 1 103 12320 84 [84, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 120 0).flatMap (fun d =>
      if admissibleNext [84, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 103 * d - 12320
        let rawDen := 12320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 120 0).filter
        (admissibleNext [84, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_80 :
    searchIndexLists 1 47 5280 88 [88, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 113 0).flatMap (fun d =>
      if admissibleNext [88, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 113 0).filter
        (admissibleNext [88, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_81 :
    searchIndexLists 1 29 3168 90 [90, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 110 0).flatMap (fun d =>
      if admissibleNext [90, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 3168
        let rawDen := 3168 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 110 0).filter
        (admissibleNext [90, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_82 :
    searchIndexLists 1 13 1320 96 [96, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 102 0).flatMap (fun d =>
      if admissibleNext [96, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 1320
        let rawDen := 1320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [96, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 102 0).filter
        (admissibleNext [96, 66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_83 :
    searchIndexLists 1 163 18720 78 [78, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 115 0).flatMap (fun d =>
      if admissibleNext [78, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 163 * d - 18720
        let rawDen := 18720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 115 0).filter
        (admissibleNext [78, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_84 :
    searchIndexLists 1 13 1440 80 [80, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 111 0).flatMap (fun d =>
      if admissibleNext [80, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 13 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 111 0).filter
        (admissibleNext [80, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_85 :
    searchIndexLists 1 97 10080 84 [84, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 104 0).flatMap (fun d =>
      if admissibleNext [84, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 97 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 104 0).filter
        (admissibleNext [84, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_86 :
    searchIndexLists 1 161 15840 88 [88, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 99 0).flatMap (fun d =>
      if admissibleNext [88, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 161 * d - 15840
        let rawDen := 15840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 99 0).filter
        (admissibleNext [88, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_87 :
    searchIndexLists 1 1 96 90 [90, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 96 1).flatMap (fun d =>
      if admissibleNext [90, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1 * d - 96
        let rawDen := 96 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 96 1).filter
        (admissibleNext [90, 72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [96] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_88 :
    searchIndexLists 1 21 2080 80 [80, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 100 0).flatMap (fun d =>
      if admissibleNext [80, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 21 * d - 2080
        let rawDen := 2080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 100 0).filter
        (admissibleNext [80, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_89 :
    searchIndexLists 1 467 43680 84 [84, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 94 0).flatMap (fun d =>
      if admissibleNext [84, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 467 * d - 43680
        let rawDen := 43680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 94 0).filter
        (admissibleNext [84, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_90 :
    searchIndexLists 1 257 22880 88 [88, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [88, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 257 * d - 22880
        let rawDen := 22880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [88, 78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_91 :
    searchIndexLists 1 37 3360 84 [84, 80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 91 0).flatMap (fun d =>
      if admissibleNext [84, 80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 91 0).filter
        (admissibleNext [84, 80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_92 :
    searchIndexLists 1 431 73920 66 [66, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 172 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 431 * d - 73920
        let rawDen := 73920 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 172 0).filter
        (admissibleNext [66, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_93 :
    searchIndexLists 1 143 20160 72 [72, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 141 0).flatMap (fun d =>
      if admissibleNext [72, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 143 * d - 20160
        let rawDen := 20160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 141 0).filter
        (admissibleNext [72, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_94 :
    searchIndexLists 1 713 87360 78 [78, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 123 0).flatMap (fun d =>
      if admissibleNext [78, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 713 * d - 87360
        let rawDen := 87360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 123 0).filter
        (admissibleNext [78, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_95 :
    searchIndexLists 1 19 2240 80 [80, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 118 0).flatMap (fun d =>
      if admissibleNext [80, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 2240
        let rawDen := 2240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 118 0).filter
        (admissibleNext [80, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_96 :
    searchIndexLists 1 61 6720 84 [84, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 111 0).flatMap (fun d =>
      if admissibleNext [84, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 61 * d - 6720
        let rawDen := 6720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 111 0).filter
        (admissibleNext [84, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_97 :
    searchIndexLists 1 237 24640 88 [88, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 104 0).flatMap (fun d =>
      if admissibleNext [88, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 237 * d - 24640
        let rawDen := 24640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 104 0).filter
        (admissibleNext [88, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_98 :
    searchIndexLists 1 199 20160 90 [90, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 102 0).flatMap (fun d =>
      if admissibleNext [90, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 199 * d - 20160
        let rawDen := 20160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 102 0).filter
        (admissibleNext [90, 64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_99 :
    searchIndexLists 1 839 110880 72 [72, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 133 0).flatMap (fun d =>
      if admissibleNext [72, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 839 * d - 110880
        let rawDen := 110880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 133 0).filter
        (admissibleNext [72, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_100 :
    searchIndexLists 1 1383 160160 78 [78, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 116 0).flatMap (fun d =>
      if admissibleNext [78, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1383 * d - 160160
        let rawDen := 160160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 116 0).filter
        (admissibleNext [78, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_101 :
    searchIndexLists 1 331 36960 80 [80, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 112 0).flatMap (fun d =>
      if admissibleNext [80, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 331 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 112 0).filter
        (admissibleNext [80, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_102 :
    searchIndexLists 1 353 36960 84 [84, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 105 0).flatMap (fun d =>
      if admissibleNext [84, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 353 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 105 0).filter
        (admissibleNext [84, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_103 :
    searchIndexLists 1 373 36960 88 [88, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 100 0).flatMap (fun d =>
      if admissibleNext [88, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 373 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 100 0).filter
        (admissibleNext [88, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_104 :
    searchIndexLists 1 1147 110880 90 [90, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 97 0).flatMap (fun d =>
      if admissibleNext [90, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1147 * d - 110880
        let rawDen := 110880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 97 0).filter
        (admissibleNext [90, 66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_105 :
    searchIndexLists 1 1297 131040 78 [78, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 102 0).flatMap (fun d =>
      if admissibleNext [78, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1297 * d - 131040
        let rawDen := 131040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 102 0).filter
        (admissibleNext [78, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_106 :
    searchIndexLists 1 103 10080 80 [80, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 98 0).flatMap (fun d =>
      if admissibleNext [80, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 103 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 98 0).filter
        (admissibleNext [80, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_107 :
    searchIndexLists 1 109 10080 84 [84, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 93 0).flatMap (fun d =>
      if admissibleNext [84, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 109 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 93 0).filter
        (admissibleNext [84, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_108 :
    searchIndexLists 1 1259 110880 88 [88, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [88, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1259 * d - 110880
        let rawDen := 110880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [88, 72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_109 :
    searchIndexLists 1 493 43680 80 [80, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [80, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 493 * d - 43680
        let rawDen := 43680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [80, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_110 :
    searchIndexLists 1 173 14560 84 [84, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 0).flatMap (fun d =>
      if admissibleNext [84, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 173 * d - 14560
        let rawDen := 14560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 0).filter
        (admissibleNext [84, 78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_111 :
    searchIndexLists 1 1909 221760 72 [72, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 117 0).flatMap (fun d =>
      if admissibleNext [72, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1909 * d - 221760
        let rawDen := 221760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 117 0).filter
        (admissibleNext [72, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_112 :
    searchIndexLists 1 9299 960960 78 [78, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 104 0).flatMap (fun d =>
      if admissibleNext [78, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9299 * d - 960960
        let rawDen := 960960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 104 0).filter
        (admissibleNext [78, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_113 :
    searchIndexLists 1 739 73920 80 [80, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 101 0).flatMap (fun d =>
      if admissibleNext [80, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 739 * d - 73920
        let rawDen := 73920 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 101 0).filter
        (admissibleNext [80, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_114 :
    searchIndexLists 1 261 24640 84 [84, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 95 0).flatMap (fun d =>
      if admissibleNext [84, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 261 * d - 24640
        let rawDen := 24640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 95 0).filter
        (admissibleNext [84, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_115 :
    searchIndexLists 1 823 73920 88 [88, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [88, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 823 * d - 73920
        let rawDen := 73920 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [88, 66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_116 :
    searchIndexLists 1 2867 262080 78 [78, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 92 0).flatMap (fun d =>
      if admissibleNext [78, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2867 * d - 262080
        let rawDen := 262080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 92 0).filter
        (admissibleNext [78, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_117 :
    searchIndexLists 1 227 20160 80 [80, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [80, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 227 * d - 20160
        let rawDen := 20160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [80, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_118 :
    searchIndexLists 1 239 20160 84 [84, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 0).flatMap (fun d =>
      if admissibleNext [84, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 239 * d - 20160
        let rawDen := 20160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 0).filter
        (admissibleNext [84, 72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_119 :
    searchIndexLists 1 359 29120 80 [80, 78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 82 0).flatMap (fun d =>
      if admissibleNext [80, 78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 359 * d - 29120
        let rawDen := 29120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 82 0).filter
        (admissibleNext [80, 78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_120 :
    searchIndexLists 1 16451 1441440 78 [78, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 88 0).flatMap (fun d =>
      if admissibleNext [78, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 16451 * d - 1441440
        let rawDen := 1441440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 88 0).filter
        (admissibleNext [78, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_121 :
    searchIndexLists 1 1301 110880 80 [80, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 86 0).flatMap (fun d =>
      if admissibleNext [80, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1301 * d - 110880
        let rawDen := 110880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 86 0).filter
        (admissibleNext [80, 72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_122 :
    searchIndexLists 1 47 8640 64 [64, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 184 0).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 184 0).filter
        (admissibleNext [64, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_123 :
    searchIndexLists 1 281 47520 66 [66, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 170 0).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 281 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 170 0).filter
        (admissibleNext [66, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_124 :
    searchIndexLists 1 31 4320 72 [72, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 140 0).flatMap (fun d =>
      if admissibleNext [72, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 140 0).filter
        (admissibleNext [72, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_125 :
    searchIndexLists 1 463 56160 78 [78, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 122 0).flatMap (fun d =>
      if admissibleNext [78, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 463 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 122 0).filter
        (admissibleNext [78, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_126 :
    searchIndexLists 1 37 4320 80 [80, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 117 0).flatMap (fun d =>
      if admissibleNext [80, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 117 0).filter
        (admissibleNext [80, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_127 :
    searchIndexLists 1 277 30240 84 [84, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 110 0).flatMap (fun d =>
      if admissibleNext [84, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 277 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 110 0).filter
        (admissibleNext [84, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_128 :
    searchIndexLists 1 461 47520 88 [88, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 104 0).flatMap (fun d =>
      if admissibleNext [88, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 461 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 104 0).filter
        (admissibleNext [88, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_129 :
    searchIndexLists 1 43 4320 90 [90, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 101 0).flatMap (fun d =>
      if admissibleNext [90, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 43 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 101 0).filter
        (admissibleNext [90, 60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_130 :
    searchIndexLists 1 661 95040 66 [66, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 144 0).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 661 * d - 95040
        let rawDen := 95040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 144 0).filter
        (admissibleNext [66, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_131 :
    searchIndexLists 1 71 8640 72 [72, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 122 0).flatMap (fun d =>
      if admissibleNext [72, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 71 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 122 0).filter
        (admissibleNext [72, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_132 :
    searchIndexLists 1 1043 112320 78 [78, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 108 0).flatMap (fun d =>
      if admissibleNext [78, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1043 * d - 112320
        let rawDen := 112320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 108 0).filter
        (admissibleNext [78, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_133 :
    searchIndexLists 1 83 8640 80 [80, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 105 0).flatMap (fun d =>
      if admissibleNext [80, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 83 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 105 0).filter
        (admissibleNext [80, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_134 :
    searchIndexLists 1 617 60480 84 [84, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 99 0).flatMap (fun d =>
      if admissibleNext [84, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 617 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 99 0).filter
        (admissibleNext [84, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_135 :
    searchIndexLists 1 1021 95040 88 [88, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 94 0).flatMap (fun d =>
      if admissibleNext [88, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1021 * d - 95040
        let rawDen := 95040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 94 0).filter
        (admissibleNext [88, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_136 :
    searchIndexLists 1 19 1728 90 [90, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 91 0).flatMap (fun d =>
      if admissibleNext [90, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 1728
        let rawDen := 1728 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [90, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 91 0).filter
        (admissibleNext [90, 64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_137 :
    searchIndexLists 1 413 47520 72 [72, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 116 0).flatMap (fun d =>
      if admissibleNext [72, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 413 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 116 0).filter
        (admissibleNext [72, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_138 :
    searchIndexLists 1 6029 617760 78 [78, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 103 0).flatMap (fun d =>
      if admissibleNext [78, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 6029 * d - 617760
        let rawDen := 617760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 103 0).filter
        (admissibleNext [78, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_139 :
    searchIndexLists 1 479 47520 80 [80, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 100 0).flatMap (fun d =>
      if admissibleNext [80, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 479 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 100 0).filter
        (admissibleNext [80, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_140 :
    searchIndexLists 1 3551 332640 84 [84, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 94 0).flatMap (fun d =>
      if admissibleNext [84, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3551 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 94 0).filter
        (admissibleNext [84, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_141 :
    searchIndexLists 1 533 47520 88 [88, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [88, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 533 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [88, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [88, 66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_142 :
    searchIndexLists 1 619 56160 78 [78, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 91 0).flatMap (fun d =>
      if admissibleNext [78, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 619 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 91 0).filter
        (admissibleNext [78, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_143 :
    searchIndexLists 1 49 4320 80 [80, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [80, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [80, 72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_144 :
    searchIndexLists 1 697 56160 80 [80, 78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 0).flatMap (fun d =>
      if admissibleNext [80, 78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 697 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 0).filter
        (admissibleNext [80, 78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_145 :
    searchIndexLists 1 5419 665280 66 [66, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 123 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 5419 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 123 0).filter
        (admissibleNext [66, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_146 :
    searchIndexLists 1 569 60480 72 [72, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 107 0).flatMap (fun d =>
      if admissibleNext [72, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 569 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 107 0).filter
        (admissibleNext [72, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_147 :
    searchIndexLists 1 8237 786240 78 [78, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 96 0).flatMap (fun d =>
      if admissibleNext [78, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 8237 * d - 786240
        let rawDen := 786240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 96 0).filter
        (admissibleNext [78, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_148 :
    searchIndexLists 1 653 60480 80 [80, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 93 0).flatMap (fun d =>
      if admissibleNext [80, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 653 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 93 0).filter
        (admissibleNext [80, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_149 :
    searchIndexLists 1 689 60480 84 [84, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 88 0).flatMap (fun d =>
      if admissibleNext [84, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 689 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 88 0).filter
        (admissibleNext [84, 64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_150 :
    searchIndexLists 1 3287 332640 72 [72, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 102 0).flatMap (fun d =>
      if admissibleNext [72, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3287 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 102 0).filter
        (admissibleNext [72, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_151 :
    searchIndexLists 1 47351 4324320 78 [78, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 92 0).flatMap (fun d =>
      if admissibleNext [78, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47351 * d - 4324320
        let rawDen := 4324320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 92 0).filter
        (admissibleNext [78, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_152 :
    searchIndexLists 1 3749 332640 80 [80, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [80, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3749 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [80, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_153 :
    searchIndexLists 1 3947 332640 84 [84, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 0).flatMap (fun d =>
      if admissibleNext [84, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3947 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [84, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 0).filter
        (admissibleNext [84, 66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_154 :
    searchIndexLists 1 4801 393120 78 [78, 72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 82 0).flatMap (fun d =>
      if admissibleNext [78, 72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 4801 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 82 0).filter
        (admissibleNext [78, 72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_155 :
    searchIndexLists 1 7267 665280 72 [72, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 92 0).flatMap (fun d =>
      if admissibleNext [72, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7267 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 92 0).filter
        (admissibleNext [72, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_156 :
    searchIndexLists 1 103711 8648640 78 [78, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 84 0).flatMap (fun d =>
      if admissibleNext [78, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 103711 * d - 8648640
        let rawDen := 8648640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 84 0).filter
        (admissibleNext [78, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_157 :
    searchIndexLists 1 8191 665280 80 [80, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 82 0).flatMap (fun d =>
      if admissibleNext [80, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 8191 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 82 0).filter
        (admissibleNext [80, 66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_158 :
    searchIndexLists 1 31 3520 66 [66, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 114 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 3520
        let rawDen := 3520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 114 0).filter
        (admissibleNext [66, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_159 :
    searchIndexLists 1 29 2880 72 [72, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 100 0).flatMap (fun d =>
      if admissibleNext [72, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 29 * d - 2880
        let rawDen := 2880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 100 0).filter
        (admissibleNext [72, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_160 :
    searchIndexLists 1 139 12480 78 [78, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [78, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 139 * d - 12480
        let rawDen := 12480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [78, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_161 :
    searchIndexLists 1 11 960 80 [80, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 88 0).flatMap (fun d =>
      if admissibleNext [80, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 88 0).filter
        (admissibleNext [80, 64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_162 :
    searchIndexLists 1 167 15840 72 [72, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 95 0).flatMap (fun d =>
      if admissibleNext [72, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 167 * d - 15840
        let rawDen := 15840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 95 0).filter
        (admissibleNext [72, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_163 :
    searchIndexLists 1 797 68640 78 [78, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 87 0).flatMap (fun d =>
      if admissibleNext [78, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 797 * d - 68640
        let rawDen := 68640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 87 0).filter
        (admissibleNext [78, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_164 :
    searchIndexLists 1 21 1760 80 [80, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 84 0).flatMap (fun d =>
      if admissibleNext [80, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 21 * d - 1760
        let rawDen := 1760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 84 0).filter
        (admissibleNext [80, 66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_165 :
    searchIndexLists 1 367 31680 72 [72, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 87 0).flatMap (fun d =>
      if admissibleNext [72, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 367 * d - 31680
        let rawDen := 31680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 87 0).filter
        (admissibleNext [72, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_166 :
    searchIndexLists 1 579 45760 78 [78, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 80 0).flatMap (fun d =>
      if admissibleNext [78, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 579 * d - 45760
        let rawDen := 45760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 80 0).filter
        (admissibleNext [78, 66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_167 :
    searchIndexLists 1 2833 221760 72 [72, 66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 0).flatMap (fun d =>
      if admissibleNext [72, 66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2833 * d - 221760
        let rawDen := 221760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 0).filter
        (admissibleNext [72, 66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_168 :
    searchIndexLists 1 509 60480 64 [64, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 119 0).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 509 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 119 0).filter
        (admissibleNext [64, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_169 :
    searchIndexLists 1 2957 332640 66 [66, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 113 0).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2957 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 113 0).filter
        (admissibleNext [66, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_170 :
    searchIndexLists 1 307 30240 72 [72, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 99 0).flatMap (fun d =>
      if admissibleNext [72, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 307 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 99 0).filter
        (admissibleNext [72, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_171 :
    searchIndexLists 1 4411 393120 78 [78, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [78, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 4411 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [78, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_172 :
    searchIndexLists 1 349 30240 80 [80, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 87 0).flatMap (fun d =>
      if admissibleNext [80, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 349 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [80, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 87 0).filter
        (admissibleNext [80, 60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_173 :
    searchIndexLists 1 6607 665280 66 [66, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 101 0).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 6607 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 101 0).filter
        (admissibleNext [66, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_174 :
    searchIndexLists 1 677 60480 72 [72, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [72, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 677 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [72, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_175 :
    searchIndexLists 1 9641 786240 78 [78, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 82 0).flatMap (fun d =>
      if admissibleNext [78, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9641 * d - 786240
        let rawDen := 786240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 82 0).filter
        (admissibleNext [78, 64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_176 :
    searchIndexLists 1 3881 332640 72 [72, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 86 0).flatMap (fun d =>
      if admissibleNext [72, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3881 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 86 0).filter
        (admissibleNext [72, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_177 :
    searchIndexLists 1 55073 4324320 78 [78, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 0).flatMap (fun d =>
      if admissibleNext [78, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 55073 * d - 4324320
        let rawDen := 4324320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 0).filter
        (admissibleNext [78, 66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_178 :
    searchIndexLists 1 1057 95040 66 [66, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1057 * d - 95040
        let rawDen := 95040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [66, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_179 :
    searchIndexLists 1 107 8640 72 [72, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 0).flatMap (fun d =>
      if admissibleNext [72, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 107 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 0).filter
        (admissibleNext [72, 64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_180 :
    searchIndexLists 1 611 47520 72 [72, 66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 78 0).flatMap (fun d =>
      if admissibleNext [72, 66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 611 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 78 0).filter
        (admissibleNext [72, 66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_181 :
    searchIndexLists 1 871 73920 66 [66, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 871 * d - 73920
        let rawDen := 73920 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 0).filter
        (admissibleNext [66, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_182 :
    searchIndexLists 1 263 20160 72 [72, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 77 0).flatMap (fun d =>
      if admissibleNext [72, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 263 * d - 20160
        let rawDen := 20160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 77 0).filter
        (admissibleNext [72, 64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_183 :
    searchIndexLists 1 1499 110880 72 [72, 66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 74 0).flatMap (fun d =>
      if admissibleNext [72, 66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1499 * d - 110880
        let rawDen := 110880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 74 0).filter
        (admissibleNext [72, 66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_184 :
    searchIndexLists 1 9379 665280 66 [66, 64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 71 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9379 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 71 0).filter
        (admissibleNext [66, 64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_185 :
    searchIndexLists 1 83 8640 64 [64, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 105 0).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 83 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 105 0).filter
        (admissibleNext [64, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_186 :
    searchIndexLists 1 479 47520 66 [66, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 100 0).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 479 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 100 0).filter
        (admissibleNext [66, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_187 :
    searchIndexLists 1 49 4320 72 [72, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 89 0).flatMap (fun d =>
      if admissibleNext [72, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 49 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 89 0).filter
        (admissibleNext [72, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_188 :
    searchIndexLists 1 697 56160 78 [78, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 0).flatMap (fun d =>
      if admissibleNext [78, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 697 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [78, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 0).filter
        (admissibleNext [78, 60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_189 :
    searchIndexLists 1 1057 95040 66 [66, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 90 0).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1057 * d - 95040
        let rawDen := 95040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 90 0).filter
        (admissibleNext [66, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_190 :
    searchIndexLists 1 107 8640 72 [72, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 0).flatMap (fun d =>
      if admissibleNext [72, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 107 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 0).filter
        (admissibleNext [72, 64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_191 :
    searchIndexLists 1 611 47520 72 [72, 66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 78 0).flatMap (fun d =>
      if admissibleNext [72, 66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 611 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 78 0).filter
        (admissibleNext [72, 66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_192 :
    searchIndexLists 1 8191 665280 66 [66, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 82 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 8191 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 82 0).filter
        (admissibleNext [66, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_193 :
    searchIndexLists 1 821 60480 72 [72, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 74 0).flatMap (fun d =>
      if admissibleNext [72, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 821 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 74 0).filter
        (admissibleNext [72, 64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_194 :
    searchIndexLists 1 137 10560 66 [66, 64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 78 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 137 * d - 10560
        let rawDen := 10560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 78 0).filter
        (admissibleNext [66, 64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_195 :
    searchIndexLists 1 107 8640 64 [64, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 0).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 107 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 0).filter
        (admissibleNext [64, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_196 :
    searchIndexLists 1 611 47520 66 [66, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 78 0).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 611 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 78 0).filter
        (admissibleNext [66, 60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_197 :
    searchIndexLists 1 1321 95040 66 [66, 64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 72 0).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1321 * d - 95040
        let rawDen := 95040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 72 0).filter
        (admissibleNext [66, 64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD16_198 :
    searchIndexLists 1 10039 665280 66 [66, 64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 0).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 10039 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 0 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 0).filter
        (admissibleNext [66, 64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
