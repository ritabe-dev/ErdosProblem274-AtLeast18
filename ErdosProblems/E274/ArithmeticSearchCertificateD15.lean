import ErdosProblems.E274.ArithmeticSearchCertificateD16

/-! Kernel-reducible branch certificate for the exact E274 length-seventeen arithmetic search. -/

namespace ErdosProblems.E274

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_0 :
    searchIndexLists 2 1051 45360 81 [81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 82 5).flatMap (fun d =>
      if admissibleNext [81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 1051 * d - 45360
        let rawDen := 45360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 82 5).filter
        (admissibleNext [81, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_1 :
    searchIndexLists 2 17 720 84 [84, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 0).flatMap (fun d =>
      if admissibleNext [84, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3] d then
        let rawNum := 17 * d - 720
        let rawDen := 720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [84, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 0).filter
        (admissibleNext [84, 72, 63, 60, 54, 48, 45, 36, 27, 24, 18, 12, 9, 6, 3]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_2 :
    searchIndexLists 2 73 4320 56 [56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]] := by
  rw [searchIndexLists]
  change
    (List.range' 60 59).flatMap (fun d =>
      if admissibleNext [56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 73 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 60 59).filter
        (admissibleNext [56, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [60, 64, 66, 72, 78, 80, 84, 88, 90, 96, 102, 104, 108, 112, 114] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_3 :
    searchIndexLists 2 547 30240 60 [60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 50).flatMap (fun d =>
      if admissibleNext [60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 547 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 50).filter
        (admissibleNext [60, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72, 78, 80, 84, 88, 90, 96, 102, 104, 108] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_4 :
    searchIndexLists 2 1157 60480 64 [64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 40).flatMap (fun d =>
      if admissibleNext [64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1157 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 40).filter
        (admissibleNext [64, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78, 80, 84, 88, 90, 96, 102, 104] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_5 :
    searchIndexLists 2 6521 332640 66 [66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 36).flatMap (fun d =>
      if admissibleNext [66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 6521 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 36).filter
        (admissibleNext [66, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80, 84, 88, 90, 96, 102] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_6 :
    searchIndexLists 2 631 30240 72 [72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 23).flatMap (fun d =>
      if admissibleNext [72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 631 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 23).filter
        (admissibleNext [72, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78, 80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_7 :
    searchIndexLists 2 8623 393120 78 [78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 13).flatMap (fun d =>
      if admissibleNext [78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 8623 * d - 393120
        let rawDen := 393120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 13).filter
        (admissibleNext [78, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_8 :
    searchIndexLists 2 673 30240 80 [80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 9).flatMap (fun d =>
      if admissibleNext [80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 673 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 9).filter
        (admissibleNext [80, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [84, 88] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_9 :
    searchIndexLists 2 691 30240 84 [84, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 3).flatMap (fun d =>
      if admissibleNext [84, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 691 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [84, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 3).filter
        (admissibleNext [84, 54, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_10 :
    searchIndexLists 2 3 160 60 [60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]] := by
  rw [searchIndexLists]
  change
    (List.range' 61 46).flatMap (fun d =>
      if admissibleNext [60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 3 * d - 160
        let rawDen := 160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160], [4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 46).filter
        (admissibleNext [60, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72, 78, 80, 84, 88, 90, 96, 102, 104] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_11 :
    searchIndexLists 2 19 960 64 [64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 37).flatMap (fun d =>
      if admissibleNext [64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 37).filter
        (admissibleNext [64, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78, 80, 84, 88, 90, 96] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_12 :
    searchIndexLists 2 107 5280 66 [66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 32).flatMap (fun d =>
      if admissibleNext [66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 107 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 32).filter
        (admissibleNext [66, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80, 84, 88, 90, 96] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_13 :
    searchIndexLists 2 31 1440 72 [72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]] := by
  rw [searchIndexLists]
  change
    (List.range' 73 20).flatMap (fun d =>
      if admissibleNext [72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 31 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = [[4, 6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]]
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 20).filter
        (admissibleNext [72, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78, 80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_14 :
    searchIndexLists 2 47 2080 78 [78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 10).flatMap (fun d =>
      if admissibleNext [78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 2080
        let rawDen := 2080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 10).filter
        (admissibleNext [78, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [80, 84, 88] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_15 :
    searchIndexLists 2 11 480 80 [80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 7).flatMap (fun d =>
      if admissibleNext [80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 11 * d - 480
        let rawDen := 480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 7).filter
        (admissibleNext [80, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_16 :
    searchIndexLists 2 79 3360 84 [84, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 85 1).flatMap (fun d =>
      if admissibleNext [84, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 79 * d - 3360
        let rawDen := 3360 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [84, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 85 1).filter
        (admissibleNext [84, 56, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_17 :
    searchIndexLists 2 47 2240 64 [64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 31).flatMap (fun d =>
      if admissibleNext [64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 47 * d - 2240
        let rawDen := 2240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 31).filter
        (admissibleNext [64, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78, 80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_18 :
    searchIndexLists 2 793 36960 66 [66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 27).flatMap (fun d =>
      if admissibleNext [66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 793 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 27).filter
        (admissibleNext [66, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_19 :
    searchIndexLists 2 229 10080 72 [72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 16).flatMap (fun d =>
      if admissibleNext [72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 229 * d - 10080
        let rawDen := 10080 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 16).filter
        (admissibleNext [72, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78, 80, 84, 88] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_20 :
    searchIndexLists 2 1039 43680 78 [78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 6).flatMap (fun d =>
      if admissibleNext [78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1039 * d - 43680
        let rawDen := 43680 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 6).filter
        (admissibleNext [78, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [80, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_21 :
    searchIndexLists 2 27 1120 80 [80, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 81 2).flatMap (fun d =>
      if admissibleNext [80, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 27 * d - 1120
        let rawDen := 1120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [80, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 81 2).filter
        (admissibleNext [80, 60, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_22 :
    searchIndexLists 2 1663 73920 66 [66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 22).flatMap (fun d =>
      if admissibleNext [66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1663 * d - 73920
        let rawDen := 73920 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 22).filter
        (admissibleNext [66, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80, 84, 88] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_23 :
    searchIndexLists 2 479 20160 72 [72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 12).flatMap (fun d =>
      if admissibleNext [72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 479 * d - 20160
        let rawDen := 20160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 12).filter
        (admissibleNext [72, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78, 80, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_24 :
    searchIndexLists 2 723 29120 78 [78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 2).flatMap (fun d =>
      if admissibleNext [78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 723 * d - 29120
        let rawDen := 29120 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 2).filter
        (admissibleNext [78, 64, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_25 :
    searchIndexLists 2 2687 110880 72 [72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 10).flatMap (fun d =>
      if admissibleNext [72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2687 * d - 110880
        let rawDen := 110880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 10).filter
        (admissibleNext [72, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_26 :
    searchIndexLists 2 12157 480480 78 [78, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 1).flatMap (fun d =>
      if admissibleNext [78, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 12157 * d - 480480
        let rawDen := 480480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [78, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 1).filter
        (admissibleNext [78, 66, 48, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_27 :
    searchIndexLists 2 91 4320 60 [60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 34).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 91 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 34).filter
        (admissibleNext [60, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72, 78, 80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_28 :
    searchIndexLists 2 191 8640 64 [64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 26).flatMap (fun d =>
      if admissibleNext [64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 191 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 26).filter
        (admissibleNext [64, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78, 80, 84, 88, 90] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_29 :
    searchIndexLists 2 1073 47520 66 [66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 22).flatMap (fun d =>
      if admissibleNext [66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1073 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 22).filter
        (admissibleNext [66, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80, 84, 88] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_30 :
    searchIndexLists 2 103 4320 72 [72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 11).flatMap (fun d =>
      if admissibleNext [72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 103 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 11).filter
        (admissibleNext [72, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_31 :
    searchIndexLists 2 1399 56160 78 [78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 79 2).flatMap (fun d =>
      if admissibleNext [78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1399 * d - 56160
        let rawDen := 56160 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 79 2).filter
        (admissibleNext [78, 56, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_32 :
    searchIndexLists 2 1409 60480 64 [64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 21).flatMap (fun d =>
      if admissibleNext [64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1409 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 21).filter
        (admissibleNext [64, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78, 80, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_33 :
    searchIndexLists 2 7907 332640 66 [66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 18).flatMap (fun d =>
      if admissibleNext [66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 7907 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 18).filter
        (admissibleNext [66, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80, 84] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_34 :
    searchIndexLists 2 757 30240 72 [72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 7).flatMap (fun d =>
      if admissibleNext [72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 757 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 7).filter
        (admissibleNext [72, 60, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_35 :
    searchIndexLists 2 16507 665280 66 [66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 14).flatMap (fun d =>
      if admissibleNext [66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 16507 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 14).filter
        (admissibleNext [66, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_36 :
    searchIndexLists 2 1577 60480 72 [72, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 4).flatMap (fun d =>
      if admissibleNext [72, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1577 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 4).filter
        (admissibleNext [72, 64, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_37 :
    searchIndexLists 2 8831 332640 72 [72, 66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 3).flatMap (fun d =>
      if admissibleNext [72, 66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 8831 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 3).filter
        (admissibleNext [72, 66, 54, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_38 :
    searchIndexLists 2 23 960 64 [64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 19).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 23 * d - 960
        let rawDen := 960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 19).filter
        (admissibleNext [64, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_39 :
    searchIndexLists 2 43 1760 66 [66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 15).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 43 * d - 1760
        let rawDen := 1760 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 15).filter
        (admissibleNext [66, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_40 :
    searchIndexLists 2 37 1440 72 [72, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 5).flatMap (fun d =>
      if admissibleNext [72, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 37 * d - 1440
        let rawDen := 1440 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 5).filter
        (admissibleNext [72, 60, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_41 :
    searchIndexLists 2 269 10560 66 [66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 12).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 269 * d - 10560
        let rawDen := 10560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 12).filter
        (admissibleNext [66, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_42 :
    searchIndexLists 2 77 2880 72 [72, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 2).flatMap (fun d =>
      if admissibleNext [72, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 77 * d - 2880
        let rawDen := 2880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 2).filter
        (admissibleNext [72, 64, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_43 :
    searchIndexLists 2 431 15840 72 [72, 66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 1).flatMap (fun d =>
      if admissibleNext [72, 66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 431 * d - 15840
        let rawDen := 15840 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 1).filter
        (admissibleNext [72, 66, 56, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_44 :
    searchIndexLists 2 657 24640 66 [66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 9).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 657 * d - 24640
        let rawDen := 24640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 9).filter
        (admissibleNext [66, 64, 60, 42, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_45 :
    searchIndexLists 2 727 30240 60 [60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 23).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 727 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 23).filter
        (admissibleNext [60, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72, 78, 80] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_46 :
    searchIndexLists 2 1517 60480 64 [64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 15).flatMap (fun d =>
      if admissibleNext [64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1517 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 15).filter
        (admissibleNext [64, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_47 :
    searchIndexLists 2 8501 332640 66 [66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 12).flatMap (fun d =>
      if admissibleNext [66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 8501 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 12).filter
        (admissibleNext [66, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_48 :
    searchIndexLists 2 811 30240 72 [72, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 73 2).flatMap (fun d =>
      if admissibleNext [72, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 811 * d - 30240
        let rawDen := 30240 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [72, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 73 2).filter
        (admissibleNext [72, 56, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_49 :
    searchIndexLists 2 227 8640 64 [64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 12).flatMap (fun d =>
      if admissibleNext [64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 227 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 12).filter
        (admissibleNext [64, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_50 :
    searchIndexLists 2 1271 47520 66 [66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 8).flatMap (fun d =>
      if admissibleNext [66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1271 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 8).filter
        (admissibleNext [66, 60, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_51 :
    searchIndexLists 2 2641 95040 66 [66, 64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 5).flatMap (fun d =>
      if admissibleNext [66, 64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 2641 * d - 95040
        let rawDen := 95040 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 5).filter
        (admissibleNext [66, 64, 54, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_52 :
    searchIndexLists 2 181 6720 64 [64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 10).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 181 * d - 6720
        let rawDen := 6720 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 10).filter
        (admissibleNext [64, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_53 :
    searchIndexLists 2 1013 36960 66 [66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 6).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1013 * d - 36960
        let rawDen := 36960 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 6).filter
        (admissibleNext [66, 60, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_54 :
    searchIndexLists 2 701 24640 66 [66, 64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 4).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 701 * d - 24640
        let rawDen := 24640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 4).filter
        (admissibleNext [66, 64, 56, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_55 :
    searchIndexLists 2 313 10560 66 [66, 64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 1).flatMap (fun d =>
      if admissibleNext [66, 64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 313 * d - 10560
        let rawDen := 10560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 1).filter
        (admissibleNext [66, 64, 60, 48, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_56 :
    searchIndexLists 2 1769 60480 64 [64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 4).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1769 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 4).filter
        (admissibleNext [64, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_57 :
    searchIndexLists 2 9887 332640 66 [66, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 1).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9887 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 1).filter
        (admissibleNext [66, 60, 56, 54, 40, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_58 :
    searchIndexLists 2 109 4320 60 [60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 19).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 109 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 19).filter
        (admissibleNext [60, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66, 72, 78] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_59 :
    searchIndexLists 2 227 8640 64 [64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 12).flatMap (fun d =>
      if admissibleNext [64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 227 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 12).filter
        (admissibleNext [64, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_60 :
    searchIndexLists 2 1271 47520 66 [66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 8).flatMap (fun d =>
      if admissibleNext [66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1271 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 8).filter
        (admissibleNext [66, 56, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_61 :
    searchIndexLists 2 1661 60480 64 [64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 8).flatMap (fun d =>
      if admissibleNext [64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1661 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 8).filter
        (admissibleNext [64, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66, 72] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_62 :
    searchIndexLists 2 9293 332640 66 [66, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 5).flatMap (fun d =>
      if admissibleNext [66, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9293 * d - 332640
        let rawDen := 332640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 5).filter
        (admissibleNext [66, 60, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_63 :
    searchIndexLists 2 19279 665280 66 [66, 64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 3).flatMap (fun d =>
      if admissibleNext [66, 64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 19279 * d - 665280
        let rawDen := 665280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 3).filter
        (admissibleNext [66, 64, 54, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_64 :
    searchIndexLists 2 9 320 64 [64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 7).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 9 * d - 320
        let rawDen := 320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 7).filter
        (admissibleNext [64, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_65 :
    searchIndexLists 2 151 5280 66 [66, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 3).flatMap (fun d =>
      if admissibleNext [66, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 151 * d - 5280
        let rawDen := 5280 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 3).filter
        (admissibleNext [66, 60, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_66 :
    searchIndexLists 2 313 10560 66 [66, 64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 1).flatMap (fun d =>
      if admissibleNext [66, 64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 313 * d - 10560
        let rawDen := 10560 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 1).filter
        (admissibleNext [66, 64, 56, 48, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_67 :
    searchIndexLists 2 263 8640 64 [64, 60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 1).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 263 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 1).filter
        (admissibleNext [64, 60, 56, 54, 42, 36, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_68 :
    searchIndexLists 2 121 4320 60 [60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 11).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 121 * d - 4320
        let rawDen := 4320 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 11).filter
        (admissibleNext [60, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [64, 66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_69 :
    searchIndexLists 2 251 8640 64 [64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 4).flatMap (fun d =>
      if admissibleNext [64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 251 * d - 8640
        let rawDen := 8640 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 4).filter
        (admissibleNext [64, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_70 :
    searchIndexLists 2 1403 47520 66 [66, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 67 1).flatMap (fun d =>
      if admissibleNext [66, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1403 * d - 47520
        let rawDen := 47520 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [66, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 67 1).filter
        (admissibleNext [66, 56, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_71 :
    searchIndexLists 2 1829 60480 64 [64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 2).flatMap (fun d =>
      if admissibleNext [64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 1829 * d - 60480
        let rawDen := 60480 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 2).filter
        (admissibleNext [64, 60, 54, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [66] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_72 :
    searchIndexLists 2 89 2880 64 [64, 60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 65 0).flatMap (fun d =>
      if admissibleNext [64, 60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 89 * d - 2880
        let rawDen := 2880 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [64, 60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 65 0).filter
        (admissibleNext [64, 60, 56, 48, 42, 40, 32, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
@[simp] theorem arithmeticCertD15_73 :
    searchIndexLists 2 17 540 60 [60, 56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] =
      [] := by
  rw [searchIndexLists]
  change
    (List.range' 61 3).flatMap (fun d =>
      if admissibleNext [60, 56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4] d then
        let rawNum := 17 * d - 540
        let rawDen := 540 * d
        let common := Nat.gcd rawNum rawDen
        searchIndexLists 1 (rawNum / common) (rawDen / common) d
          (d :: [60, 56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4])
      else []) = []
  rw [flatMap_if_eq_filter_flatMap]
  have hfilter :
      (List.range' 61 3).filter
        (admissibleNext [60, 56, 54, 48, 42, 40, 36, 30, 24, 18, 16, 12, 8, 6, 4]) =
        [] := by
    decide +kernel
  rw [hfilter]
  norm_num

end ErdosProblems.E274
