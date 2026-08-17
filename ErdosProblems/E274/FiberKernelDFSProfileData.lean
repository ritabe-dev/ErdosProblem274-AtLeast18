import ErdosProblems.E274.FiberKernelDFSCore

/-! Generated fixed data for the five E274 fiber certificates. -/

namespace ErdosProblems.E274

def fiberProfile1Rows : List Nat := [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 54, 56, 60, 4320]
def fiberProfile1Scale : Nat := 45360

def fiberProfile2Rows : List Nat := [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 64, 320]
def fiberProfile2Scale : Nat := 30240

def fiberProfile3Rows : List Nat := [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 80, 160]
def fiberProfile3Scale : Nat := 15120

def fiberProfile4Rows : List Nat := [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 60, 96, 120]
def fiberProfile4Scale : Nat := 15120

def fiberProfile5Rows : List Nat := [6, 8, 12, 16, 18, 24, 30, 32, 36, 40, 42, 48, 56, 72, 90, 96]
def fiberProfile5Scale : Nat := 15120

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_6 :
    kernelFiberChoices4 6 = [(3, 3), (5, 3), (6, 3)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_8 :
    kernelFiberChoices4 8 = [(1, 2), (2, 2), (3, 4), (4, 2), (5, 4), (6, 4), (7, 6)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_12 :
    kernelFiberChoices4 12 = [(1, 3), (2, 3), (3, 6), (4, 3), (5, 6), (6, 6), (7, 9)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_16 :
    kernelFiberChoices4 16 = [(1, 4), (2, 4), (3, 8), (4, 4), (5, 8), (6, 8), (7, 12)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_18 :
    kernelFiberChoices4 18 = [(3, 9), (5, 9), (6, 9)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_24 :
    kernelFiberChoices4 24 = [(1, 6), (2, 6), (3, 12), (4, 6), (5, 12), (6, 12), (7, 18)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_30 :
    kernelFiberChoices4 30 = [(3, 15), (5, 15), (6, 15)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_32 :
    kernelFiberChoices4 32 = [(1, 8), (2, 8), (3, 16), (4, 8), (5, 16), (6, 16), (7, 24)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_36 :
    kernelFiberChoices4 36 = [(1, 9), (2, 9), (3, 18), (4, 9), (5, 18), (6, 18), (7, 27)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_40 :
    kernelFiberChoices4 40 = [(1, 10), (2, 10), (3, 20), (4, 10), (5, 20), (6, 20), (7, 30)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_42 :
    kernelFiberChoices4 42 = [(3, 21), (5, 21), (6, 21)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_48 :
    kernelFiberChoices4 48 = [(1, 12), (2, 12), (3, 24), (4, 12), (5, 24), (6, 24), (7, 36)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_54 :
    kernelFiberChoices4 54 = [(3, 27), (5, 27), (6, 27)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_56 :
    kernelFiberChoices4 56 = [(1, 14), (2, 14), (3, 28), (4, 14), (5, 28), (6, 28), (7, 42)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_60 :
    kernelFiberChoices4 60 = [(1, 15), (2, 15), (3, 30), (4, 15), (5, 30), (6, 30), (7, 45)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_64 :
    kernelFiberChoices4 64 = [(1, 16), (2, 16), (3, 32), (4, 16), (5, 32), (6, 32), (7, 48)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_72 :
    kernelFiberChoices4 72 = [(1, 18), (2, 18), (3, 36), (4, 18), (5, 36), (6, 36), (7, 54)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_80 :
    kernelFiberChoices4 80 = [(1, 20), (2, 20), (3, 40), (4, 20), (5, 40), (6, 40), (7, 60)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_90 :
    kernelFiberChoices4 90 = [(3, 45), (5, 45), (6, 45)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_96 :
    kernelFiberChoices4 96 = [(1, 24), (2, 24), (3, 48), (4, 24), (5, 48), (6, 48), (7, 72)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_120 :
    kernelFiberChoices4 120 = [(1, 30), (2, 30), (3, 60), (4, 30), (5, 60), (6, 60), (7, 90)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_160 :
    kernelFiberChoices4 160 = [(1, 40), (2, 40), (3, 80), (4, 40), (5, 80), (6, 80), (7, 120)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_320 :
    kernelFiberChoices4 320 = [(1, 80), (2, 80), (3, 160), (4, 80), (5, 160), (6, 160), (7, 240)] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kernelFiberChoices4_4320 :
    kernelFiberChoices4 4320 = [(1, 1080), (2, 1080), (3, 2160), (4, 1080), (5, 2160), (6, 2160), (7, 3240)] := by
  decide +kernel

@[simp] theorem kernelTestBit_1_0 :
    Nat.testBit 1 0 = true := by
  decide

@[simp] theorem kernelTestBit_1_1 :
    Nat.testBit 1 1 = false := by
  decide

@[simp] theorem kernelTestBit_1_2 :
    Nat.testBit 1 2 = false := by
  decide

@[simp] theorem kernelTestBit_2_0 :
    Nat.testBit 2 0 = false := by
  decide

@[simp] theorem kernelTestBit_2_1 :
    Nat.testBit 2 1 = true := by
  decide

@[simp] theorem kernelTestBit_2_2 :
    Nat.testBit 2 2 = false := by
  decide

@[simp] theorem kernelTestBit_3_0 :
    Nat.testBit 3 0 = true := by
  decide

@[simp] theorem kernelTestBit_3_1 :
    Nat.testBit 3 1 = true := by
  decide

@[simp] theorem kernelTestBit_3_2 :
    Nat.testBit 3 2 = false := by
  decide

@[simp] theorem kernelTestBit_4_0 :
    Nat.testBit 4 0 = false := by
  decide

@[simp] theorem kernelTestBit_4_1 :
    Nat.testBit 4 1 = false := by
  decide

@[simp] theorem kernelTestBit_4_2 :
    Nat.testBit 4 2 = true := by
  decide

@[simp] theorem kernelTestBit_5_0 :
    Nat.testBit 5 0 = true := by
  decide

@[simp] theorem kernelTestBit_5_1 :
    Nat.testBit 5 1 = false := by
  decide

@[simp] theorem kernelTestBit_5_2 :
    Nat.testBit 5 2 = true := by
  decide

@[simp] theorem kernelTestBit_6_0 :
    Nat.testBit 6 0 = false := by
  decide

@[simp] theorem kernelTestBit_6_1 :
    Nat.testBit 6 1 = true := by
  decide

@[simp] theorem kernelTestBit_6_2 :
    Nat.testBit 6 2 = true := by
  decide

@[simp] theorem kernelTestBit_7_0 :
    Nat.testBit 7 0 = true := by
  decide

@[simp] theorem kernelTestBit_7_1 :
    Nat.testBit 7 1 = true := by
  decide

@[simp] theorem kernelTestBit_7_2 :
    Nat.testBit 7 2 = true := by
  decide

end ErdosProblems.E274
