/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Qatlib.Papers.GroverAES15.GroverLedger

def TightRounding (m e : ℕ) (x : ℚ) : Prop :=
  (((2 * m : ℕ) - 1 : ℕ) : ℚ) / 200 * 2 ^ e ≤ x ∧
    x < (((2 * m : ℕ) + 1 : ℕ) : ℚ) / 200 * 2 ^ e

structure QuotedParams where
  keyBits : ℕ
  s : ℕ
  t : ℕ
  c : ℕ
  tDepth : ℕ
  totalDepth : ℕ
  boxes : ℕ
  ctrlT : ℕ
deriving DecidableEq, Repr

def aes128 : QuotedParams :=
  ⟨128, 984, 1060864, 1380420, 50688, 110799, 3, 13204⟩

def aes192 : QuotedParams :=
  ⟨192, 1112, 1204224, 1567296, 44352, 96956, 4, 17812⟩

def aes256 : QuotedParams :=
  ⟨256, 1336, 1505280, 1956099, 59904, 130929, 5, 22420⟩

def quotedIters128 : ℕ := 14488038916154245684

def quotedIters192 : ℕ := 62225653328057771307630486155

def quotedIters256 : ℕ := 267257146016241686964920093290467695825

theorem quotedIters128_floor :
    (quotedIters128 : ℝ) ≤ Real.pi / 4 * (2 : ℝ) ^ 64 ∧
      Real.pi / 4 * (2 : ℝ) ^ 64 < quotedIters128 + 1 := by
  have e : (2 : ℝ) ^ 64 = 18446744073709551616 := by norm_num
  have key : Real.pi / 4 * (2 : ℝ) ^ 64 = (4611686018427387904 : ℝ) * Real.pi := by
    rw [e]; ring
  have hlo : (14488038916154245684 : ℝ) ≤ (4611686018427387904 : ℝ) * Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hhi : (4611686018427387904 : ℝ) * Real.pi < (14488038916154245685 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  rw [key]
  constructor
  · rw [show ((quotedIters128 : ℕ) : ℝ) = (14488038916154245684 : ℝ) by norm_num [quotedIters128]]
    exact hlo
  · rw [show ((quotedIters128 : ℕ) : ℝ) + 1 = (14488038916154245685 : ℝ) by norm_num [quotedIters128]]
    exact hhi

def qubits (p : QuotedParams) : ℕ := p.boxes * p.s + 1

def perIterT (p : QuotedParams) : ℕ := 2 * p.boxes * p.t + p.ctrlT

def perIterC (p : QuotedParams) : ℕ := 2 * p.boxes * p.c

def tGates (p : QuotedParams) (n : ℕ) : ℕ := n * perIterT p

def clifford (p : QuotedParams) (n : ℕ) : ℕ := n * perIterC p

def tDepthRule (p : QuotedParams) (n : ℕ) : ℕ := n * 2 * p.tDepth

def depthRule (p : QuotedParams) (n : ℕ) : ℕ := n * 2 * p.totalDepth

theorem qubits_128 : qubits aes128 = 2953 := by
  norm_num [qubits, aes128]

theorem qubits_192 : qubits aes192 = 4449 := by
  norm_num [qubits, aes192]

theorem qubits_256 : qubits aes256 = 6681 := by
  norm_num [qubits, aes256]

theorem tGates_128_eq : tGates aes128 quotedIters128 = 92410333566331246819877392 := by
  norm_num [tGates, perIterT, aes128, quotedIters128]

theorem tGates_192_eq :
    tGates aes192 quotedIters192 = 600577364563695697783811630695542620 := by
  norm_num [tGates, perIterT, aes192, quotedIters192]

theorem tGates_256_eq :
    tGates aes256 quotedIters256 = 4028960272766967004167302688774324417454956500 := by
  norm_num [tGates, perIterT, aes256, quotedIters256]

theorem tGates_128_round : TightRounding 119 86 (tGates aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, tGates, perIterT, aes128, quotedIters128]

theorem tGates_192_round : TightRounding 181 118 (tGates aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, tGates, perIterT, aes192, quotedIters192]

theorem tGates_256_round : TightRounding 141 151 (tGates aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, tGates, perIterT, aes256, quotedIters256]

theorem clifford_128_round : TightRounding 155 86 (clifford aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, clifford, perIterC, aes128, quotedIters128]

theorem clifford_192_round : TightRounding 117 119 (clifford aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, clifford, perIterC, aes192, quotedIters192]

theorem clifford_256_round : TightRounding 183 151 (clifford aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, clifford, perIterC, aes256, quotedIters256]

theorem tDepthRule_128_round : TightRounding 121 80 (tDepthRule aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes128, quotedIters128]

theorem tDepthRule_192_round : TightRounding 106 112 (tDepthRule aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes192, quotedIters192]

theorem tDepthRule_256_round : TightRounding 144 144 (tDepthRule aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes256, quotedIters256]

theorem depthRule_128_round : TightRounding 133 81 (depthRule aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes128, quotedIters128]

theorem depthRule_192_round : TightRounding 116 113 (depthRule aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes192, quotedIters192]

theorem depthRule_256_round : TightRounding 157 145 (depthRule aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes256, quotedIters256]

theorem tDepth_128row : TightRounding 106 80 (tDepthRule aes192 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes192, quotedIters128]

theorem depth_128row : TightRounding 116 81 (depthRule aes192 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes192, quotedIters128]

theorem tDepth_192row : TightRounding 121 112 (tDepthRule aes128 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes128, quotedIters192]

theorem depth_192row : TightRounding 133 113 (depthRule aes128 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes128, quotedIters192]

theorem quoted_ledger_bounds :
    qubits aes128 = 2953 ∧ qubits aes192 = 4449 ∧ qubits aes256 = 6681 ∧
      TightRounding 119 86 (tGates aes128 quotedIters128 : ℚ) ∧
      TightRounding 155 86 (clifford aes128 quotedIters128 : ℚ) ∧
      TightRounding 181 118 (tGates aes192 quotedIters192 : ℚ) ∧
      TightRounding 117 119 (clifford aes192 quotedIters192 : ℚ) ∧
      TightRounding 141 151 (tGates aes256 quotedIters256 : ℚ) ∧
      TightRounding 183 151 (clifford aes256 quotedIters256 : ℚ) :=
  ⟨qubits_128, qubits_192, qubits_256,
    tGates_128_round, clifford_128_round,
    tGates_192_round, clifford_192_round,
    tGates_256_round, clifford_256_round⟩

structure Table5Row where
  keyBits : ℕ
  qubits : ℕ
  tMant : ℕ
  tExp : ℕ
  cMant : ℕ
  cExp : ℕ
  tdMant : ℕ
  tdExp : ℕ
  odMant : ℕ
  odExp : ℕ
deriving DecidableEq, Repr

def table5_128 : Table5Row :=
  ⟨128, 2953, 119, 86, 155, 86, 106, 80, 116, 81⟩

def table5_192 : Table5Row :=
  ⟨192, 4449, 181, 118, 117, 119, 121, 112, 133, 113⟩

def table5_256 : Table5Row :=
  ⟨256, 6681, 141, 151, 183, 151, 144, 144, 157, 145⟩

def RowMatches (row : Table5Row) (pD : QuotedParams) (nD : ℕ)
    (p : QuotedParams) (n : ℕ) : Prop :=
  qubits p = row.qubits ∧
    TightRounding row.tMant row.tExp (tGates p n : ℚ) ∧
    TightRounding row.cMant row.cExp (clifford p n : ℚ) ∧
    TightRounding row.tdMant row.tdExp (tDepthRule pD nD : ℚ) ∧
    TightRounding row.odMant row.odExp (depthRule pD nD : ℚ)

theorem row128 : RowMatches table5_128 aes192 quotedIters128 aes128 quotedIters128 :=
  ⟨qubits_128, tGates_128_round, clifford_128_round,
    tDepth_128row, depth_128row⟩

theorem row192 : RowMatches table5_192 aes128 quotedIters192 aes192 quotedIters192 :=
  ⟨qubits_192, tGates_192_round, clifford_192_round,
    tDepth_192row, depth_192row⟩

theorem row256 : RowMatches table5_256 aes256 quotedIters256 aes256 quotedIters256 :=
  ⟨qubits_256, tGates_256_round, clifford_256_round,
    tDepthRule_256_round, depthRule_256_round⟩

theorem printed_table_entries : RowMatches table5_128 aes192 quotedIters128 aes128 quotedIters128 ∧
    RowMatches table5_192 aes128 quotedIters192 aes192 quotedIters192 ∧
    RowMatches table5_256 aes256 quotedIters256 aes256 quotedIters256 :=
  ⟨row128, row192, row256⟩

end Qatlib.Papers.GroverAES15.GroverLedger
