/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Grover-search resource arithmetic for AES

This module records the quoted AES circuit parameters and Grover iteration counts from
[GrasslEtAl2015], then computes qubit, gate, and depth expressions with exact integer
arithmetic. `TightRounding` certifies the displayed mantissa-and-exponent intervals.

The predicates `RowMatches` and the theorem `printed_table_entries` track the printed table
using separate parameter choices for gate counts and depths, including the cross-used AES-128
and AES-192 depth parameters.

## Main statements

* `quotedIters128_floor`: the floor bound for the quoted AES-128 iteration count.
* `quoted_ledger_bounds`: qubit counts and rounded gate-count intervals.
* `printed_table_entries`: the three printed table rows with their explicit depth-parameter
  choices.

## References

* [Grassl et al., 2015][GrasslEtAl2015]
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Qatlib.Papers.GroverAES15.GroverLedger

/-- The rational value lies in the half-open interval with endpoints `((2*m - 1)/200) * 2^e` and
`((2*m + 1)/200) * 2^e`, where the numerator subtraction is taken in natural numbers. -/
def TightRounding (m e : ℕ) (x : ℚ) : Prop :=
  (((2 * m : ℕ) - 1 : ℕ) : ℚ) / 200 * 2 ^ e ≤ x ∧
    x < (((2 * m : ℕ) + 1 : ℕ) : ℚ) / 200 * 2 ^ e

/-- The quoted key size, workspace size, T and Clifford counts, depths, parallel-box count, and
controlled-operation T-count parameter. -/
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

/-- The quoted circuit-resource parameters for the AES-128 ledger. -/
def aes128 : QuotedParams :=
  ⟨128, 984, 1060864, 1380420, 50688, 110799, 3, 13204⟩

/-- The quoted circuit-resource parameters for the AES-192 ledger. -/
def aes192 : QuotedParams :=
  ⟨192, 1112, 1204224, 1567296, 44352, 96956, 4, 17812⟩

/-- The quoted circuit-resource parameters for the AES-256 ledger. -/
def aes256 : QuotedParams :=
  ⟨256, 1336, 1505280, 1956099, 59904, 130929, 5, 22420⟩

/-- The quoted integer Grover iteration count for the AES-128 resource ledger. -/
def quotedIters128 : ℕ := 14488038916154245684

/-- The quoted integer Grover iteration count for the AES-192 resource ledger. -/
def quotedIters192 : ℕ := 62225653328057771307630486155

/-- The quoted integer Grover iteration count for the AES-256 resource ledger. -/
def quotedIters256 : ℕ := 267257146016241686964920093290467695825

/-- The quoted AES-128 iteration count is the floor of `(π/4) * 2^64` [GrasslEtAl2015]. -/
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

/-- The workspace count `p.boxes * p.s` plus one additional qubit. -/
def qubits (p : QuotedParams) : ℕ := p.boxes * p.s + 1

/-- The per-iteration T-gate count `2 * p.boxes * p.t + p.ctrlT`. -/
def perIterT (p : QuotedParams) : ℕ := 2 * p.boxes * p.t + p.ctrlT

/-- The per-iteration Clifford-gate count `2 * p.boxes * p.c`. -/
def perIterC (p : QuotedParams) : ℕ := 2 * p.boxes * p.c

/-- The total T-gate count for `n` iterations using the supplied resource parameters. -/
def tGates (p : QuotedParams) (n : ℕ) : ℕ := n * perIterT p

/-- The total Clifford-gate count for `n` iterations using the supplied resource parameters. -/
def clifford (p : QuotedParams) (n : ℕ) : ℕ := n * perIterC p

/-- The T-depth expression `n * 2 * p.tDepth` for `n` iterations. -/
def tDepthRule (p : QuotedParams) (n : ℕ) : ℕ := n * 2 * p.tDepth

/-- The total-depth expression `n * 2 * p.totalDepth` for `n` iterations. -/
def depthRule (p : QuotedParams) (n : ℕ) : ℕ := n * 2 * p.totalDepth

/-- The AES-128 workspace expression evaluates to 2953 qubits. -/
theorem qubits_128 : qubits aes128 = 2953 := by
  norm_num [qubits, aes128]

/-- The AES-192 workspace expression evaluates to 4449 qubits. -/
theorem qubits_192 : qubits aes192 = 4449 := by
  norm_num [qubits, aes192]

/-- The AES-256 workspace expression evaluates to 6681 qubits. -/
theorem qubits_256 : qubits aes256 = 6681 := by
  norm_num [qubits, aes256]

/-- The AES-128 T-gate expression at the quoted iteration count evaluates to
`92410333566331246819877392`. -/
theorem tGates_128_eq : tGates aes128 quotedIters128 = 92410333566331246819877392 := by
  norm_num [tGates, perIterT, aes128, quotedIters128]

/-- The AES-192 T-gate expression at the quoted iteration count evaluates to
`600577364563695697783811630695542620`. -/
theorem tGates_192_eq :
    tGates aes192 quotedIters192 = 600577364563695697783811630695542620 := by
  norm_num [tGates, perIterT, aes192, quotedIters192]

/-- The AES-256 T-gate expression at the quoted iteration count evaluates to
`4028960272766967004167302688774324417454956500`. -/
theorem tGates_256_eq :
    tGates aes256 quotedIters256 = 4028960272766967004167302688774324417454956500 := by
  norm_num [tGates, perIterT, aes256, quotedIters256]

/-- The AES-128 T-gate count lies in the rounding interval around `1.19 * 2^86`. -/
theorem tGates_128_round : TightRounding 119 86 (tGates aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, tGates, perIterT, aes128, quotedIters128]

/-- The AES-192 T-gate count lies in the rounding interval around `1.81 * 2^118`. -/
theorem tGates_192_round : TightRounding 181 118 (tGates aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, tGates, perIterT, aes192, quotedIters192]

/-- The AES-256 T-gate count lies in the rounding interval around `1.41 * 2^151`. -/
theorem tGates_256_round : TightRounding 141 151 (tGates aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, tGates, perIterT, aes256, quotedIters256]

/-- The AES-128 Clifford-gate count lies in the rounding interval around `1.55 * 2^86`. -/
theorem clifford_128_round : TightRounding 155 86 (clifford aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, clifford, perIterC, aes128, quotedIters128]

/-- The AES-192 Clifford-gate count lies in the rounding interval around `1.17 * 2^119`. -/
theorem clifford_192_round : TightRounding 117 119 (clifford aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, clifford, perIterC, aes192, quotedIters192]

/-- The AES-256 Clifford-gate count lies in the rounding interval around `1.83 * 2^151`. -/
theorem clifford_256_round : TightRounding 183 151 (clifford aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, clifford, perIterC, aes256, quotedIters256]

/-- The AES-128 T-depth expression with its own parameters lies in the rounding interval around
`1.21 * 2^80`. -/
theorem tDepthRule_128_round : TightRounding 121 80 (tDepthRule aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes128, quotedIters128]

/-- The AES-192 T-depth expression with its own parameters lies in the rounding interval around
`1.06 * 2^112`. -/
theorem tDepthRule_192_round : TightRounding 106 112 (tDepthRule aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes192, quotedIters192]

/-- The AES-256 T-depth expression lies in the rounding interval around `1.44 * 2^144`. -/
theorem tDepthRule_256_round : TightRounding 144 144 (tDepthRule aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes256, quotedIters256]

/-- The AES-128 total-depth expression with its own parameters lies in the rounding interval
around `1.33 * 2^81`. -/
theorem depthRule_128_round : TightRounding 133 81 (depthRule aes128 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes128, quotedIters128]

/-- The AES-192 total-depth expression with its own parameters lies in the rounding interval
around `1.16 * 2^113`. -/
theorem depthRule_192_round : TightRounding 116 113 (depthRule aes192 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes192, quotedIters192]

/-- The AES-256 total-depth expression lies in the rounding interval around `1.57 * 2^145`. -/
theorem depthRule_256_round : TightRounding 157 145 (depthRule aes256 quotedIters256 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes256, quotedIters256]

/-- Using the AES-192 depth parameter with the AES-128 iteration count gives the rounding
interval around `1.06 * 2^80` [GrasslEtAl2015]. -/
theorem tDepth_128row : TightRounding 106 80 (tDepthRule aes192 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes192, quotedIters128]

/-- Using the AES-192 total-depth parameter with the AES-128 iteration count gives the rounding
interval around `1.16 * 2^81` [GrasslEtAl2015]. -/
theorem depth_128row : TightRounding 116 81 (depthRule aes192 quotedIters128 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes192, quotedIters128]

/-- Using the AES-128 depth parameter with the AES-192 iteration count gives the rounding
interval around `1.21 * 2^112` [GrasslEtAl2015]. -/
theorem tDepth_192row : TightRounding 121 112 (tDepthRule aes128 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, tDepthRule, aes128, quotedIters192]

/-- Using the AES-128 total-depth parameter with the AES-192 iteration count gives the rounding
interval around `1.33 * 2^113` [GrasslEtAl2015]. -/
theorem depth_192row : TightRounding 133 113 (depthRule aes128 quotedIters192 : ℚ) := by
  constructor <;> norm_num [TightRounding, depthRule, aes128, quotedIters192]

/-- The three AES ledgers have the stated qubit counts and T-gate and Clifford-gate rounding
intervals at their quoted iteration counts [GrasslEtAl2015]. -/
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

/-- A printed resource-table row containing the key size, qubit count, and mantissa-and-exponent
pairs for gate counts and depths. -/
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

/-- The printed Table 5 resource row labeled AES-128. -/
def table5_128 : Table5Row :=
  ⟨128, 2953, 119, 86, 155, 86, 106, 80, 116, 81⟩

/-- The printed Table 5 resource row labeled AES-192. -/
def table5_192 : Table5Row :=
  ⟨192, 4449, 181, 118, 117, 119, 121, 112, 133, 113⟩

/-- The printed Table 5 resource row labeled AES-256. -/
def table5_256 : Table5Row :=
  ⟨256, 6681, 141, 151, 183, 151, 144, 144, 157, 145⟩

/-- The row's qubit and rounded gate counts match `p` and `n`, while its rounded depths match
the separately supplied `pD` and `nD`. -/
def RowMatches (row : Table5Row) (pD : QuotedParams) (nD : ℕ)
    (p : QuotedParams) (n : ℕ) : Prop :=
  qubits p = row.qubits ∧
    TightRounding row.tMant row.tExp (tGates p n : ℚ) ∧
    TightRounding row.cMant row.cExp (clifford p n : ℚ) ∧
    TightRounding row.tdMant row.tdExp (tDepthRule pD nD : ℚ) ∧
    TightRounding row.odMant row.odExp (depthRule pD nD : ℚ)

/-- The AES-128 printed row matches AES-128 gate parameters and AES-192 depth parameters, both
at the AES-128 iteration count. -/
theorem row128 : RowMatches table5_128 aes192 quotedIters128 aes128 quotedIters128 :=
  ⟨qubits_128, tGates_128_round, clifford_128_round,
    tDepth_128row, depth_128row⟩

/-- The AES-192 printed row matches AES-192 gate parameters and AES-128 depth parameters, both
at the AES-192 iteration count. -/
theorem row192 : RowMatches table5_192 aes128 quotedIters192 aes192 quotedIters192 :=
  ⟨qubits_192, tGates_192_round, clifford_192_round,
    tDepth_192row, depth_192row⟩

/-- The AES-256 printed row matches the AES-256 gate and depth parameters at the quoted AES-256
iteration count. -/
theorem row256 : RowMatches table5_256 aes256 quotedIters256 aes256 quotedIters256 :=
  ⟨qubits_256, tGates_256_round, clifford_256_round,
    tDepthRule_256_round, depthRule_256_round⟩

/-- All three printed resource rows satisfy `RowMatches` with the displayed parameter choices,
including the cross-used AES-128 and AES-192 depth parameters [GrasslEtAl2015]. -/
theorem printed_table_entries : RowMatches table5_128 aes192 quotedIters128 aes128 quotedIters128 ∧
    RowMatches table5_192 aes128 quotedIters192 aes192 quotedIters192 ∧
    RowMatches table5_256 aes256 quotedIters256 aes256 quotedIters256 :=
  ⟨row128, row192, row256⟩

end Qatlib.Papers.GroverAES15.GroverLedger
