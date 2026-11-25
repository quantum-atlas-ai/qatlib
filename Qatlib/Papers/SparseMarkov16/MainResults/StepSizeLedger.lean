/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Step-size ledger of the second-order product formula

Childs--Li, *Efficient simulation of sparse Markovian quantum dynamics*,
fixed arXiv:1611.05543v3 (9 Oct 2023), Proposition 2.

Proposition 2 first bounds the error of one second-order product-formula step by
`16 m³t³L³/r²` for `m` summands, total time `t`, generator size `L` and `r`
symmetric steps, and then chooses `r` as `⌈4 (mtL)^{3/2}/√ε⌉` for the tolerance
`ε`. This module isolates only that scalar choice: from
`4 (mtL)^{3/2}/√ε ≤ r` it derives `16 m³t³L³/r² ≤ ε`.

The statement is arithmetic. It says nothing about the diamond norm, about the
product formula itself, or about the geometric-series premise `2mλL ≤ 1/2`
under which Proposition 2 applies the bound.
-/
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SparseMarkov16.MainResults.StepSizeLedger

/-- Proposition 2 step-size ledger: whenever the number of steps `r` dominates
`4 (mtL)^{3/2}/√ε`, the second-order error term `16 m³t³L³/r²` is at most `ε`.

For `r = 0` the real division is truncated at zero, so the bound holds
vacuously; the interesting case is `r > 0`, where squaring
`4 (mtL)^{3/2} ≤ r√ε` gives `16 m³t³L³ ≤ r²ε`. -/
theorem productFormula_error_of_step {m t L ε r : ℝ} (hm : 0 ≤ m) (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hε : 0 < ε) (hr : 4 * (m * t * L) ^ (3 / 2 : ℝ) / Real.sqrt ε ≤ r) :
    16 * m ^ 3 * t ^ 3 * L ^ 3 / r ^ 2 ≤ ε := by
  have hA : (0 : ℝ) ≤ m * t * L := mul_nonneg (mul_nonneg hm ht) hL
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hleft : 0 ≤ 4 * (m * t * L) ^ (3 / 2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hA _)
  have hr0 : 0 ≤ r := le_trans (div_nonneg hleft hsqrt.le) hr
  have hmul : 4 * (m * t * L) ^ (3 / 2 : ℝ) ≤ r * Real.sqrt ε := (div_le_iff₀ hsqrt).mp hr
  have hsq : (4 * (m * t * L) ^ (3 / 2 : ℝ)) * (4 * (m * t * L) ^ (3 / 2 : ℝ)) ≤
      (r * Real.sqrt ε) * (r * Real.sqrt ε) := mul_self_le_mul_self hleft hmul
  have hpow : ((m * t * L) ^ (3 / 2 : ℝ)) ^ 2 = (m * t * L) ^ 3 := by
    calc ((m * t * L) ^ (3 / 2 : ℝ)) ^ 2
        = ((m * t * L) ^ (3 / 2 : ℝ)) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ = (m * t * L) ^ ((3 / 2 : ℝ) * 2) := (Real.rpow_mul hA (3 / 2) 2).symm
      _ = (m * t * L) ^ (3 : ℝ) := by norm_num
      _ = (m * t * L) ^ 3 := Real.rpow_natCast _ _
  have hsqε : (r * Real.sqrt ε) * (r * Real.sqrt ε) = r ^ 2 * ε := by
    rw [show r * Real.sqrt ε * (r * Real.sqrt ε) = r * r * (Real.sqrt ε * Real.sqrt ε) by
      ring]
    rw [Real.mul_self_sqrt hε.le]
    ring
  have hkey : (4 * (m * t * L) ^ (3 / 2 : ℝ)) * (4 * (m * t * L) ^ (3 / 2 : ℝ)) =
      16 * (m * t * L) ^ 3 := by
    rw [show (4 * (m * t * L) ^ (3 / 2 : ℝ)) * (4 * (m * t * L) ^ (3 / 2 : ℝ)) =
      16 * (((m * t * L) ^ (3 / 2 : ℝ)) ^ 2) by ring, hpow]
  have hmain : 16 * (m * t * L) ^ 3 ≤ r ^ 2 * ε := by
    rw [← hkey]
    exact hsq.trans_eq hsqε
  have hexp : (m * t * L) ^ 3 = m ^ 3 * t ^ 3 * L ^ 3 := by ring
  have hfin : 16 * m ^ 3 * t ^ 3 * L ^ 3 ≤ ε * r ^ 2 := by
    nlinarith [hmain, hexp]
  rcases eq_or_lt_of_le hr0 with hzero | hpos
  · rw [show r = 0 from hzero.symm, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero]
    exact hε.le
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < r ^ 2)]
    exact hfin

end Qatlib.Papers.SparseMarkov16.MainResults.StepSizeLedger
