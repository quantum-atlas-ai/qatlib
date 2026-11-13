/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Logarithmic Circuit-Depth Lower Bound from Legal-Path Counting

This module formalizes Corollary 2 (p. 15, Equation (38)) of Aharonov et al.,
establishing that whenever `n · 2^d · 3^{d - 1} ≤ C · 15^{d + 1}` holds for a
positive constant `C`, the circuit depth `d` grows as `Ω(log n)` for all
sufficiently large `n`.

## Main statements

* `source_corollary2_depth_log`: Corollary 2, logarithmic circuit-depth lower
  bound `c · log n ≤ d` from exponential path-weight upper bounds.

## References

* [Aharonov et al., 2022][AharonovEtAl2022Noisy], Corollary 2, p. 15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Paths

/-- Fixed arXiv:2211.03999v1, Corollary 2, p.15: if `n · 2^d · 3^{d-1} ≤ C · 15^{d+1}` for
an absolute constant `C`, then asymptotically `d = Ω(log n)`. -/
theorem source_corollary2_depth_log
    (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (n d : ℕ), n₀ ≤ n →
      (n : ℝ) * (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) ≤ C * (15 : ℝ) ^ (d + 1) →
      c * Real.log n ≤ d := by
  let L : ℝ := Real.log (5 / 2 : ℝ)
  have hL : 0 < L := Real.log_pos (by norm_num)
  let M : ℝ := max 0 (Real.log (45 * C))
  refine ⟨1 / (2 * L), by positivity, max 2 ⌈Real.exp (2 * M)⌉₊, ?_⟩
  intro n d hn₀ hbound
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn₀
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
  have hexp : Real.exp (2 * M) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn₀)
  have hM : Real.log (45 * C) ≤ Real.log n / 2 := by
    have hlog := Real.log_le_log (Real.exp_pos (2 * M)) hexp
    rw [Real.log_exp] at hlog
    have hmax : Real.log (45 * C) ≤ M := le_max_right _ _
    linarith
  have hthree : (3 : ℝ) ^ d / 3 ≤ (3 : ℝ) ^ (d - 1) := by
    cases d with
    | zero => norm_num
    | succ k => simp [pow_succ]
  have hscaled : (n : ℝ) * (6 : ℝ) ^ d / 3 ≤ C * 15 * (15 : ℝ) ^ d := calc
    (n : ℝ) * (6 : ℝ) ^ d / 3 =
        (n : ℝ) * (2 : ℝ) ^ d * ((3 : ℝ) ^ d / 3) := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]
      ring
    _ ≤ (n : ℝ) * (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) :=
      mul_le_mul_of_nonneg_left hthree (by positivity)
    _ ≤ C * (15 : ℝ) ^ (d + 1) := hbound
    _ = C * 15 * (15 : ℝ) ^ d := by rw [pow_succ]; ring
  have hnle : (n : ℝ) ≤ 45 * C * (5 / 2 : ℝ) ^ d := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < (6 : ℝ) ^ d)).mp
    calc
      (n : ℝ) * (6 : ℝ) ^ d ≤ (C * 15 * (15 : ℝ) ^ d) * 3 :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mp hscaled
      _ = (45 * C * (5 / 2 : ℝ) ^ d) * (6 : ℝ) ^ d := by
        rw [mul_assoc (45 * C), ← mul_pow]
        norm_num
        ring
  have hlog := Real.log_le_log hnpos hnle
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  change Real.log n ≤ Real.log (45 * C) + (d : ℝ) * L at hlog
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity : 0 < 2 * L)).2
  nlinarith only [hlog, hM]

end Qatlib.Papers.NoisyCircuit22.MainResults.Paths
