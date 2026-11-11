/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.GroverPlane.Coefficients — Lemma 8: lower bound for the coefficient length

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Lemma 8, Eq. (B19), p. 18–19.

In the fixed Grover-plane basis `{X₀, Y₀}` the gradient is `g_k = x_k X₀ + y_k Y₀`, and the
coefficient length is `ξ_k := √(x_k² + y_k²)`.  Using `‖X₀‖_F² = ‖Y₀‖_F² = 2q₀(1-q₀)` and
`‖g_k‖_F² = 2q_k(1-q_k)`, Lemma 8 proves
`ξ_k² = q_k(1-q_k) / (q₀(1-q₀))` (Eq. (B19)),
and, away from the Newton region (`e_k > r_N`), the uniform lower bound `ξ_k ≥ 1/32`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.GroverPlane.Coefficients

/-- **Lemma 8, Eq. (B19)** (arXiv:2603.26039v3, p. 18).  If the squared gradient norm is
`‖g_k‖_F² = 2q_k(1-q_k)`, the basis vectors satisfy `‖X₀‖_F² = ‖Y₀‖_F² = 2q₀(1-q₀)`, and
`ξ_k² ‖X₀‖_F² = ‖g_k‖_F²` (orthogonal basis decomposition), then
`ξ_k² = q_k(1-q_k)/(q₀(1-q₀))`. -/
theorem coefficient_length_identity
    (q q0 ξ2 gSq XSq : ℝ) (hq0 : 0 < q0) (hq01 : q0 < 1)
    (hXSq : XSq = 2 * q0 * (1 - q0))
    (hgSq : gSq = 2 * q * (1 - q))
    (hξ : gSq = ξ2 * XSq) :
    ξ2 = q * (1 - q) / (q0 * (1 - q0)) := by
  have h2 : q0 * (1 - q0) ≠ 0 := by
    have : 0 < q0 * (1 - q0) := mul_pos hq0 (by linarith)
    positivity
  rw [hgSq, hXSq] at hξ
  rw [eq_div_iff h2]
  linarith [hξ]

/-- **Lemma 8, lower bound** (arXiv:2603.26039v3, p. 18–19).  Assume `q ∈ [q₀, 1 - r_N]`
(monotonicity `q_k ≥ q₀` and `e_k = 1 - q_k > r_N`), that `0 < r_N < 1/2` and
`r_N ≥ q₀(1-q₀)/512` (the paper's estimate `r_N ≥ p₀/512` for `p₀ = q₀(1-q₀)`), and the
identity `ξ² = q(1-q)/(q₀(1-q₀))` of Eq. (B19).  Then `ξ² ≥ 1/1024` and `ξ ≥ 1/32`. -/
theorem coefficient_length_lower_bound
    (q q0 ξ2 rN : ℝ) (hq0 : 0 < q0) (hq01 : q0 < 1)
    (hqge : q0 ≤ q) (hqle : q ≤ 1 - rN)
    (hrN0 : 0 < rN) (hrNhalf : rN < 1 / 2)
    (hrNge : rN ≥ q0 * (1 - q0) / 512)
    (hξ : ξ2 = q * (1 - q) / (q0 * (1 - q0))) :
    ξ2 ≥ 1 / 1024 ∧ Real.sqrt ξ2 ≥ 1 / 32 := by
  have hp0 : 0 < q0 * (1 - q0) := mul_pos hq0 (by linarith)
  -- Concavity of `q ↦ q(1-q)` on the interval `[q₀, 1-r_N]`.
  have hconcave : q * (1 - q) ≥ min (q0 * (1 - q0)) (rN * (1 - rN)) := by
    by_cases hqh : q ≤ 1 / 2
    · have hfactor : 0 ≤ (q - q0) * (1 - q - q0) := by
        apply mul_nonneg
        · linarith
        · linarith
      have hgt : q * (1 - q) ≥ q0 * (1 - q0) := by nlinarith [hfactor]
      exact le_trans (min_le_left _ _) hgt
    · push_neg at hqh
      have hfactor : 0 ≤ (q - rN) * (1 - q - rN) := by
        apply mul_nonneg
        · linarith
        · linarith
      have hgt : q * (1 - q) ≥ rN * (1 - rN) := by nlinarith [hfactor]
      exact le_trans (min_le_right _ _) hgt
  -- The right-hand side of Eq. (B19) is at least `1/1024`.
  have hmin : min (q0 * (1 - q0)) (rN * (1 - rN)) ≥ q0 * (1 - q0) / 1024 := by
    apply le_min
    · nlinarith [hp0]
    · have h1 : q0 * (1 - q0) / 512 ≤ rN := hrNge
      have h2 : (1 : ℝ) / 2 ≤ 1 - rN := by linarith
      have ha : 0 ≤ q0 * (1 - q0) / 512 := by positivity
      have hb : 0 ≤ rN := le_of_lt hrN0
      have hmul := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) hb
      have hleft : q0 * (1 - q0) / 512 * ((1 : ℝ) / 2) = q0 * (1 - q0) / 1024 := by ring
      rw [hleft] at hmul
      exact hmul
  have hmain : q * (1 - q) ≥ q0 * (1 - q0) / 1024 := le_trans hmin hconcave
  have hξ2ge : ξ2 ≥ 1 / 1024 := by
    rw [hξ, ge_iff_le, le_div_iff₀ hp0]
    nlinarith [hmain]
  constructor
  · exact hξ2ge
  · have h2 : Real.sqrt (1 / 1024 : ℝ) ≤ Real.sqrt ξ2 := Real.sqrt_le_sqrt hξ2ge
    have h3 : Real.sqrt (1 / 1024 : ℝ) = 1 / 32 := by
      rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h2, h3]

end Qatlib.Papers.QSearchPrec26.RmSearch.GroverPlane.Coefficients
