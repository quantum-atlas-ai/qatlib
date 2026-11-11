/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Sampling complexity of the single-ancilla observable estimation routine

Source: Jiang and An, "Contour-integral based quantum eigenvalue transformation: analysis and
applications", fixed arXiv:2601.11959v3 (2026-09-20).

This file records the mathematical core of the observable-estimation guarantees of Theorem 9
(p. 19), Theorem 13 (Appendix C, p. 36) and Theorem 10 (p. 19).  All three state the same
output guarantee — an estimate `μ` of `⟨ψ| f(A)† O f(A) |ψ⟩` within additive error `ϵ`, with
probability at least `(1 - ξ2)²` — and differ in the resource accounting of the circuit that
produces the samples.  The full statements quantify over the quantum circuit of Algorithm 1,
Step 3, which is not modelled at the paper layer, so only the scalar core is formalized here.

The paper's argument (Appendix C, eqs. (C.10)-(C.17)) has three mathematical ingredients:
Hoeffding's inequality for the sample mean (C.13)-(C.14), the perturbation bound of Theorem 12
(C.16), and the triangle inequality combining those two errors (C.17).  All three ingredients
are purely scalar and are proved below; the Hoeffding step is reduced to its arithmetic core,
namely that the paper's sample count is exactly the value making the Hoeffding exponent of
(C.13) reach `log(2/ξ2)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ContourQET26.ObservableEst

/-! ### Scalar core of the proof of Theorems 9, 10 and 13 -/

/-- **Hoeffding sample count (eq. (C.14)), arithmetic core.**  If the number of repetitions `T`
is at least `8‖O‖² ln(2/ξ2)‖c‖₁⁴ / ϵ²`, then the Hoeffding exponent of eq. (C.13) satisfies
`T ϵ² / (8‖c‖₁⁴‖O‖²) ≥ ln(2/ξ2)`. -/
lemma hoeffding_log_bound {normO normc1 ϵ T ξ2 : ℝ} (hO : 0 < normO) (hc : 0 < normc1)
    (hϵ : 0 < ϵ)
    (hT : 8 * normO ^ 2 * Real.log (2 / ξ2) * normc1 ^ 4 / ϵ ^ 2 ≤ T) :
    Real.log (2 / ξ2) ≤ T * ϵ ^ 2 / (8 * normO ^ 2 * normc1 ^ 4) := by
  have hA : 0 < 8 * normO ^ 2 * normc1 ^ 4 := by positivity
  have hϵ2 : 0 < ϵ ^ 2 := by positivity
  have h1 := (div_le_iff₀ hϵ2).mp hT
  have key : Real.log (2 / ξ2) * (8 * normO ^ 2 * normc1 ^ 4) ≤ T * ϵ ^ 2 := by
    nlinarith [h1]
  exact (le_div_iff₀ hA).mpr key

/-- **Hoeffding tail bound (eqs. (C.13)-(C.14)).**  With `T` repetitions as in (C.14), the
two-sided Hoeffding tail probability `2 exp(-T ϵ²/(8‖c‖₁⁴‖O‖²))` of eq. (C.13) is at most `ξ2`,
which is the "with probability at least `1 - ξ2`" claim of (C.15). -/
lemma hoeffding_tail_bound {normO normc1 ϵ T ξ2 : ℝ} (hO : 0 < normO) (hc : 0 < normc1)
    (hϵ : 0 < ϵ) (hξ2 : 0 < ξ2)
    (hT : 8 * normO ^ 2 * Real.log (2 / ξ2) * normc1 ^ 4 / ϵ ^ 2 ≤ T) :
    2 * Real.exp (-(T * ϵ ^ 2 / (8 * normO ^ 2 * normc1 ^ 4))) ≤ ξ2 := by
  have hlog := hoeffding_log_bound hO hc hϵ hT
  have hE : Real.exp (-(Real.log (2 / ξ2))) = ξ2 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 / ξ2)]
    field_simp
  calc 2 * Real.exp (-(T * ϵ ^ 2 / (8 * normO ^ 2 * normc1 ^ 4)))
      ≤ 2 * Real.exp (-(Real.log (2 / ξ2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
        exact Real.exp_le_exp.mpr (by linarith)
    _ = 2 * (ξ2 / 2) := by rw [hE]
    _ = ξ2 := by ring

/-- **Theorem 12 threshold (eq. (C.16)).**  If `ξ1 ≤ ϵ / (6‖O‖‖f(A)‖)` then the perturbation
error of Theorem 12 is at most `ϵ/2`, as used in eq. (C.16). -/
lemma xi1_threshold {normO normfA ξ1 ϵ : ℝ} (hO : 0 < normO) (hfA : 0 < normfA)
    (hbound : ξ1 ≤ ϵ / (6 * normO * normfA)) :
    3 * normO * normfA * ξ1 ≤ ϵ / 2 := by
  have h6 : 0 < 6 * normO * normfA := by positivity
  have hb := (le_div_iff₀ h6).mp hbound
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [hb]

/-- **Combination step (eq. (C.17)).**  The sampling error `|μ - g| ≤ ϵ/2` of (C.15) and the
perturbation error `|g - target| ≤ ϵ/2` of (C.16) give the final guarantee
`|μ - target| ≤ ϵ`. -/
lemma estimation_error_chain {μ g target ϵ : ℝ} (h1 : |μ - g| ≤ ϵ / 2)
    (h2 : |g - target| ≤ ϵ / 2) : |μ - target| ≤ ϵ := by
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Qatlib.Papers.ContourQET26.ObservableEst
