/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ProdFormSpec21.MainResults.SourceProposition1
public import Qatlib.Papers.ProdFormSpec21.MainResults.SourceCorollary3
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimization of the Proposition 1 two-term Trotter bound

For [YiCrosson2022], Proposition 1, Eq. (35), the leading error bound
has a two-term shape. We study the unit-coefficient model
`D²/(T lam³) + C₁² T/(M² lam³)` in the total time `T`, at fixed depth
`M`, endpoint distance `D = ‖Hᵢ - H_f‖`, commutator scale
`C₁ = ‖[Hᵢ, H_f]‖` and gap lower bound `lam`; see
`Qatlib.Papers.ProdFormSpec21.MainResults.proposition1_leading_bound`.
This module optimizes that shape exactly: by AM--GM it is bounded
below by `2 D C₁/(M lam³)` for every `T > 0`, and at the Corollary 3
critical time `T_c = 2 M D/(3 C₁)` (Eq. (42)) its value is
`(13/6) D C₁/(M lam³)`, within a factor `13/12` of its minimum.
The minimum of the two-term model is attained at `M D/C₁`.
Corollary 3 instead minimizes the Appendix F model with the squared
numerator `(D + 3 C₁ T/(2 M))²`.

The Lemma 2 / Lemma 4 estimates that produce the two terms are the
analytic input of Proposition 1 and are not reproved here.
[Fixed source](https://arxiv.org/abs/2102.12655v1).
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open Qatlib.Papers.ProdFormSpec21.MainResults
open scoped Matrix.Norms.L2Operator

/-- The two-term Proposition 1 bound
`D²/(T * lam³) + C₁² * T/(M² * lam³)` as a function of the total
time `T`. -/
noncomputable def twoTermBound (D C1 M lam T : ℝ) : ℝ :=
  D ^ 2 / (T * lam ^ 3) + C1 ^ 2 * T / (M ^ 2 * lam ^ 3)

/-- **Proposition 1 bound, global lower bound.**  For positive
`D C1 M lam T`, the two-term bound is at least
`2 * D * C1 / (M * lam ^ 3)`, by AM--GM on its two positive terms. -/
theorem two_term_bound_ge (D C1 M lam T : ℝ) (hD : 0 < D) (hC1 : 0 < C1)
    (hM : 0 < M) (hlam : 0 < lam) (hT : 0 < T) :
    2 * D * C1 / (M * lam ^ 3) ≤ twoTermBound D C1 M lam T := by
  unfold twoTermBound
  set a : ℝ := D ^ 2 / (T * lam ^ 3) with ha
  set b : ℝ := C1 ^ 2 * T / (M ^ 2 * lam ^ 3) with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hK : (0 : ℝ) ≤ D * C1 / (M * lam ^ 3) := by positivity
  have hab : a * b = (D * C1 / (M * lam ^ 3)) ^ 2 := by
    rw [ha, hb]
    field_simp
  have hsqrt : Real.sqrt a * Real.sqrt b = D * C1 / (M * lam ^ 3) := by
    rw [← Real.sqrt_mul ha0, hab, Real.sqrt_sq hK]
  have hgoal : 2 * (D * C1 / (M * lam ^ 3)) ≤ a + b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha0,
      Real.sq_sqrt hb0, hsqrt]
  have hform : 2 * D * C1 / (M * lam ^ 3) = 2 * (D * C1 / (M * lam ^ 3)) := by
    rw [mul_assoc, mul_div_assoc]
  rw [hform]
  exact hgoal

/-- The lower bound is attained at the positive time `M D/C₁`. -/
theorem two_term_bound_at_balanced_time (D C1 M lam : ℝ) (hD : 0 < D)
    (hC1 : 0 < C1) (hM : 0 < M) (hlam : 0 < lam) :
    twoTermBound D C1 M lam (M * D / C1) = 2 * D * C1 / (M * lam ^ 3) := by
  unfold twoTermBound
  field_simp [hD.ne', hC1.ne', hM.ne', hlam.ne']
  ring

/-- **Corollary 3 time in the two-term bound.**  At the critical time
`T_c = 2 M D/(3 C₁)` of Eq. (42), the two-term Proposition 1 bound
takes the value `(13/6) * D * C1 / (M * lam ^ 3)`, the Eq. (43) scale
with explicit constant `13/6`. -/
theorem two_term_bound_at_critical (D C1 M lam : ℝ) (hD : 0 < D)
    (hC1 : 0 < C1) (hM : 0 < M) (hlam : 0 < lam) :
    twoTermBound D C1 M lam
        (Qatlib.Papers.ProdFormSpec21.MainResults.criticalT D C1 M)
      = 13 / 6 * (D * C1 / (M * lam ^ 3)) := by
  unfold twoTermBound
    Qatlib.Papers.ProdFormSpec21.MainResults.criticalT
  field_simp [hD.ne', hC1.ne', hM.ne', hlam.ne']
  ring

/-- **Near-optimality at `T_c`.**  The value of the two-term bound at
the Corollary 3 critical time is within a factor `13/12` of its
global lower bound `2 * D * C1 / (M * lam ^ 3)`: it equals
`(13/12) * (2 * D * C1 / (M * lam ^ 3))`. -/
theorem two_term_bound_at_critical_factor (D C1 M lam : ℝ) (hD : 0 < D)
    (hC1 : 0 < C1) (hM : 0 < M) (hlam : 0 < lam) :
    twoTermBound D C1 M lam
        (Qatlib.Papers.ProdFormSpec21.MainResults.criticalT D C1 M)
      = 13 / 12 * (2 * D * C1 / (M * lam ^ 3)) := by
  rw [two_term_bound_at_critical D C1 M lam hD hC1 hM hlam]
  ring

/-- **Proposition 1 + Corollary 3 combined.**  If a Trotter error
`εtro` is bounded by the two-term bound at the critical time (for
instance via
`Qatlib.Papers.ProdFormSpec21.MainResults.proposition1_leading_bound`
applied at `T = T_c`), then
`εtro ≤ (13/6) * D * C1 / (M * lam ^ 3)`, the Eq. (43) optimal-error
scale with explicit constant. -/
theorem trotter_error_le_at_critical (εtro D C1 M lam : ℝ)
    (hD : 0 < D) (hC1 : 0 < C1) (hM : 0 < M) (hlam : 0 < lam)
    (htro : εtro ≤ twoTermBound D C1 M lam
      (Qatlib.Papers.ProdFormSpec21.MainResults.criticalT D C1 M)) :
    εtro ≤ 13 / 6 * (D * C1 / (M * lam ^ 3)) := by
  rw [two_term_bound_at_critical D C1 M lam hD hC1 hM hlam] at htro
  exact htro

/-- The operator-norm error between adiabatic and Trotterized evolutions
at the time in Eq. (42), assuming the two component bounds of the
unit-coefficient model at that time. -/
theorem total_trotter_error_le_at_critical {I : Type*} [Fintype I] [Nonempty I]
    [DecidableEq I] (Ad Tt P Pf : Matrix I I ℂ) (D C1 M lam : ℝ)
    (hD : 0 < D) (hC1 : 0 < C1) (hM : 0 < M) (hlam : 0 < lam)
    (hadb : adiabaticError Ad P Pf ≤ D ^ 2 / (criticalT D C1 M * lam ^ 3))
    (htot : trotterErr Tt P Pf ≤ C1 ^ 2 * criticalT D C1 M / (M ^ 2 * lam ^ 3)) :
    totalTrotterError Ad Tt P ≤ 13 / 6 * (D * C1 / (M * lam ^ 3)) := by
  have hT : 0 < criticalT D C1 M := by
    unfold criticalT
    positivity
  exact trotter_error_le_at_critical _ D C1 M lam hD hC1 hM hlam
    (proposition1_leading_bound _ _ _ D C1 lam _ M hlam hD hC1 hT hM
      (proposition1_triangle Ad Tt P Pf) hadb htot)

end Qatlib.Papers.ProdFormSpec21.MainResults
