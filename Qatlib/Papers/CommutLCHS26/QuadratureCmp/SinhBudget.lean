/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhError

/-!
# Budget selection for sinh quadrature

This module selects the sinh quadrature mesh `step` and the tail `selectedWindow` from positive
error budgets. Under the analytic-width and positivity hypotheses, the resulting finite rule
satisfies the combined budget estimate associated with [AftabAnTrivisa2026].

## Main statements

* `step_pos`: positivity of the selected mesh step.
* `selected_error`: a finite quadrature error bounded by the sum of mesh and tail budgets.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
open Complex Matrix Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhError
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

/-- The budget-selected sinh mesh step, capped at one and scaled by the strip half-width and
mesh logarithm. -/
def step (β M ε : ℝ) : ℝ := min 1 (2 * Real.pi * β / meshLog M ε)

/-- The sinh window obtained from the square root of the selected tail logarithm. -/
def selectedWindow (n : ℕ) (b c d η ε : ℝ) : ℝ :=
  window c η (Real.sqrt (tailLog (tailConstant n b c d) ε))

/-- The selected mesh step is positive for positive half-width, strip mass, and error budget. -/
theorem step_pos {β M ε : ℝ} (hβ : 0 < β) (hM : 0 < M) (hε : 0 < ε) : 0 < step β M ε := by
  have hl := meshLog_pos hM hε
  unfold step
  positivity

/-- For a nonempty matrix index type and positive scales, the strip mass is positive at a
half-width below `analyticWidth` and `π / 4`. -/
theorem stripMass_pos [Nonempty ι] (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4) (T : ℝ) (H L : Matrix ι ι ℂ)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    0 < stripMass n b c d η β (T * ‖L‖) := by
  obtain ⟨hgap, hbn⟩ := gaps_of_lt_width n hb hη hβ₀ (by linarith [Real.pi_pos]) c d T H L hw
  have hd := distance_product_pos n hη hβ₀ (by linarith [Real.pi_pos]) hgap hbn
  have hp : 0 < kernelPrefactor n b η β := by
    unfold kernelPrefactor
    apply div_pos (pow_pos (by linarith : 0 < b + 1) n)
    convert! mul_pos (show 0 < 2 * Real.pi by positivity) hd using 1; ring
  have hB := gaussian_rate_pos hc hη hβ₀ hβ
  exact mul_pos (mul_pos (mul_pos hη hp) (Real.exp_pos _))
    (Real.sqrt_pos.mpr (div_pos (by positivity) hB))

/-- The selected sinh mesh step is positive, and the selected finite rule has error at most the
sum of the positive mesh and tail budgets under the stated analytic-width hypotheses; see
[Aftab et al., Corollary 4.18][AftabAnTrivisa2026]. -/
theorem selected_error [Nonempty ι] (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T εm εt : ℝ}
    (hT : 0 ≤ T) (hεm : 0 < εm) (hεt : 0 < εt)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    let h := step β (stripMass n b c d η β (T * ‖L‖)) εm
    let Y := selectedWindow n b c d η εt
    0 < h ∧ ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
      finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤ εm + εt := by
  (try dsimp only)
  let M := stripMass n b c d η β (T * ‖L‖)
  let h := step β M εm
  let Y := selectedWindow n b c d η εt
  have hM : 0 < M := stripMass_pos n b c d η β hb hc hη hβ₀.le hβ T H L hw
  have hh : 0 < h := step_pos hβ₀ hM hεm
  have hm : 2 * M / (Real.exp (2 * Real.pi * β / h) - 1) ≤ εm :=
    mesh_budget_of_step hM hεm hh (min_le_right _ _)
  have ht : latticeTail n b c d T η h H L (cutoff Y h) ≤ εt :=
    selected_tail_budget n b c d hb hc H L hH hL hT hη hh hεt
  exact ⟨hh, (original_finite_error n b c d η β hb hc hη hβ₀ hβ H L hH hL hT hh Y hw).trans
    (_root_.add_le_add hm ht)⟩

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
