/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Coverage
import Qatlib.Papers.LatentPQCTran26.MainResults.LinearMetaGrad
import Qatlib.Papers.LatentPQCTran26.MainResults.ActualWarmRoute

/-!
# Coverage by native squared gradients

`squaredGradient_continuous` supplies continuity of the squared native gradient from continuity
of the derivative. The estimates `reference_coverage` and `routed_coverage` use a derivative
norm bound and a lower bound on the reference mean to quantify the measure of parameters whose
squared gradient exceeds half that mean bound. See [TranEtAl2026] for the paper context.

## Main statements

* `reference_coverage`: If the derivative norm is bounded by positive `C` and the reference mean
  squared gradient is at least nonnegative `mu0` with `mu0 / 2 < C ^ 2`, the set with squared
  gradient at least `mu0 / 2` has reference real measure at least `mu0 / (2 * C ^ 2)`.
* `routed_coverage`: Under the stated derivative and reference-mean bounds, the routed mixture
  assigns real measure at least `lam * mu0 / (2 * C ^ 2)` to the set with squared gradient at
  least `mu0 / 2`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

noncomputable section
open MeasureTheory
namespace Qatlib.Papers.LatentPQCTran26.MainResults.NativeCoverage
open LinearMetaGrad Overlap Coverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
 [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in

/-- A continuous Fréchet derivative implies continuity of the squared native gradient norm. -/
theorem squaredGradient_continuous (L : E → ℝ) (hD : Continuous (fderiv ℝ L)) :
    Continuous (fun x => ‖gradient L x‖^2) := by
  simp only [nativeGradient_norm]
  exact hD.norm.pow 2

/-- If the derivative norm is bounded by positive `C` and the reference mean squared gradient is
at least nonnegative `mu0` with `mu0 / 2 < C ^ 2`, the set with squared gradient at least
`mu0 / 2` has reference real measure at least `mu0 / (2 * C ^ 2)`. -/
theorem reference_coverage
    (nu : Measure E) [IsProbabilityMeasure nu] (L : E → ℝ)
    (hD : Continuous (fderiv ℝ L)) (C mu0 : ℝ) (hC0 : 0 < C) (_hmu : 0 ≤ mu0)
    (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (hmean : mu0 ≤ ∫ x, ‖gradient L x‖^2 ∂nu) (hsml : mu0/2 < C^2) :
    mu0/(2*C^2) ≤ nu.real (gradRichSet (fun x => ‖gradient L x‖^2) (mu0/2)) := by
  have hF := squaredGradient_continuous L hD
  have hb : ∀ x, ‖gradient L x‖^2 ≤ C^2 := by
    intro x
    rw [nativeGradient_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  have hint : Integrable (fun x => ‖gradient L x‖^2) nu :=
    (integrable_const (C^2)).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact hb x))
  have hS : MeasurableSet (gradRichSet (fun x => ‖gradient L x‖^2) (mu0/2)) :=
    measurableSet_le measurable_const hF.measurable
  have hmain := reverse_markov nu (fun x => ‖gradient L x‖^2) (C^2) (mu0/2) mu0
    hint (fun x => sq_nonneg _) hb hmean hS hsml
  have hden : 0 < C^2-mu0/2 := by linarith
  have hC2 : 0 < C^2 := sq_pos_of_pos hC0
  have hnum : mu0/(2*C^2) ≤ (mu0-mu0/2)/(C^2-mu0/2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*C^2) hden).mpr
    nlinarith [sq_nonneg mu0]
  exact hnum.trans hmain

/-- Under the stated derivative and reference-mean bounds, the routed mixture assigns real
measure at least `lam * mu0 / (2 * C ^ 2)` to the set with squared gradient at least `mu0 /
2`. -/
theorem routed_coverage
    (nu train : Measure E) [IsProbabilityMeasure nu] [IsProbabilityMeasure train]
    (lam : NNReal) (L : E → ℝ) (hD : Continuous (fderiv ℝ L))
    (C mu0 : ℝ) (hC0 : 0 < C) (hmu : 0 ≤ mu0) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (hmean : mu0 ≤ ∫ x, ‖gradient L x‖^2 ∂nu) (hsml : mu0/2 < C^2) :
    (lam : ℝ) * (mu0/(2*C^2)) ≤
      ((ActualWarmRoute.prior nu train lam).map ActualWarmRoute.route).real
        (gradRichSet (fun x => ‖gradient L x‖^2) (mu0/2)) := by
  rw [ActualWarmRoute.pushforward,measureReal_add_apply,measureReal_nnreal_smul_apply]
  have hn := measureReal_nonneg (μ := (1-lam) • train)
    (s := gradRichSet (fun x => ‖gradient L x‖^2) (mu0/2))
  have hr := mul_le_mul_of_nonneg_left
    (reference_coverage nu L hD C mu0 hC0 hmu hC hmean hsml) lam.coe_nonneg
  exact hr.trans (le_add_of_nonneg_right hn)

end Qatlib.Papers.LatentPQCTran26.MainResults.NativeCoverage
