/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Population derivatives for linear decoders

`populationLoss` averages a loss after a feature-dependent continuous linear decoder. Under
boundedness, measurability, and differentiability hypotheses, its derivative is the integral of
the sample derivatives. A common bias right inverse yields `bias_identity` and lower bounds on
the bias and full derivative norms for outputs concentrated near a reference point. See
[TranEtAl2026] for the paper context.

## Main statements

* `populationLoss_hasFDerivAt`: Under the stated measurability, uniform boundedness, and
  smoothness assumptions, the sample derivative is integrable and its integral is the Fréchet
  derivative of `populationLoss`.
* `bias_identity`: If `b` is a common right inverse for the decoders, the population derivative
  composed with `b` is the mean output-space derivative, under the stated
  differentiation-under-the-integral hypotheses.
* `fullDerivative_lower_bound`: Under the stated regularity and concentration hypotheses, a
  common bias right inverse of norm at most one gives a bias derivative norm at least `g -
  Lambda * gamma` and at most the full population derivative norm.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Filter
open scoped Topology
namespace Qatlib.Papers.LatentPQCTran26.MainResults.LinearMetaGrad
variable {E H P Z : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
 [NormedAddCommGroup H] [NormedSpace ℝ H]
 [NormedAddCommGroup P] [NormedSpace ℝ P]
 [MeasurableSpace Z]

/-- The integral of `L (T (h z) w)` over the latent measure `r`. -/
def populationLoss (r : Measure Z) (h : Z → H) (T : H → P →L[ℝ] E)
    (L : E → ℝ) (w : P) : ℝ := ∫ z, L (T (h z) w) ∂r

omit [CompleteSpace E] [NormedSpace ℝ H] in

/-- Under the stated measurability, uniform boundedness, and smoothness assumptions, the sample
derivative is integrable and its integral is the Fréchet derivative of `populationLoss`. -/
theorem populationLoss_hasFDerivAt
    (r : Measure Z) [IsProbabilityMeasure r] (h : Z → H)
    (hh : AEStronglyMeasurable h r) (T : H → P →L[ℝ] E) (hT : Continuous T)
    (N : ℝ) (hN : ∀ z, ‖T (h z)‖ ≤ N)
    (L : E → ℝ) (hL : Differentiable ℝ L) (hD : Continuous (fderiv ℝ L))
    (B C : ℝ) (hB : ∀ x, ‖L x‖ ≤ B) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (w : P) :
    Integrable (fun z => (fderiv ℝ L (T (h z) w)).comp (T (h z))) r ∧
    HasFDerivAt (populationLoss r h T L)
      (∫ z, (fderiv ℝ L (T (h z) w)).comp (T (h z)) ∂r) w := by
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ L 0)).trans (hC 0)
  have hcont : ∀ v : P,
      Continuous (fun u : H => (fderiv ℝ L (T u v)).comp (T u)) := by
    intro v
    fun_prop
  have hmeas : ∀ v : P, AEStronglyMeasurable (fun z => L (T (h z) v)) r := by
    intro v
    exact (hL.continuous.comp (hT.clm_apply continuous_const)).comp_aestronglyMeasurable hh
  have hbound : ∀ v : P, ∀ z,
      ‖(fderiv ℝ L (T (h z) v)).comp (T (h z))‖ ≤ C * N := by
    intro v z
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hC _) (hN z) (norm_nonneg _) hC0)
  have hint : Integrable (fun z => L (T (h z) w)) r :=
    Integrable.mono' (integrable_const B) (hmeas w) (Filter.Eventually.of_forall (fun z => hB _))
  have hresult := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun v z => L (T (h z) v))
    (F' := fun v z => (fderiv ℝ L (T (h z) v)).comp (T (h z)))
    (s := Set.univ) (bound := fun _ => C * N) (Filter.univ_mem)
    (Filter.Eventually.of_forall hmeas) hint
    ((hcont w).comp_aestronglyMeasurable hh)
    (Filter.Eventually.of_forall (fun z v _ => hbound v z)) (integrable_const _)
    (Filter.Eventually.of_forall (fun z v _ =>
      (hL _).hasFDerivAt.comp v (T (h z)).hasFDerivAt))
  exact ⟨Integrable.mono' (integrable_const (C * N))
    ((hcont w).comp_aestronglyMeasurable hh) (Filter.Eventually.of_forall (hbound w)),hresult⟩

/-- If `b` is a common right inverse for the decoders, the population derivative composed with
`b` is the mean output-space derivative, under the stated differentiation-under-the-integral
hypotheses. -/
theorem bias_identity
    (r : Measure Z) [IsProbabilityMeasure r] (h : Z → H)
    (hh : AEStronglyMeasurable h r) (T : H → P →L[ℝ] E) (hT : Continuous T)
    (N : ℝ) (hN : ∀ z, ‖T (h z)‖ ≤ N)
    (L : E → ℝ) (hL : Differentiable ℝ L) (hD : Continuous (fderiv ℝ L))
    (B C : ℝ) (hB : ∀ x, ‖L x‖ ≤ B) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (w : P) (b : E →L[ℝ] P) (hb : ∀ u, (T u).comp b = ContinuousLinearMap.id ℝ E) :
    (fderiv ℝ (populationLoss r h T L) w).comp b =
      ∫ z, fderiv ℝ L (T (h z) w) ∂r := by
  obtain ⟨hint, hd⟩ := populationLoss_hasFDerivAt r h hh T hT N hN L hL hD B C hB hC w
  rw [hd.fderiv]
  have hdi : Integrable (fun z => fderiv ℝ L (T (h z) w)) r :=
    Integrable.mono' (integrable_const C)
      ((hD.comp (hT.clm_apply continuous_const)).comp_aestronglyMeasurable hh)
      (Filter.Eventually.of_forall (fun z => hC _))
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.integral_apply hint,
    ContinuousLinearMap.integral_apply hdi]
  apply integral_congr_ae
  filter_upwards [] with z
  change ((fderiv ℝ L (T (h z) w)).comp ((T (h z)).comp b)) v = _
  rw [hb]
  rfl

omit [CompleteSpace E] [NormedAddCommGroup H] [NormedSpace ℝ H] in

/-- If decoded outputs stay within `gamma` of `theta` and the loss derivative is
`Lambda`-Lipschitz with `Lambda ≥ 0`, an integrable mean derivative has norm at least `g -
Lambda * gamma` whenever `g ≤ ‖fderiv ℝ L theta‖`. -/
theorem meanDerivative_lower_bound
    (r : Measure Z) [IsProbabilityMeasure r] (h : Z → H)
    (T : H → P →L[ℝ] E) (L : E → ℝ) (theta : E) (w : P)
    (Lambda gamma g : ℝ) (hLambda : 0 ≤ Lambda)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hnear : ∀ z, ‖T (h z) w - theta‖ ≤ gamma)
    (hg : g ≤ ‖fderiv ℝ L theta‖)
    (hint : Integrable (fun z => fderiv ℝ L (T (h z) w)) r) :
    g - Lambda * gamma ≤ ‖∫ z, fderiv ℝ L (T (h z) w) ∂r‖ := by
  have hnorm : ‖(∫ z, fderiv ℝ L (T (h z) w) ∂r) - fderiv ℝ L theta‖ ≤
      Lambda * gamma := by
    rw [show (∫ z, fderiv ℝ L (T (h z) w) ∂r) - fderiv ℝ L theta =
      ∫ z, fderiv ℝ L (T (h z) w) - fderiv ℝ L theta ∂r by
        rw [integral_sub hint (integrable_const _)]; simp]
    calc
      ‖∫ z, fderiv ℝ L (T (h z) w) - fderiv ℝ L theta ∂r‖ ≤
          (Lambda * gamma) * r.real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        exact Filter.Eventually.of_forall fun z =>
          (hLip _ _).trans (mul_le_mul_of_nonneg_left (hnear z) hLambda)
      _ = Lambda * gamma := by simp
  have hbase := norm_le_norm_add_norm_sub (∫ z, fderiv ℝ L (T (h z) w) ∂r)
    (fderiv ℝ L theta)
  linarith

/-- Under the stated regularity and concentration hypotheses, a common bias right inverse of
norm at most one gives a bias derivative norm at least `g - Lambda * gamma` and at most the
full population derivative norm. -/
theorem fullDerivative_lower_bound
    (r : Measure Z) [IsProbabilityMeasure r] (h : Z → H)
    (hh : AEStronglyMeasurable h r) (T : H → P →L[ℝ] E) (hT : Continuous T)
    (N : ℝ) (hN : ∀ z, ‖T (h z)‖ ≤ N)
    (L : E → ℝ) (hL : Differentiable ℝ L) (hD : Continuous (fderiv ℝ L))
    (B C : ℝ) (hB : ∀ x, ‖L x‖ ≤ B) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (w : P) (b : E →L[ℝ] P) (hb : ∀ u, (T u).comp b = ContinuousLinearMap.id ℝ E)
    (hbn : ‖b‖ ≤ 1) (theta : E) (Lambda gamma g : ℝ) (hLambda : 0 ≤ Lambda)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hnear : ∀ z, ‖T (h z) w - theta‖ ≤ gamma) (hg : g ≤ ‖fderiv ℝ L theta‖) :
    g - Lambda * gamma ≤ ‖(fderiv ℝ (populationLoss r h T L) w).comp b‖ ∧
      ‖(fderiv ℝ (populationLoss r h T L) w).comp b‖ ≤
        ‖fderiv ℝ (populationLoss r h T L) w‖ := by
  have hdi : Integrable (fun z => fderiv ℝ L (T (h z) w)) r :=
    Integrable.mono' (integrable_const C)
      ((hD.comp (hT.clm_apply continuous_const)).comp_aestronglyMeasurable hh)
      (Filter.Eventually.of_forall (fun z => hC _))
  constructor
  · rw [bias_identity r h hh T hT N hN L hL hD B C hB hC w b hb]
    exact meanDerivative_lower_bound r h T L theta w Lambda gamma g hLambda hLip hnear hg hdi
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using (mul_le_mul_of_nonneg_left hbn
        (norm_nonneg (fderiv ℝ (populationLoss r h T L) w))))

/-- The norm of the native gradient of a real function on a complete real inner-product space
equals the norm of its Fréchet derivative. -/
theorem nativeGradient_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (f : V → ℝ) (x : V) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ V).symm.norm_map _

end Qatlib.Papers.LatentPQCTran26.MainResults.LinearMetaGrad
