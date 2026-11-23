module

public import Qatlib.Papers.DenseOutSim26.FreeTruncation.FiniteL2
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Matrix
open MeasureTheory intervalIntegral
open Set
open scoped Matrix.Norms.L2Operator

namespace QatlibTests.DenseOutSim26FiniteL2Regression

open Qatlib.Papers.DenseOutSim26.FreeTruncation.FiniteL2

example : ‖siteState 0‖ = 1 := siteState_norm 0

example : denseOutputForm (siteState 0) (scaledIdentity 1) = 1 := by
  simpa using scaledIdentity_form 1

/-- The two-site identity curve meets the linear majorant and has a positive
integrated signal, so the top-level bound is applied on a nonempty domain. -/
example :
    ‖∫ t in (0 : ℝ)..1,
        denseOutputForm (siteState 0) (scaledIdentity t)
          - denseOutputForm (siteState 0) (0 : Matrix TwoSite TwoSite ℂ)‖ ≤
      (1 : ℝ) * (1 : ℝ) ^ 2 / (1 : ℝ) ^ (1 : ℝ) := by
  have hcard : 0 < Fintype.card TwoSite := by
    simp [TwoSite, Fintype.card_fin]
  have hcont : ContinuousOn
      (fun t : ℝ => scaledIdentity t - (0 : Matrix TwoSite TwoSite ℂ)) (Icc 0 1) := by
    have hc : Continuous (scaledIdentity : ℝ → Matrix TwoSite TwoSite ℂ) := by
      unfold scaledIdentity
      exact (Complex.continuous_ofReal.smul continuous_const)
    exact (hc.sub continuous_const).continuousOn
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖scaledIdentity t - (0 : Matrix TwoSite TwoSite ℂ)‖ ≤
        (1 : ℝ) * t / (1 : ℝ) ^ (1 : ℝ) := by
    intro t ht
    have hpow : (1 : ℝ) ^ (1 : ℝ) = 1 := Real.one_rpow _
    rw [hpow, one_mul, div_one, sub_zero]
    exact scaledIdentity_l2_le ht.1
  have h := dense_output_l2_light_cone (I := TwoSite) hcard scaledIdentity (fun _ => 0)
    1 1 1 1 zero_le_one zero_lt_one zero_le_one hcont hpt
  exact h.2 (siteState 0) (siteState_norm 0)

example :
    ∫ t in (0 : ℝ)..1, denseOutputForm (siteState 0) (scaledIdentity t) = (1 / 2 : ℂ) := by
  simp_rw [scaledIdentity_form]
  rw [intervalIntegral.integral_ofReal, integral_id]
  norm_num

end QatlibTests.DenseOutSim26FiniteL2Regression
