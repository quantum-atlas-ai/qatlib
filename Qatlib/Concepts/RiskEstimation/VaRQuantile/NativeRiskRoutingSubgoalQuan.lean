/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.NativeRiskRoutingSubgoalStat
import Qatlib.Concepts.RiskEstimation.CDFEstimation.NativeCDFReadoutRestrictedQuan

/-!
# Transport of rational quantile routing

This module identifies rational-valued bisection with `riskBisect` after casting the sample
values and target to the reals. `riskNativeRouting` also bounds the recorded number of calls by
the fuel. These results connect rational readout to the bisection procedure of
[WoernerEgger2019].

## Main statements

* `risk_native_bisect_transport`: equality of the rational and real search laws.
* `riskNativeRouting`: the transport identity together with the support call bound.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open scoped Classical ENNReal

/-- Rational bisection agrees with real bisection after casting the samples and target from the
rationals to the reals. -/
theorem risk_native_bisect_transport (sampler : ℚ → PMF ℚ) (xs : List ℚ) (q : ℚ)
    (fuel lo hi : ℕ) :
    riskNativeBisect sampler xs q fuel lo hi =
      riskBisect (fun t => PMF.map (fun z : ℚ => (z : ℝ)) (sampler t)) xs (q : ℝ) fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    by_cases hstop : hi ≤ lo
    · simp only [riskNativeBisect, riskBisect, if_pos hstop]
    · conv_lhs =>
        unfold riskNativeBisect
        simp only [if_neg hstop]
      change (sampler (xs.getD ((lo+hi)/2) 0)).bind (fun z =>
          (if q ≤ z then riskNativeBisect sampler xs q fuel lo ((lo+hi)/2)
            else riskNativeBisect sampler xs q fuel ((lo+hi)/2+1) hi).map
              (fun out => (out.1,out.2+1))) = _
      rw [riskBisect, if_neg hstop]
      rw [PMF.bind_map (sampler (xs.getD ((lo+hi)/2) 0)) (fun z : ℚ => (z : ℝ))]
      apply congrArg (fun f : ℚ → PMF (ℕ × ℕ) => (sampler (xs.getD ((lo+hi)/2) 0)).bind f)
      funext z
      simp only [Function.comp_apply, Rat.cast_le]
      split_ifs <;> rw [← ih]

/-- The rational bisection law agrees with its real-valued transport and records at most the
supplied fuel in calls. This supplies the rational routing step for the value-at-risk search
of [Woerner and Egger, Section II][WoernerEgger2019]. -/
theorem riskNativeRouting : NativeRiskRoutingSubgoal := by
  intro sampler xs q fuel lo hi
  change riskNativeBisect sampler xs q fuel lo hi = _ ∧ _
  have ht := risk_native_bisect_transport sampler xs q fuel lo hi
  refine ⟨?_, ?_⟩
  · simpa only [PMF.map, Function.comp_def, PMF.bind_pure] using! ht
  change ∀ z ∈ (riskNativeBisect sampler xs q fuel lo hi).support, z.2 ≤ fuel
  rw [ht]
  exact riskBisect_support_calls _ _ _ _ _ _

end Qatlib.Concepts.RiskEstimation.VaRQuantile
