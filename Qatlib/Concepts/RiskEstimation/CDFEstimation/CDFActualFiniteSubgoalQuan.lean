/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.CDFEstimation.CDFActualFiniteSubgoalStat
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RiskEstimation.CDFEstimation
open Matrix
open scoped Classical BigOperators
set_option warningAsError false
set_option autoImplicit false

theorem riskKet_eq {I : Type} (d e : DecidableEq I) (j : I) : @Qatlib.Foundations.PureStateMath.Ket I d j = @Qatlib.Foundations.PureStateMath.Ket I e j := by
  funext i
  by_cases hi : i = j <;> simp [Qatlib.Foundations.PureStateMath.Ket, hi]

theorem riskCDF_eq {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (t : ℚ) :
    riskCDF A j loss t = ∑ i, BornProb (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i * riskCDFPayoff loss t i := by
  unfold riskCDF
  rw [riskKet_eq (fun a b => Classical.propDecidable (a = b)) inferInstance j]

theorem riskCDFPayoff_bounds {I : Type} (loss : I → ℚ) (t : ℚ) :
    ∀ i, riskCDFPayoff loss t i ∈ Set.Icc (0:ℝ) 1 := by
  intro i; dsimp [riskCDFPayoff]; split <;> norm_num

theorem riskCDF_monotone {I : Type} [Fintype I] (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) :
    Monotone (riskCDF A j loss) := by
  intro t u htu
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (bornProb_nonneg _ _)
  unfold riskCDFPayoff
  by_cases ht : loss i ≤ t
  · simp only [if_pos ht, if_pos (ht.trans htu), le_refl]
  · rw [if_neg ht]; split <;> norm_num

theorem riskCDFActualFinite : CDFActualFiniteSubgoal := by
  intro I _ _ A j loss t hA
  refine ⟨?_, fun u htu => riskCDF_monotone A j loss htu⟩
  rw [riskCDF_eq]
  simpa only [ApplyGate] using!
    (payoff_actual_rotation_and_mean A j (riskCDFPayoff loss t) hA (riskCDFPayoff_bounds loss t)).2
end Qatlib.Concepts.RiskEstimation.CDFEstimation
