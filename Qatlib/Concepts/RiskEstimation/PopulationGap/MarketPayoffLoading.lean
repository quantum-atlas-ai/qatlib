/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.MarketPayoffLoading
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.MonteCarloMean.PayoffEncoding
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

theorem rationalWeight_ideal_born {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < rationalWeightMass w) (a : Option (Fin n)) :
    BornProb (idealWeightPrepare w *ᵥ Ket none) a =
      ((w a / rationalWeightMass w : ℚ) : ℝ) := by
  rw [(rational_weight_ideal_preparation_exact n w hw hZ).2.1]
  simp only [BornProb, rationalWeightTarget, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt]
  exact_mod_cast div_nonneg (hw a) hZ.le

theorem rationalWeight_prepare_payoff_bias {n : ℕ} (w : Option (Fin n) → ℚ) (bits : ℕ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < rationalWeightMass w)
    (f : Option (Fin n) → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    |(∑ a, BornProb (rationalWeightPrepare w bits *ᵥ Ket none) a * f a) -
      ∑ a, ((w a / rationalWeightMass w : ℚ) : ℝ) * f a| ≤
      64 * (n : ℝ) / 2 ^ bits := by
  have hn := rational_weight_numerical_word_unitary_and_error n bits w hw
  have hi := rational_weight_ideal_preparation_exact n w hw hZ
  have hb := empirical_payoff_l2_error
    (rationalWeightPrepare w bits *ᵥ Ket none)
    (idealWeightPrepare w *ᵥ Ket none)
    (normalized_applyGate hn.2.1 (normalized_ket none))
    (normalized_applyGate hi.1 (normalized_ket none)) f hf
  have hop : ‖toEuclidean_fromVec
      (rationalWeightPrepare w bits *ᵥ Ket none - idealWeightPrepare w *ᵥ Ket none)‖ ≤
      ‖rationalWeightPrepare w bits - idealWeightPrepare w‖ := by
    rw [← Matrix.sub_mulVec]
    change ‖toEuclidean_fromVec (ApplyGate
      (rationalWeightPrepare w bits - idealWeightPrepare w) (Ket none))‖ ≤ _
    rw [← toEuclideanCLM_applyGate]
    have h := ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Option (Fin n)) (Option (Fin n)) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Option (Fin n)) →L[ℂ] EuclideanSpace ℂ (Option (Fin n))))
      (rationalWeightPrepare w bits - idealWeightPrepare w)).le_opNorm
      (toEuclidean_fromVec (Ket none))
    simpa only [(normalized_iff_norm_toEuclidean_fromVec (Ket none)).mp (normalized_ket none),
      mul_one, Matrix.l2_opNorm_def] using! h
  have he : ‖rationalWeightPrepare w bits - idealWeightPrepare w‖ ≤
      32 * (n : ℝ) / 2 ^ bits := hn.2.2
  have hideal : (∑ a, BornProb (idealWeightPrepare w *ᵥ Ket none) a * f a) =
      ∑ a, ((w a / rationalWeightMass w : ℚ) : ℝ) * f a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [rationalWeight_ideal_born w hw hZ a]
  rw [← hideal]
  calc
    _ ≤ 2 * ‖toEuclidean_fromVec
      (rationalWeightPrepare w bits *ᵥ Ket none - idealWeightPrepare w *ᵥ Ket none)‖ := hb
    _ ≤ 2 * ‖rationalWeightPrepare w bits - idealWeightPrepare w‖ := by linarith
    _ ≤ 2 * (32 * (n : ℝ) / 2 ^ bits) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem marketPayoffLoading : MarketPayoffLoading := by
  intro n bits payoffBits w loss hw hZ hloss
  have hn := rational_weight_numerical_word_unitary_and_error n bits w hw
  have hc := rational_weight_data_ranges_and_actual_comparisons n bits w hw
  refine ⟨hn.2.1, hn.2.2, hc.2.2, ?_, ?_⟩
  · intro t
    rw [riskCDF_eq]
    exact rationalWeight_prepare_payoff_bias w bits hw hZ (riskCDFPayoff loss t)
      (riskCDFPayoff_bounds loss t)
  · intro t
    have htail := riskTailPayoff_bounds loss t hloss
    have hval := rational_payoff_weighted_bias (rationalWeightPrepare w bits) none
      (riskTailPayoff loss t) payoffBits hn.2.1 htail
    have hprep := rationalWeight_prepare_payoff_bias w bits hw hZ
      (fun a => (riskTailPayoff loss t a : ℝ))
      (fun a => by (try dsimp only); exact ⟨by exact_mod_cast (htail a).1, by exact_mod_cast (htail a).2⟩)
    have htri := abs_sub_le
      (∑ i, BornProb (rationalWeightPrepare w bits *ᵥ Ket none) i *
        (rationalPayoffValue (riskTailPayoff loss t i) payoffBits : ℝ))
      (∑ i, BornProb (rationalWeightPrepare w bits *ᵥ Ket none) i *
        (riskTailPayoff loss t i : ℝ))
      (∑ a, ((w a / rationalWeightMass w : ℚ) : ℝ) * (riskTailPayoff loss t a : ℝ))
    linarith

end Qatlib.Concepts.RiskEstimation.PopulationGap
