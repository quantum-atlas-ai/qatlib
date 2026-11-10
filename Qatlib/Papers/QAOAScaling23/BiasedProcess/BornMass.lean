/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeOracle
import Qatlib.Papers.QAOAScaling23.BiasedProcess.ClassMass
import Qatlib.Papers.QAOAScaling23.SearchPrimitive.NativeMassLaw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
variable {I : Type} [Fintype I] [DecidableEq I]

theorem prepared_normalized (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I) :
    Normalized (preparedAAState U seed) := normalized_applyGate hU (normalized_ket seed)

def preparedLaw (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I) : PMF I :=
  bornDistribution (preparedAAState U seed) (prepared_normalized U hU seed)

theorem preparedLaw_real (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I) (i : I) :
    (preparedLaw U hU seed i).toReal = BornProb (preparedAAState U seed) i := by
  exact ENNReal.toReal_ofReal (bornProb_nonneg _ _)

theorem strict_mass_prefix (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) :
    MeasureProb (preparedAAState U seed) (strictMarked cost current) =
      prefixSum (weights cost (preparedLaw U hU seed)) (costRank cost current).val := by
  rw [prefix_labels cost _ _ (costRank cost current).isLt.le]
  simp_rw [preparedLaw_real]
  simp only [MeasureProb,strictMarked,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  exact if_congr (costRank_lt_iff cost i current).symm rfl rfl

theorem optimal_le_strict_mass (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (hr : 0 < (costRank cost current).val) :
    weights cost (preparedLaw U hU seed) 0 ≤ MeasureProb (preparedAAState U seed) (strictMarked cost current) := by
  rw [strict_mass_prefix]
  exact optimal_le_prefix cost _ _ hr

theorem strict_mass_pos (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (hr : 0 < (costRank cost current).val)
    (h0 : 0 < weights cost (preparedLaw U hU seed) 0) :
    0 < MeasureProb (preparedAAState U seed) (strictMarked cost current) :=
  h0.trans_le (optimal_le_strict_mass U hU seed cost current hr)

theorem strict_mass_le_one (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) :
    MeasureProb (preparedAAState U seed) (strictMarked cost current) ≤ 1 :=
  Qatlib.Foundations.BornMetrics.EventProbability.measureProb_le_one (prepared_normalized U hU seed) _

theorem optimal_cap (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (hr : 0 < (costRank cost current).val)
    (h0 : 0 < weights cost (preparedLaw U hU seed) 0) (M : ℕ)
    (hM : 1 / Real.sqrt (weights cost (preparedLaw U hU seed) 0) ≤ (M : ℝ)) :
    1 ≤ (M : ℝ) * Real.sqrt (MeasureProb (preparedAAState U seed) (strictMarked cost current)) := by
  have hs : 0 < Real.sqrt (weights cost (preparedLaw U hU seed) 0) := Real.sqrt_pos.mpr h0
  have hb : 1 ≤ (M : ℝ) * Real.sqrt (weights cost (preparedLaw U hU seed) 0) :=
    (div_le_iff₀ hs).mp hM
  exact hb.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (optimal_le_strict_mass U hU seed cost current hr)) (Nat.cast_nonneg M))
omit [DecidableEq I] in

theorem classes_le_bit_bound (cost : I → ℝ) (N : ℕ) (hN : Fintype.card I ≤ 2^N) :
    (costLevels cost).card ≤ 2^N := (classes_card_le cost).trans hN
end Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
