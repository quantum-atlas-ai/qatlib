/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.LowerTarget
import Qatlib.Papers.QAOAScaling23.BiasedProcess.CompletionRow
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Born

theorem option_fiber_event {A B C : Type} [Fintype B] (p : PMF A) (label : A → Option B)
    (f : B → Option C) (j : C) :
    event p (fun a => (label a).bind f = some j) =
      ∑ i, if f i = some j then event p (fun a => label a = some i) else 0 := by
  classical
  have he (a : A) : (@ite ℝ≥0∞ ((label a).bind f = some j) (Classical.propDecidable _) 1 0) =
      ∑ i, if f i = some j then (@ite ℝ≥0∞ (label a = some i) (Classical.propDecidable _) 1 0) else 0 := by
    cases h : label a with
    | none => simp
    | some i =>
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
  refine (event_eq p _).trans ?_
  refine (expectation_congr he).trans ?_
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f i = some j <;> simp [hi,event]

theorem option_success_sum {A B : Type} [Fintype B] (p : PMF A) (label : A → Option B) :
    event p (fun a => (label a).isSome) = ∑ j, event p (fun a => label a = some j) := by
  classical
  have he (a : A) : (@ite ℝ≥0∞ ((label a).isSome = true) (Classical.propDecidable _) 1 0) =
      ∑ j, @ite ℝ≥0∞ (label a = some j) (Classical.propDecidable _) 1 0 := by
    cases h : label a with
    | none => simp
    | some j => simp
  exact (event_eq p _).trans ((expectation_congr he).trans (expectation_sum p Finset.univ _))
variable {I : Type} [Fintype I] [DecidableEq I]

def classOutput (cost : I → ℝ) (current : I) (tr : CappedSearchTrace I) :
    Option (Fin (costRank cost current).val) :=
  tr.result.bind (lowerRank cost (costRank cost current).val)
omit [DecidableEq I] in

theorem lowerRank_eq_class (cost : I → ℝ) (current i : I) (j : Fin (costRank cost current).val) :
    lowerRank cost (costRank cost current).val i = some j ↔
      costRank cost i = ⟨j.val,lt_trans j.isLt (costRank cost current).isLt⟩ := by
  rw [lowerRank_some,Fin.ext_iff]

theorem target_born_point (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (costRank cost current).val)
    (j : Fin (costRank cost current).val) :
    lowerClassLaw cost (preparedLaw U hU seed) _ (costRank cost current).isLt.le hpos j =
      ∑ i, if lowerRank cost (costRank cost current).val i = some j then
        ENNReal.ofReal (BornProb (preparedAAState U seed) i / MeasureProb (preparedAAState U seed) (strictMarked cost current)) else 0 := by
  change ENNReal.ofReal _ = _
  simp_rw [lowerRank_eq_class]
  rw [costClassLaw_real_fiber]
  simp_rw [preparedLaw_real]
  rw [← strict_mass_prefix,Finset.sum_div]
  have he (i : I) : (if costRank cost i = ⟨j.val,lt_trans j.isLt (costRank cost current).isLt⟩ then
      BornProb (preparedAAState U seed) i else 0) / MeasureProb (preparedAAState U seed) (strictMarked cost current) =
      if costRank cost i = ⟨j.val,lt_trans j.isLt (costRank cost current).isLt⟩ then
        BornProb (preparedAAState U seed) i / MeasureProb (preparedAAState U seed) (strictMarked cost current) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    split_ifs
    · exact div_nonneg (bornProb_nonneg _ _) (by rw [strict_mass_prefix];exact hpos.le)
    · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem native_class_point (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (costRank cost current).val)
    (ms : List ℕ) (j : Fin (costRank cost current).val) :
    let p :=
        searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) (1::ms)
    event p (fun tr => classOutput cost current tr = some j) =
      event p (fun tr => tr.result.isSome) *
        lowerClassLaw cost (preparedLaw U hU seed) _ (costRank cost current).isLt.le hpos j := by
  (try dsimp only)
  simp only [classOutput]
  rw [option_fiber_event,target_born_point,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : lowerRank cost (costRank cost current).val i = some j
  · rw [if_pos hi,if_pos hi]
    have hlt : costRank cost i < costRank cost current := by
      have he := (lowerRank_some cost _ i j).mp hi
      change (costRank cost i).val < (costRank cost current).val
      rw [he]
      exact j.isLt
    have him : i ∈ strictMarked cost current := by
      simpa [strictMarked] using (costRank_lt_iff cost i current).mp hlt
    apply Qatlib.Papers.QAOAScaling23.SearchPrimitive.native_positive_mass_biased_law U hU seed _ _ (strictValid_correct cost current)
      (by rwa [strict_mass_prefix]) (strict_mass_le_one U hU seed cost current) ms i him
  · simp [hi]

theorem native_class_success (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I)
    (hpos : 0 < prefixSum (weights cost (preparedLaw U hU seed)) (costRank cost current).val)
    (ms : List ℕ) :
    let p :=
        searchForSchedule U hU seed (strictMarked cost current) (strictValid cost current) (1::ms)
    event p (fun tr => (classOutput cost current tr).isSome) = event p (fun tr => tr.result.isSome) := by
  (try dsimp only)
  rw [option_success_sum]
  simp_rw [native_class_point U hU seed cost current hpos ms]
  rw [← Finset.mul_sum]
  have hs :=
      (lowerClassLaw cost (preparedLaw U hU seed) _ (costRank cost current).isLt.le hpos).tsum_coe
  rw [tsum_fintype] at hs
  rw [hs,mul_one]
end Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
