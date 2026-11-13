/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.LowerTarget
import Qatlib.Papers.QAOAScaling23.BiasedProcess.CompletionRow

/-!
# Cost-class marginals of native threshold search

This module aggregates optional candidate outputs into lower cost-class outputs. It identifies
the target class law with normalized Born fiber masses and proves that native scheduled search
preserves this class distribution conditional on success, as required for the biased process
associated with [ShaydulinEtAl2024].

## Main statements

* `target_born_point`: A conditional lower-class probability is the sum of the normalized
  prepared Born masses of the candidate labels in that class.
* `native_class_point`: The native scheduled search's probability of a specified lower-class
  output equals its total success probability times the conditional lower-class probability.
* `native_class_success`: For native scheduled search, extracting the lower-class output
  preserves the probability that the candidate result is present.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

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

/-- The probability that an optional label followed by an optional map yields `j` is the sum of
the original label-event probabilities over the fiber yielding `j`. -/
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

/-- The probability that an optional label is present equals the sum of its point-output event
probabilities over a finite label type. -/
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

/-- The optional lower cost-class rank obtained from a search receipt's candidate result
relative to the current rank. -/
def classOutput (cost : I → ℝ) (current : I) (tr : CappedSearchTrace I) :
    Option (Fin (costRank cost current).val) :=
  tr.result.bind (lowerRank cost (costRank cost current).val)
omit [DecidableEq I] in

/-- Returning `j` through the lower-rank map is equivalent to the candidate having the
corresponding full cost-class rank. -/
theorem lowerRank_eq_class (cost : I → ℝ) (current i : I) (j : Fin (costRank cost current).val) :
    lowerRank cost (costRank cost current).val i = some j ↔
      costRank cost i = ⟨j.val,lt_trans j.isLt (costRank cost current).isLt⟩ := by
  rw [lowerRank_some,Fin.ext_iff]

/-- A conditional lower-class probability is the sum of the normalized prepared Born masses of
the candidate labels in that class. -/
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

/-- The native scheduled search's probability of a specified lower-class output equals its total
success probability times the conditional lower-class probability. -/
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

/-- For native scheduled search, extracting the lower-class output preserves the probability
that the candidate result is present. -/
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
