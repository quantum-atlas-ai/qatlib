/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.GcMatchingLowerBoundStat
public import Qatlib.Concepts.GraphQuery.GcBaselines.AdversaryStar

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GraphQuery.EdgeQuery
open Qatlib.Concepts.AdversaryBounds.AdvWitness
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.GraphQuery.GcBaselines

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def matchingStarInput (n : ℕ) : Option (Fin (n / 2)) → Fin n → Bool
  | none, _ => false
  | some e, i => decide (i.val = 2 * e.val ∨ i.val = 2 * e.val + 1)

/-- Shows that the matching star input has a graph collision exactly when its index is present. -/
private theorem matchingStarInput_collision (n : ℕ) (x : Option (Fin (n / 2))) :
    graphCollision (matchingAdj n) (matchingStarInput n x) = x.isSome := by
  cases x with
  | none => simp [graphCollision, matchingStarInput]
  | some e =>
    have hu : 2 * e.val < n := by omega
    have hv : 2 * e.val + 1 < n := by omega
    apply decide_eq_true
    refine ⟨⟨2 * e.val, hu⟩, ⟨2 * e.val + 1, hv⟩, ?_, ?_, ?_⟩
    · simp [matchingAdj]
    · simp [matchingStarInput]
    · simp [matchingStarInput]

/-- Bounds the matching star adversary filter bound by one. -/
private theorem matchingStar_filter (n : ℕ) :
    advFilterBound (matchingStarInput n) (advStarGamma (n / 2)) ≤ 1 := by
  apply starFilterBound_le _ 1 (by norm_num)
  intro i
  let S := Finset.univ.filter (fun e : Fin (n / 2) =>
    matchingStarInput n (some e) i ≠ matchingStarInput n none i)
  have hc : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    have he' : i.val = 2 * e.val ∨ i.val = 2 * e.val + 1 := by
      have h := (Finset.mem_filter.mp he).2
      by_contra hn
      exact h (by simp [matchingStarInput, hn])
    have hf' : i.val = 2 * f.val ∨ i.val = 2 * f.val + 1 := by
      have h := (Finset.mem_filter.mp hf).2
      by_contra hn
      exact h (by simp [matchingStarInput, hn])
    apply Fin.ext
    omega
  have h := starFilter_norm_le (matchingStarInput n) i
  have hs := Real.sqrt_le_sqrt (show (S.card : ℝ) ≤ 1 by exact_mod_cast hc)
  exact h.trans (by simpa using hs)

/-- Establishes the graph collision lower bound for matchings in `GcMatchingLowerBound`. -/
theorem gcMatchingLowerBound : GcMatchingLowerBound := by
  intro n W _ _ C ψ E hC hψ hsuccess
  by_cases hm : n / 2 = 0
  · simp only [hm, Nat.cast_zero, Real.sqrt_zero, mul_zero]
    positivity
  have hmpos : 0 < n / 2 := Nat.pos_of_ne_zero hm
  have hw := negative_adversary_star_actual_search_witness (n / 2) hmpos
  have hs : ∀ x : Option (Fin (n / 2)), 1 - (1 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) (matchingStarInput n x)) C ψ)
        (if x.isSome then E else Eᶜ) := by
    intro x
    have h := hsuccess (matchingStarInput n x)
    rw [matchingStarInput_collision] at h
    convert! h using 1
    norm_num
  have h := negative_adversary_actual_bounded_error_circuit_lower_bound
    (Option (Fin (n / 2))) W n (matchingStarInput n) (advStarGamma (n / 2))
    Option.isSome C ψ E (1 / 3) hw.1 hw.2.2.2.1 hC hψ (by norm_num) (by norm_num) hs
  rw [hw.2.1] at h
  have hb := mul_le_mul_of_nonneg_left (matchingStar_filter n)
    (by positivity : 0 ≤ 2 * (QueryCount C : ℝ))
  have hf := h.trans (by simpa only [mul_one] using hb)
  convert! hf using 1
  norm_num

end Qatlib.Concepts.GraphQuery.GcBaselines
