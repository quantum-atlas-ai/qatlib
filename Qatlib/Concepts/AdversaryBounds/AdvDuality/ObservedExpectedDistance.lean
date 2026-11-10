/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedExpectedHybridDefs
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

private theorem list_cauchy_sq {α : Type*} (xs : List α) (f g : α → ℝ) :
    ((xs.map fun x => f x * g x).sum) ^ 2 ≤
      (xs.map fun x => f x ^ 2).sum * (xs.map fun x => g x ^ 2).sum := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin xs.length))
    (fun i => f xs[i.val]) (fun i => g xs[i.val])
  simpa only [← List.sum_ofFn,
    List.ofFn_getElem_eq_map xs (fun x => f x * g x),
    List.ofFn_getElem_eq_map xs (fun x => f x ^ 2),
    List.ofFn_getElem_eq_map xs (fun x => g x ^ 2)] using h

private theorem re_list_sum (xs : List ℂ) :
    xs.sum.re = (xs.map Complex.re).sum := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
    simp only [List.sum_cons, List.map_cons, Complex.add_re, ih]

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem mass_eq_euclidean_sq (v : QState I) :
    branchMass v = ‖toEuclidean_fromVec v‖ ^ 2 := by
  simp only [branchMass, MeasureProb, BornProb, norm_toEuclidean_fromVec_sq]

private theorem euclidean_sub_sq (v w : QState I) :
    ‖toEuclidean_fromVec (v - w)‖ ^ 2 =
      ‖toEuclidean_fromVec v‖ ^ 2 + ‖toEuclidean_fromVec w‖ ^ 2 -
        2 * (Inner v w).re := by
  rw [show toEuclidean_fromVec (v - w) =
      toEuclidean_fromVec v - toEuclidean_fromVec w from rfl,
    norm_sub_sq (𝕜 := ℂ), inner_euclidean_fromVec]
  change ‖toEuclidean_fromVec v‖ ^ 2 - 2 * (Inner v w).re +
    ‖toEuclidean_fromVec w‖ ^ 2 = _
  ring

private theorem paired_distance_identity (ts : List (BranchTrace I × BranchTrace I)) :
    (ts.map fun t => ‖toEuclidean_fromVec (t.1.state - t.2.state)‖ ^ 2).sum =
      (ts.map fun t => ‖toEuclidean_fromVec t.1.state‖ ^ 2).sum +
      (ts.map fun t => ‖toEuclidean_fromVec t.2.state‖ ^ 2).sum -
      2 * (ts.map fun t => (Inner t.1.state t.2.state).re).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, euclidean_sub_sq]
    ring

private theorem query_inner_change_le (A B : Matrix I I ℂ)
    (hB : B ∈ Matrix.unitaryGroup I ℂ) (v w : QState I) :
    ‖Inner (ApplyGate A v) (ApplyGate B w) - Inner v w‖ ≤
      ‖A - B‖ * ‖toEuclidean_fromVec v‖ * ‖toEuclidean_fromVec w‖ := by
  have he : Inner (ApplyGate A v) (ApplyGate B w) - Inner v w =
      Inner (ApplyGate (A - B) v) (ApplyGate B w) := by
    rw [← inner_applyGate hB v w]
    rw [← inner_euclidean_fromVec, ← inner_euclidean_fromVec,
      ← inner_euclidean_fromVec, ← inner_sub_left]
    congr 1
    change toEuclidean_fromVec (A *ᵥ v - B *ᵥ v) =
      toEuclidean_fromVec ((A - B) *ᵥ v)
    rw [Matrix.sub_mulVec]
  rw [he, ← inner_euclidean_fromVec]
  calc
    _ ≤ ‖toEuclidean_fromVec (ApplyGate (A - B) v)‖ *
        ‖toEuclidean_fromVec (ApplyGate B w)‖ := norm_inner_le_norm _ _
    _ ≤ (‖A - B‖ * ‖toEuclidean_fromVec v‖) * ‖toEuclidean_fromVec w‖ := by
      rw [norm_applyGate_of_mem_unitaryGroup hB]
      exact mul_le_mul_of_nonneg_right (norm_applyGate_le (A - B) v) (norm_nonneg _)
    _ = _ := rfl

theorem observed_paired_expected_distance
    (A B : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hB : B ∈ Matrix.unitaryGroup I ℂ)
    (hP : observedWellFormed P) (hψ : Normalized ψ) :
    ((observedPairedTraces A B P ψ ψ).map fun t =>
      ‖toEuclidean_fromVec (t.1.state - t.2.state)‖ ^ 2).sum ≤
      2 * ‖A - B‖ * Real.sqrt
        (expectedObservedQueries A P ψ * expectedObservedQueries B P ψ) := by
  let ts := observedPairedTraces A B P ψ ψ
  let vs := observedPairedVisits A B P ψ ψ
  let err := fun v : QState I × QState I =>
    Inner (ApplyGate A v.1) (ApplyGate B v.2) - Inner v.1 v.2
  let S := (vs.map fun v =>
    ‖toEuclidean_fromVec v.1‖ * ‖toEuclidean_fromVec v.2‖).sum
  have hleft : (ts.map fun t => ‖toEuclidean_fromVec t.1.state‖ ^ 2).sum = 1 := by
    have h := congrArg
      (fun xs : List (BranchTrace I) => (xs.map fun t => branchMass t.state).sum)
      (observedPairedTraces_left A B P ψ ψ)
    simp only [List.map_map, Function.comp_def] at h
    rw [observedTraces_mass A hA P hP ψ] at h
    simpa only [mass_eq_euclidean_sq,
      (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, one_pow] using h
  have hright : (ts.map fun t => ‖toEuclidean_fromVec t.2.state‖ ^ 2).sum = 1 := by
    have h := congrArg
      (fun xs : List (BranchTrace I) => (xs.map fun t => branchMass t.state).sum)
      (observedPairedTraces_right A B P ψ ψ)
    simp only [List.map_map, Function.comp_def] at h
    rw [observedTraces_mass B hB P hP ψ] at h
    simpa only [mass_eq_euclidean_sq,
      (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, one_pow] using h
  have hvisitA : (vs.map fun v => ‖toEuclidean_fromVec v.1‖ ^ 2).sum =
      expectedObservedQueries A P ψ := by
    have h := congrArg (fun xs : List (QState I) => (xs.map branchMass).sum)
      (observedPairedVisits_left A B P ψ ψ)
    simp only [List.map_map, Function.comp_def] at h
    rw [observedQueryVisits_mass A hA P hP ψ] at h
    simpa only [mass_eq_euclidean_sq] using h
  have hvisitB : (vs.map fun v => ‖toEuclidean_fromVec v.2‖ ^ 2).sum =
      expectedObservedQueries B P ψ := by
    have h := congrArg (fun xs : List (QState I) => (xs.map branchMass).sum)
      (observedPairedVisits_right A B P ψ ψ)
    simp only [List.map_map, Function.comp_def] at h
    rw [observedQueryVisits_mass B hB P hP ψ] at h
    simpa only [mass_eq_euclidean_sq] using h
  have hcs : S ^ 2 ≤ expectedObservedQueries A P ψ * expectedObservedQueries B P ψ := by
    have h := list_cauchy_sq vs (fun v => ‖toEuclidean_fromVec v.1‖)
      (fun v => ‖toEuclidean_fromVec v.2‖)
    rwa [hvisitA, hvisitB] at h
  have hroot : S ≤ Real.sqrt
      (expectedObservedQueries A P ψ * expectedObservedQueries B P ψ) :=
    Real.le_sqrt_of_sq_le hcs
  have ht := congrArg Complex.re (observed_paired_inner_telescope A B P hP ψ ψ)
  rw [(normalized_iff_inner_self ψ).mp hψ] at ht
  simp only [Complex.add_re, Complex.one_re, re_list_sum, List.map_map,
    Function.comp_def] at ht
  have hnegative (v : QState I × QState I) :
      -(err v).re ≤ ‖A - B‖ *
        (‖toEuclidean_fromVec v.1‖ * ‖toEuclidean_fromVec v.2‖) := by
    calc
      _ ≤ ‖err v‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ ≤ _ := by
        simpa only [err, mul_assoc] using query_inner_change_le A B hB v.1 v.2
  have hsum : -(vs.map fun v => (err v).re).sum ≤ ‖A - B‖ * S := by
    dsimp only [S]
    induction vs with
    | nil => simp
    | cons v vs ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      nlinarith [hnegative v]
  have hd := paired_distance_identity ts
  rw [hleft, hright] at hd
  have hbound : (ts.map fun t =>
      ‖toEuclidean_fromVec (t.1.state - t.2.state)‖ ^ 2).sum ≤
      2 * ‖A - B‖ * S := by
    change (ts.map fun t => (Inner t.1.state t.2.state).re).sum =
      1 + (vs.map fun v => (err v).re).sum at ht
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left hroot
    (mul_nonneg (by norm_num) (norm_nonneg _)))

end Qatlib.Concepts.AdversaryBounds.AdvDuality
