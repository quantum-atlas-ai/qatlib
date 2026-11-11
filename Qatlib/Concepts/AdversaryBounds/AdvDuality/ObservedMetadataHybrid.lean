/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedExpectedHybridDefs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn

/-!
# Metadata scores from paired state distance

`observed_metadata_score_sq_le_distance` converts paired terminal state distance into a bound on
the difference of `observedMetadataScore` values. The score may depend on acceptance and the
complete outcome record, provided its absolute value is at most one. This connects classical
branch statistics to the state distinguishability viewpoint discussed in [Watrous2018].

The proof first bounds a single scored difference of squared norms, then sums with
Cauchy--Schwarz. Normalization of both executions and agreement of paired metadata yield the
final factor of four.

## Main statements

* `metadata_leaf_bound` controls a scored difference of squared norms for one pair.
* `metadata_list_score_sq` bounds the squared total score difference for normalized families.
* `observed_metadata_score_sq_le_distance` applies this estimate to unitary oracle executions of
  a well-formed circuit.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- The square of a real list sum of products is bounded by the product of the corresponding
sums of squares. -/
private theorem metadata_list_cauchy {α : Type*} (xs : List α) (f g : α → ℝ) :
    ((xs.map fun x => f x * g x).sum) ^ 2 ≤
      (xs.map fun x => f x ^ 2).sum * (xs.map fun x => g x ^ 2).sum := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin xs.length))
    (fun i => f xs[i.val]) (fun i => g xs[i.val])
  simpa only [← List.sum_ofFn,
    List.ofFn_getElem_eq_map xs (fun x => f x * g x),
    List.ofFn_getElem_eq_map xs (fun x => f x ^ 2),
    List.ofFn_getElem_eq_map xs (fun x => g x ^ 2)] using h

/-- Summing pointwise differences over a list equals the difference of the two list sums. -/
private theorem metadata_sum_sub {α : Type*} (xs : List α) (f g : α → ℝ) :
    (xs.map fun x => f x - g x).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- A pointwise inequality on elements of a list gives the corresponding inequality between
mapped sums. -/
private theorem metadata_sum_mono {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem x hy))

/-- The absolute value of a real list sum is at most the sum of the absolute values of its
terms. -/
private theorem metadata_abs_sum_le {α : Type*} (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map fun x => |f x|).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)

/-- A difference of squared norms multiplied by a score of absolute value at most one is bounded
in absolute value by the distance times the sum of the norms. -/
private theorem metadata_leaf_bound {E : Type*} [NormedAddCommGroup E]
    (u v : E) (c : ℝ) (hc : |c| ≤ 1) :
    |c * (‖u‖ ^ 2 - ‖v‖ ^ 2)| ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  rw [abs_mul, sq_sub_sq, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hdiff := abs_norm_sub_norm_le u v
  have hplus := add_nonneg (norm_nonneg u) (norm_nonneg v)
  calc
    |c| * ((‖u‖ + ‖v‖) * |‖u‖ - ‖v‖|) =
        |c| * (|‖u‖ - ‖v‖| * (‖u‖ + ‖v‖)) := by ring
    |c| * (|‖u‖ - ‖v‖| * (‖u‖ + ‖v‖)) ≤
        1 * (‖u - v‖ * (‖u‖ + ‖v‖)) :=
      mul_le_mul hc (mul_le_mul_of_nonneg_right hdiff hplus)
        (mul_nonneg (abs_nonneg _) hplus) zero_le_one
    _ = _ := one_mul _

/-- For two families whose squared norms each sum to one, a bounded score's squared weighted
mass difference is at most four times the total squared distance. -/
private theorem metadata_list_score_sq {α E : Type*} [NormedAddCommGroup E]
    (xs : List α) (u v : α → E) (score : α → ℝ)
    (hscore : ∀ x ∈ xs, |score x| ≤ 1)
    (hu : (xs.map fun x => ‖u x‖ ^ 2).sum = 1)
    (hv : (xs.map fun x => ‖v x‖ ^ 2).sum = 1) :
    ((xs.map fun x => score x * (‖u x‖ ^ 2 - ‖v x‖ ^ 2)).sum) ^ 2 ≤
      4 * (xs.map fun x => ‖u x - v x‖ ^ 2).sum := by
  let f := fun x => score x * (‖u x‖ ^ 2 - ‖v x‖ ^ 2)
  let a := fun x => ‖u x - v x‖
  let b := fun x => ‖u x‖ + ‖v x‖
  have habs : |(xs.map f).sum| ≤ (xs.map fun x => a x * b x).sum :=
    (metadata_abs_sum_le xs f).trans
      (metadata_sum_mono xs _ _ fun x hx => metadata_leaf_bound _ _ _ (hscore x hx))
  have hnonneg : 0 ≤ (xs.map fun x => a x * b x).sum :=
    List.sum_nonneg (by
      intro r hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      exact mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hsquare : (xs.map f).sum ^ 2 ≤ (xs.map fun x => a x * b x).sum ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (xs.map f).sum) habs 2
    simpa only [sq_abs] using h
  have hlinear : (xs.map fun x => 2 * ‖u x‖ ^ 2 + 2 * ‖v x‖ ^ 2).sum =
      2 * (xs.map fun x => ‖u x‖ ^ 2).sum +
        2 * (xs.map fun x => ‖v x‖ ^ 2).sum := by
    clear hscore hu hv habs hnonneg hsquare
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  have hb : (xs.map fun x => b x ^ 2).sum ≤ 4 := by
    calc
      _ ≤ (xs.map fun x => 2 * ‖u x‖ ^ 2 + 2 * ‖v x‖ ^ 2).sum :=
        metadata_sum_mono xs _ _ (by
          intro x _
          dsimp only [b]
          nlinarith [sq_nonneg (‖u x‖ - ‖v x‖)])
      _ = 4 := by rw [hlinear, hu, hv]; norm_num
  have ha : 0 ≤ (xs.map fun x => a x ^ 2).sum :=
    List.sum_nonneg (by
      intro r hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      exact sq_nonneg _)
  have hcs := metadata_list_cauchy xs a b
  have hfinal := mul_le_mul_of_nonneg_left hb ha
  change (xs.map f).sum ^ 2 ≤ 4 * (xs.map fun x => a x ^ 2).sum
  nlinarith

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The mass of a pure branch equals the squared Euclidean norm of its state vector. -/
private theorem metadata_mass_norm (ψ : QState I) :
    branchMass ψ = ‖toEuclidean_fromVec ψ‖ ^ 2 := by
  change (∑ i, ‖ψ i‖ ^ 2) = _
  exact (norm_toEuclidean_fromVec_sq ψ).symm

/-- For two unitary oracle executions of a well-formed circuit from a normalized common input, a
metadata score bounded in absolute value by one has squared expectation difference at most
four times total paired squared terminal distance. -/
theorem observed_metadata_score_sq_le_distance
    (A B : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hB : B ∈ Matrix.unitaryGroup I ℂ)
    (hP : observedWellFormed P) (hψ : Normalized ψ)
    (score : Bool → List (ℕ × ℕ) → ℝ)
    (hscore : ∀ b record, |score b record| ≤ 1) :
    (observedMetadataScore A P ψ score - observedMetadataScore B P ψ score) ^ 2 ≤
      4 * ((observedPairedTraces A B P ψ ψ).map fun t =>
        ‖toEuclidean_fromVec (t.1.state - t.2.state)‖ ^ 2).sum := by
  let xs := observedPairedTraces A B P ψ ψ
  let u := fun t : BranchTrace I × BranchTrace I => toEuclidean_fromVec t.1.state
  let v := fun t : BranchTrace I × BranchTrace I => toEuclidean_fromVec t.2.state
  let c := fun t : BranchTrace I × BranchTrace I => score t.1.accepted t.1.outcomes
  have hleft := congrArg (fun ts : List (BranchTrace I) =>
      (ts.map fun t => branchMass t.state).sum) (observedPairedTraces_left A B P ψ ψ)
  have hright := congrArg (fun ts : List (BranchTrace I) =>
      (ts.map fun t => branchMass t.state).sum) (observedPairedTraces_right A B P ψ ψ)
  simp only [List.map_map, Function.comp_def, metadata_mass_norm] at hleft hright
  have hu : (xs.map fun t => ‖u t‖ ^ 2).sum = 1 := by
    exact hleft.trans (by simpa only [metadata_mass_norm] using
      observedTraces_mass_eq_one A hA P hP hψ)
  have hv : (xs.map fun t => ‖v t‖ ^ 2).sum = 1 := by
    exact hright.trans (by simpa only [metadata_mass_norm] using
      observedTraces_mass_eq_one B hB P hP hψ)
  have hstatA := congrArg (fun ts : List (BranchTrace I) =>
      (ts.map fun t => score t.accepted t.outcomes * branchMass t.state).sum)
    (observedPairedTraces_left A B P ψ ψ)
  have hstatB := congrArg (fun ts : List (BranchTrace I) =>
      (ts.map fun t => score t.accepted t.outcomes * branchMass t.state).sum)
    (observedPairedTraces_right A B P ψ ψ)
  simp only [List.map_map, Function.comp_def] at hstatA hstatB
  have hmetadata : (xs.map fun t => score t.2.accepted t.2.outcomes * branchMass t.2.state).sum =
      (xs.map fun t => c t * branchMass t.2.state).sum := by
    congr 1
    apply List.map_congr_left
    intro t ht
    have h := observedPairedTraces_metadata A B P ψ ψ t ht
    rw [← h.1, ← h.2.2.2.2]
  have hstats : observedMetadataScore A P ψ score - observedMetadataScore B P ψ score =
      (xs.map fun t => c t * (‖u t‖ ^ 2 - ‖v t‖ ^ 2)).sum := by
    unfold observedMetadataScore
    rw [← hstatA, ← hstatB, hmetadata]
    simp only [metadata_mass_norm]
    rw [← metadata_sum_sub]
    congr 1
    apply List.map_congr_left
    intro t _
    dsimp only [u, v, c]
    ring
  rw [hstats]
  exact metadata_list_score_sq xs u v c (fun t _ => hscore _ _) hu hv

end Qatlib.Concepts.AdversaryBounds.AdvDuality
