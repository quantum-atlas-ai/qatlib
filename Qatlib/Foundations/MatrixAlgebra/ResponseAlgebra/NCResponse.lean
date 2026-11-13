/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra.NCResponseData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.BigOperators
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Finite noncommutative polynomial responses

The module expands powers of `ncTransition` into words and recovers a noncommutative polynomial
from finite transition, injection, and collection data. A truncating state recursion gives both
a degree bound and vanishing of the transition power applied to the injection.

`nc_response_evaluation` identifies the resulting finite matrix response with `ncPolyEval`, and
`nc_response` packages these conclusions uniformly over finite matrix substitutions. The block
and Kronecker matrix algebra has standard background in [HornJohnson1991].

## Main statements

* `nc_response_degree_bound`: truncation bounds the length of words with nonzero coefficients.
* `nc_response_injection_truncation`: the truncated transition power annihilates the injection.
* `nc_response`: the finite response evaluates the noncommutative polynomial for every finite
  matrix substitution.

## References

* [Horn and Johnson, 1991][HornJohnson1991]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

open Matrix
open scoped BigOperators

variable {J X S : Type} [Fintype J] [Fintype X] [DecidableEq X]
  [Fintype S] [DecidableEq S]

/-- The finite set of all words of a given length over the finite alphabet `J`. -/
private noncomputable def ncWords (J : Type) [Fintype J] : ℕ → Finset (List J)
  | 0 => by
      classical
      exact {[]}
  | n + 1 => by
      classical
      exact (Finset.univ : Finset J).biUnion
        (fun j : J => (ncWords J n).image (List.cons j))

/-- Membership in `ncWords J n` is equivalent to having length `n`. -/
private theorem ncWords_mem (w : List J) (n : ℕ) :
    w ∈ ncWords J n ↔ w.length = n := by
  classical
  induction n generalizing w with
  | zero => cases w <;> simp [ncWords]
  | succ n ih =>
      cases w with
      | nil => simp [ncWords]
      | cons j w => simp [ncWords, ih, List.length_cons]

/-- A sum over words of length `n + 1` splits into a sum over the first letter and words of
length `n`. -/
private theorem ncWords_sum_succ {E : Type} [AddCommMonoid E]
    (n : ℕ) (f : List J → E) :
    (∑ w ∈ ncWords J (n + 1), f w) = ∑ j, ∑ w ∈ ncWords J n, f (j :: w) := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset J))
      (fun j => (ncWords J n).image (List.cons j)) := by
    intro j _ k _ hjk
    apply Finset.disjoint_left.mpr
    intro w hjw hkw
    obtain ⟨v, _hv, hjv⟩ := Finset.mem_image.mp hjw
    obtain ⟨z, _hz, hkz⟩ := Finset.mem_image.mp hkw
    exact hjk (List.cons.inj (hjv.trans hkz.symm)).1
  rw [ncWords, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro j _hj
  exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)

omit [DecidableEq S] in

/-- Multiplication by `T ⊗ A` applies `T` to the response vector and multiplies the response
matrix on the left by `A`. -/
theorem nc_transition_response_tensor (T : Matrix X X ℂ)
    (A M : Matrix S S ℂ) (v : EuclideanSpace ℂ X) :
    Matrix.kronecker T A * ncResponseTensor v M =
      ncResponseTensor (T.toEuclideanLin v) (A * M) := by
  ext p y
  obtain ⟨r, x⟩ := p
  simp only [Matrix.mul_apply, ncResponseTensor,
    Fintype.sum_prod_type]
  change (∑ u : X, ∑ z : S, (T r u * A x z) * (v u * M z y)) =
    (∑ u : X, T r u * v u) * (∑ z : S, A x z * M z y)
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro z _hz
  ring

omit [DecidableEq X] [DecidableEq S] in

/-- Collecting a response tensor yields `A * M` scaled by the coordinate pairing of the
collection coefficients with the response vector. -/
theorem nc_collect_response_tensor (c : X → ℂ) (A M : Matrix S S ℂ)
    (v : EuclideanSpace ℂ X) :
    ncCollectTensor c A * ncResponseTensor v M =
      (∑ x, c x * v x) • (A * M) := by
  ext x y
  simp only [Matrix.mul_apply, ncCollectTensor, ncResponseTensor,
    Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro z _hz
  ring

/-- A transition power applied to the injection expands as a sum of response tensors indexed by
words of that length, assuming the state recursion. -/
private theorem nc_response_power_words (T : J → Matrix X X ℂ)
    (H : List J → EuclideanSpace ℂ X)
    (hrec : ∀ j w, (T j).toEuclideanLin (H w) = H (j :: w))
    (A : J → Matrix S S ℂ) (n : ℕ) :
    (ncTransition T A) ^ n * ncInjection H =
      ∑ w ∈ ncWords J n, ncResponseTensor (H w) (ncWordEval A w) := by
  classical
  induction n with
  | zero => simp [ncWords, ncInjection, ncWordEval]
  | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih]
      rw [ncTransition, Matrix.sum_mul]
      rw [ncWords_sum_succ]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro w _hw
      rw [nc_transition_response_tensor, hrec, ncWordEval]

omit [Fintype J] [DecidableEq X] in

/-- If response states vanish at lengths at least `D` and generate the nonempty-word
coefficients, every word with nonzero coefficient has length at most `D`. -/
theorem nc_response_degree_bound (H : List J → EuclideanSpace ℂ X)
    (C : J → X → ℂ) (q : NCPoly J) (D : ℕ)
    (htruncate : ∀ w, D ≤ w.length → H w = 0)
    (hq : ∀ j w, q (j :: w) = ∑ x, C j x * H w x) :
    ∀ w, q w ≠ 0 → w.length ≤ D := by
  intro w hne
  cases w with
  | nil => simp
  | cons j w =>
      by_contra hlarge
      have hD : D ≤ w.length := by simp only [List.length_cons] at hlarge; omega
      have hzero : q (j :: w) = 0 := by
        rw [hq, htruncate w hD]
        simp
      exact hne hzero

/-- A noncommutative polynomial with all nonzero coefficients at word lengths at most `D`
evaluates as the sum of its homogeneous word contributions from length zero through `D`. -/
private theorem nc_poly_degree_sum (A : J → Matrix S S ℂ) (q : NCPoly J) (D : ℕ)
    (hbound : ∀ w, q w ≠ 0 → w.length ≤ D) :
    ncPolyEval A q =
      ∑ t ∈ Finset.range (D + 1), ∑ w ∈ ncWords J t, q w • ncWordEval A w := by
  classical
  let f : List J → Matrix S S ℂ := fun w => q w • ncWordEval A w
  have hmap : ∀ w ∈ q.support, w.length ∈ Finset.range (D + 1) := by
    intro w hw
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound w (Finsupp.mem_support_iff.mp hw)))
  have hpart := Finset.sum_fiberwise_of_maps_to hmap f
  have hfiber (t : ℕ) :
      (∑ w ∈ q.support.filter (fun w => w.length = t), f w) =
      ∑ w ∈ ncWords J t, f w := by
    have hsub : q.support.filter (fun w => w.length = t) ⊆ ncWords J t := by
      intro w hw
      exact (ncWords_mem w t).mpr (Finset.mem_filter.mp hw).2
    apply Finset.sum_subset hsub
    intro w hw houtside
    have hnot : w ∉ q.support := by
      intro hs
      exact houtside (Finset.mem_filter.mpr ⟨hs, (ncWords_mem w t).mp hw⟩)
    dsimp only [f]
    rw [Finsupp.notMem_support_iff.mp hnot, zero_smul]
  calc
    ncPolyEval A q = ∑ w ∈ q.support, f w := by
      simp only [ncPolyEval, Finsupp.linearCombination_apply, Finsupp.sum, f]
    _ = ∑ t ∈ Finset.range (D + 1),
        ∑ w ∈ q.support.filter (fun w => w.length = t), f w := hpart.symm
    _ = ∑ t ∈ Finset.range (D + 1), ∑ w ∈ ncWords J t, f w := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact hfiber t

/-- Under the state and coefficient recursions, collecting the `n`th transition response yields
the polynomial contribution from words of length `n + 1`. -/
private theorem nc_collection_power_words (T : J → Matrix X X ℂ)
    (H : List J → EuclideanSpace ℂ X) (C : J → X → ℂ) (q : NCPoly J)
    (hrec : ∀ j w, (T j).toEuclideanLin (H w) = H (j :: w))
    (hq : ∀ j w, q (j :: w) = ∑ x, C j x * H w x)
    (A : J → Matrix S S ℂ) (n : ℕ) :
    ncCollection C A * ((ncTransition T A) ^ n * ncInjection H) =
      ∑ w ∈ ncWords J (n + 1), q w • ncWordEval A w := by
  classical
  rw [nc_response_power_words T H hrec A n, Matrix.mul_sum]
  calc
    (∑ w ∈ ncWords J n, ncCollection C A *
        ncResponseTensor (H w) (ncWordEval A w)) =
      ∑ w ∈ ncWords J n, ∑ j, q (j :: w) • ncWordEval A (j :: w) := by
      apply Finset.sum_congr rfl
      intro w _hw
      rw [ncCollection, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [nc_collect_response_tensor, ← hq, ncWordEval]
    _ = ∑ j, ∑ w ∈ ncWords J n, q (j :: w) • ncWordEval A (j :: w) := by
      rw [Finset.sum_comm]
    _ = ∑ w ∈ ncWords J (n + 1), q w • ncWordEval A w :=
      (ncWords_sum_succ n (fun w => q w • ncWordEval A w)).symm

/-- If the state recursion vanishes on words of length at least `D`, the `D`th transition power
annihilates the injection. -/
theorem nc_response_injection_truncation (T : J → Matrix X X ℂ)
    (H : List J → EuclideanSpace ℂ X) (D : ℕ)
    (hrec : ∀ j w, (T j).toEuclideanLin (H w) = H (j :: w))
    (htruncate : ∀ w, D ≤ w.length → H w = 0)
    (A : J → Matrix S S ℂ) :
    (ncTransition T A) ^ D * ncInjection (S := S) H = 0 := by
  classical
  rw [nc_response_power_words T H hrec A D]
  apply Finset.sum_eq_zero
  intro w hw
  have hD : D ≤ w.length := by rw [(ncWords_mem w D).mp hw]
  rw [htruncate w hD]
  ext p y
  simp [ncResponseTensor]

/-- Under the state recursion, truncation, and coefficient identities, the constant term plus
the finite collected transition sum equals the noncommutative polynomial evaluation. -/
theorem nc_response_evaluation (T : J → Matrix X X ℂ)
    (H : List J → EuclideanSpace ℂ X) (C : J → X → ℂ)
    (d : ℂ) (q : NCPoly J) (D : ℕ)
    (hrec : ∀ j w, (T j).toEuclideanLin (H w) = H (j :: w))
    (htruncate : ∀ w, D ≤ w.length → H w = 0) (hqnil : q [] = d)
    (hq : ∀ j w, q (j :: w) = ∑ x, C j x * H w x)
    (A : J → Matrix S S ℂ) :
    d • (1 : Matrix S S ℂ) + ncCollection C A *
      (∑ t ∈ Finset.range D, (ncTransition T A) ^ t) * ncInjection H =
      ncPolyEval A q := by
  classical
  have hbound := nc_response_degree_bound H C q D htruncate hq
  have heval := nc_poly_degree_sum A q D hbound
  rw [Finset.sum_range_succ'] at heval
  simp only [ncWords, Finset.sum_singleton, hqnil, ncWordEval] at heval
  calc
    _ = d • (1 : Matrix S S ℂ) + ∑ t ∈ Finset.range D,
        ncCollection C A * ((ncTransition T A) ^ t * ncInjection H) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = d • (1 : Matrix S S ℂ) + ∑ t ∈ Finset.range D,
        ∑ w ∈ ncWords J (t + 1), q w • ncWordEval A w := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _ht
      exact nc_collection_power_words T H C q hrec hq A t
    _ = ncPolyEval A q := by simpa only [add_comm] using! heval.symm

/-- A truncating response realization bounds the polynomial's word degree by `D` and, for every
finite matrix substitution, gives both injection truncation and the finite response
evaluation identity. -/
theorem nc_response (T : J → Matrix X X ℂ) (H : List J → EuclideanSpace ℂ X)
    (C : J → X → ℂ) (d : ℂ) (q : NCPoly J) (D : ℕ)
    (hrec : ∀ j w, (T j).toEuclideanLin (H w) = H (j :: w))
    (htruncate : ∀ w, D ≤ w.length → H w = 0)
    (hqnil : q [] = d) (hq : ∀ j w, q (j :: w) = ∑ x, C j x * H w x) :
    (∀ w, q w ≠ 0 → w.length ≤ D) ∧
    (∀ (S : Type) [Fintype S] [DecidableEq S] (A : J → Matrix S S ℂ),
      (ncTransition T A) ^ D * ncInjection (S := S) H = 0 ∧
      d • (1 : Matrix S S ℂ) + ncCollection C A *
        (∑ t ∈ Finset.range D, (ncTransition T A) ^ t) * ncInjection H =
        ncPolyEval A q) := by
  refine ⟨nc_response_degree_bound H C q D htruncate hq, ?_⟩
  intro S _ _ A
  exact ⟨nc_response_injection_truncation (S := S) T H D hrec htruncate A,
    nc_response_evaluation T H C d q D hrec htruncate hqnil hq A⟩

end Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra
