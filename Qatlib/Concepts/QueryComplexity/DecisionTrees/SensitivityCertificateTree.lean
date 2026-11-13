/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics

/-!
# Certificate trees and sensitive block histories

This module constructs `certificateTree` by repeatedly querying certificates of compatible
positive inputs. A history invariant produces sensitive block families for negative extensions,
proving correctness after a number of rounds equal to block sensitivity and yielding the
deterministic certificate bound of [BealsEtAl2001].

## Main statements

* `certificateTree_budget`: each round costs at most the one certificate complexity.
* `certificateTree_correct`: the history invariant ensures correctness when the round budget is
  exhausted.
* `certificateTree_exists`: a correct deterministic tree uses at most C¹(f)bs(f) queries.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

variable {N : ℕ}

/-- Replace the values of assignment `a` on `S` by the corresponding values of input `x`. -/
def overwrite (a x : Fin N → Bool) (S : Finset (Fin N)) : Fin N → Bool :=
  fun i => if i ∈ S then x i else a i

/-- Overwriting an assignment on the empty set leaves it unchanged. -/
@[simp] lemma overwrite_empty (a x : Fin N → Bool) : overwrite a x ∅ = a := by
  funext i
  simp [overwrite]

/-- The query tree that reads the indices in `L`, updates the assignment with their input
values, and then runs `next` on the resulting assignment. -/
def readCertificate (L : List (Fin N)) (a : Fin N → Bool)
    (next : (Fin N → Bool) → BoolQueryTree (Fin N) Bool) : BoolQueryTree (Fin N) Bool :=
  match L with
  | [] => next a
  | i :: L => .ask i (readCertificate L (Function.update a i false) next)
      (readCertificate L (Function.update a i true) next)

/-- If every continuation uses at most `b` queries, reading `L` before the continuation uses at
most `L.length + b` queries. -/
lemma readCertificate_budget (L : List (Fin N)) (a : Fin N → Bool)
    (next : (Fin N → Bool) → BoolQueryTree (Fin N) Bool) (b : ℕ)
    (hb : ∀ a, (next a).MaxQueries ≤ b) :
    (readCertificate L a next).MaxQueries ≤ L.length + b := by
  induction L generalizing a with
  | nil => simpa [readCertificate] using hb a
  | cons i L ih =>
    have hf := ih (Function.update a i false)
    have ht := ih (Function.update a i true)
    simp only [readCertificate,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries, List.length_cons]
    omega

/-- Updating one coordinate and then overwriting a list of coordinates equals overwriting their
combined list. -/
lemma overwrite_cons (a x : Fin N → Bool) (i : Fin N) (L : List (Fin N)) :
    overwrite (Function.update a i (x i)) x L.toFinset = overwrite a x (i :: L).toFinset := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [overwrite]
  · simp [overwrite, hj]

/-- The output of `readCertificate` equals the output of its continuation at the assignment
obtained by overwriting the queried coordinates with the input values. -/
lemma readCertificate_run (L : List (Fin N)) (a x : Fin N → Bool)
    (next : (Fin N → Bool) → BoolQueryTree (Fin N) Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (readCertificate L a next)).1 =
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (next (overwrite a x L.toFinset))).1 := by
  induction L generalizing a with
  | nil => simp [readCertificate]
  | cons i L ih =>
    cases hi : x i
    · simp only [readCertificate, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hi, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      rw [← hi, overwrite_cons]
    · simp only [readCertificate, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hi, ↓reduceIte]
      rw [ih]
      rw [← hi, overwrite_cons]

/-- The existence of an input agreeing with `a` on `K` on which `f` is true. -/
def PositiveExtension (f : (Fin N → Bool) → Bool) (K : Finset (Fin N))
    (a : Fin N → Bool) : Prop :=
  ∃ x, (∀ i ∈ K, x i = a i) ∧ f x = true

/-- A positive input extending the assignment on `K`, together with a certificate whose size is
at most the one certificate complexity. -/
structure PositiveCertificate (f : (Fin N → Bool) → Bool) (K : Finset (Fin N))
    (a : Fin N → Bool) where
  input : Fin N → Bool
  indices : Finset (Fin N)
  agrees : ∀ i ∈ K, input i = a i
  positive : f input = true
  certificate : IsCertificateFor f input indices
  size_le : indices.card ≤ oneCertificateComplexity f

/-- Choose a positive extension and a certificate bounded by the one certificate complexity. -/
noncomputable def choosePositiveCertificate (f : (Fin N → Bool) → Bool)
    (K : Finset (Fin N)) (a : Fin N → Bool) (h : PositiveExtension f K a) :
    PositiveCertificate f K a := by
  let x := Classical.choose h
  have hx := Classical.choose_spec h
  let S := Classical.choose (certificate_minimum f x)
  have hS := Classical.choose_spec (certificate_minimum f x)
  exact ⟨x, S, hx.1, hx.2, hS.1, hS.2 ▸ certificateSizeAt_le_one hx.2⟩

/-- The recursive decision tree that reads certificates of compatible positive inputs for a
specified number of rounds, stopping with false when no positive extension exists. -/
noncomputable def certificateTree (f : (Fin N → Bool) → Bool) :
    ℕ → Finset (Fin N) → (Fin N → Bool) → BoolQueryTree (Fin N) Bool
  | 0, K, a => .halt (if PositiveExtension f K a then true else false)
  | r + 1, K, a =>
      if h : PositiveExtension f K a then
        let c := choosePositiveCertificate f K a h
        readCertificate c.indices.toList a
          (fun b => certificateTree f r (K ∪ c.indices) b)
      else .halt false

/-- The certificate tree with `r` rounds uses at most `r` times the one certificate complexity
queries. -/
lemma certificateTree_budget (f : (Fin N → Bool) → Bool) (r : ℕ)
    (K : Finset (Fin N)) (a : Fin N → Bool) :
    (certificateTree f r K a).MaxQueries ≤ r * oneCertificateComplexity f := by
  induction r generalizing K a with
  | zero => simp [certificateTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | succ r ih =>
    unfold certificateTree
    split
    · rename_i hp
      let c := choosePositiveCertificate f K a hp
      have hb := readCertificate_budget c.indices.toList a
        (fun b => certificateTree f r (K ∪ c.indices) b)
        (r * oneCertificateComplexity f) (fun b => ih (K ∪ c.indices) b)
      have hc := c.size_le
      simp only [Finset.length_toList] at hb
      change (readCertificate c.indices.toList a _).MaxQueries ≤ _
      calc
        _ ≤ c.indices.card + r * oneCertificateComplexity f := hb
        _ ≤ oneCertificateComplexity f + r * oneCertificateComplexity f := by omega
        _ = (r + 1) * oneCertificateComplexity f := by ring
    · simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]

/-- The condition that each negative extension of the assignment on `K` possesses a sensitive
family of exactly `m` blocks contained in `K`. -/
def CertificateHistory (f : (Fin N → Bool) → Bool) (K : Finset (Fin N))
    (a : Fin N → Bool) (m : ℕ) : Prop :=
  ∀ y, (∀ i ∈ K, y i = a i) → f y = false →
    ∃ F, SensitiveFamily f y F ∧ F.card = m ∧ ∀ B ∈ F, B ⊆ K

/-- Adding the indices of a compatible positive certificate increases the sensitive family
history length by one for any new assignment agreeing on the previous queried set. -/
lemma certificateHistory_step {f : (Fin N → Bool) → Bool} {K : Finset (Fin N)}
    {a b : Fin N → Bool} {m : ℕ} (c : PositiveCertificate f K a)
    (hh : CertificateHistory f K a m) (hb : ∀ i ∈ K, b i = a i) :
    CertificateHistory f (K ∪ c.indices) b (m + 1) := by
  intro y hy hfy
  have hyK : ∀ i ∈ K, y i = a i := fun i hi =>
    (hy i (Finset.mem_union_left _ hi)).trans (hb i hi)
  obtain ⟨F, hF, hcard, hsub⟩ := hh y hyK hfy
  let B := differing y c.input c.indices
  have hB : BlockSensitive f y B := by
    have hv := c.certificate (flipBlock y B)
      (fun i hi => flip_differing_on y c.input c.indices i hi)
    unfold BlockSensitive
    rw [hv, c.positive, hfy]
    decide
  have hd : ∀ C ∈ F, B ∩ C = ∅ := by
    intro C hC
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hiB, hiC⟩ := Finset.mem_inter.mp hi
    have hiK := hsub C hC hiC
    exact (Finset.mem_filter.mp hiB).2 ((hyK i hiK).trans (c.agrees i hiK).symm)
  have hext := sensitiveFamily_insert hF hB hd
  refine ⟨insert B F, hext.1, by rw [hext.2, hcard], ?_⟩
  intro C hC i hi
  rcases Finset.mem_insert.mp hC with hCB | hCF
  · subst C
    exact Finset.mem_union_right _ (differing_subset y c.input c.indices hi)
  · exact Finset.mem_union_left _ (hsub C hCF hi)

/-- If the history length equals block sensitivity and a positive extension still exists, every
input agreeing on the queried coordinates is positive. -/
lemma exhaustedHistory_positive {f : (Fin N → Bool) → Bool} {K : Finset (Fin N)}
    {a : Fin N → Bool} (hh : CertificateHistory f K a (blockSensitivity f))
    (hp : PositiveExtension f K a) (x : Fin N → Bool) (hx : ∀ i ∈ K, x i = a i) :
    f x = true := by
  cases hfx : f x
  · obtain ⟨y, hy, hfy⟩ := hp
    obtain ⟨F, hF, hcard, hsub⟩ := hh x hx hfx
    let B := differing x y Finset.univ
    have hB : BlockSensitive f x B := by
      simp [BlockSensitive, B, flip_differing_univ, hfx, hfy]
    have hd : ∀ C ∈ F, B ∩ C = ∅ := by
      intro C hC
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hiB, hiC⟩ := Finset.mem_inter.mp hi
      have hiK := hsub C hC hiC
      exact (Finset.mem_filter.mp hiB).2 ((hx i hiK).trans (hy i hiK).symm)
    have hext := sensitiveFamily_insert hF hB hd
    have hbound := sensitiveFamily_card_le f x (insert B F) hext.1
    rw [hext.2, hcard] at hbound
    omega
  · rfl

/-- If no positive extension exists, every input agreeing with the assignment on the queried
coordinates is negative. -/
lemma noPositiveExtension_false {f : (Fin N → Bool) → Bool} {K : Finset (Fin N)}
    {a : Fin N → Bool} (hp : ¬ PositiveExtension f K a)
    (x : Fin N → Bool) (hx : ∀ i ∈ K, x i = a i) : f x = false := by
  cases hfx : f x
  · rfl
  · exact (hp ⟨x, hx, hfx⟩).elim

/-- If `x` agrees with `a` on `K`, overwriting any additional set of coordinates with values
from `x` preserves agreement with `a` on `K`. -/
lemma overwrite_agrees_old {K S : Finset (Fin N)} {a x : Fin N → Bool}
    (hx : ∀ i ∈ K, x i = a i) : ∀ i ∈ K, overwrite a x S i = a i := by
  intro i hi
  by_cases hS : i ∈ S <;> simp [overwrite, hS, hx i hi]

/-- If `x` agrees with `a` on `K`, it agrees with the overwritten assignment on the union of `K`
and the overwritten set. -/
lemma overwrite_agrees_union {K S : Finset (Fin N)} {a x : Fin N → Bool}
    (hx : ∀ i ∈ K, x i = a i) : ∀ i ∈ K ∪ S, x i = overwrite a x S i := by
  intro i hi
  by_cases hS : i ∈ S
  · simp [overwrite, hS]
  · have hiK := (Finset.mem_union.mp hi).resolve_right hS
    simp [overwrite, hS, hx i hiK]

/-- Given a certificate history, the certificate tree computes `f` on every consistent input
when the elapsed and remaining rounds sum to block sensitivity. -/
lemma certificateTree_correct (f : (Fin N → Bool) → Bool) (r m : ℕ)
    (K : Finset (Fin N)) (a : Fin N → Bool)
    (hh : CertificateHistory f K a m) (hm : m + r = blockSensitivity f)
    (x : Fin N → Bool) (hx : ∀ i ∈ K, x i = a i) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (certificateTree f r K a)).1 = f x := by
  induction r generalizing m K a with
  | zero =>
    have hm' : m = blockSensitivity f := by omega
    subst m
    simp only [certificateTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
    by_cases hp : PositiveExtension f K a
    · rw [if_pos hp]
      exact (exhaustedHistory_positive hh hp x hx).symm
    · rw [if_neg hp]
      exact (noPositiveExtension_false hp x hx).symm
  | succ r ih =>
    unfold certificateTree
    split
    · rename_i hp
      let c := choosePositiveCertificate f K a hp
      change (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (readCertificate c.indices.toList a
        (fun b => certificateTree f r (K ∪ c.indices) b))).1 = f x
      rw [readCertificate_run, Finset.toList_toFinset]
      exact ih (m + 1) (K ∪ c.indices) (overwrite a x c.indices)
        (certificateHistory_step c hh (overwrite_agrees_old hx)) (by omega)
        (overwrite_agrees_union hx)
    · simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
      exact (noPositiveExtension_false (by assumption) x hx).symm

/-- Every total Boolean function has a correct deterministic query tree with maximum query count
at most one certificate complexity times block sensitivity. This is the certificate
construction for [Beals et al., Lemma 5.3][BealsEtAl2001]. -/
theorem certificateTree_exists (f : (Fin N → Bool) → Bool) :
    ∃ t : BoolQueryTree (Fin N) Bool,
      (∀ x, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1 = f x) ∧
      t.MaxQueries ≤ oneCertificateComplexity f * blockSensitivity f := by
  let a : Fin N → Bool := fun _ => false
  let t := certificateTree f (blockSensitivity f) ∅ a
  refine ⟨t, ?_, ?_⟩
  · intro x
    apply certificateTree_correct f (blockSensitivity f) 0 ∅ a
    · intro y _ _
      exact ⟨∅, by simp [SensitiveFamily], rfl, by simp⟩
    · simp
    · simp
  · simpa only [Nat.mul_comm] using certificateTree_budget f (blockSensitivity f) ∅ a

end Qatlib.Concepts.QueryComplexity.DecisionTrees
