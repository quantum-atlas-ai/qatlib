/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4 of arXiv:1105.3310v3 (Montanaro, 2012)

Paper: Ashley Montanaro, *The quantum query complexity of learning multilinear
polynomials*, arXiv:1105.3310v3 (8 Mar 2012), fixed at
`prove/assets/1105.3310.pdf`.

Source location: Lemma 4, §2 p.4 (statement), Appendix B p.6 (proof).

The paper defines, for `S ⊆ [n]`,
`f_S(x) = Σ_{β ∈ {0,1}^S} (-1)^{|S| - |β|} f(x + Σ_{j} β_j e_{S_j})`,
the signed average of `f` over the Boolean cube at `x` spanned by `{e_i : i ∈ S}`,
and observes it is the iterated discrete derivative `Δ_{S_1} … Δ_{S_k} f`.
Lemma 4 then states, for `f` multilinear of degree `d` with expansion
`f(x) = Σ_{|T| ≤ d} α_T ∏_{i∈T} x_i` and `|S| = d - 1`,
`f_S(x) = α_S + Σ_{k ∉ S} α_{S∪{k}} x_k`.

This file fixes the field `F` (the paper's `𝔽_q`, `q = |F|`) as an arbitrary
`Field`, defines the coefficient representation, the signed cube sum `fS`, and
proves Lemma 4 in full.
-/

open Finset
open scoped BigOperators

namespace Qatlib.Papers.Multilinear11.MainResults.MultilinearExpansion

variable {n : ℕ} {F : Type*} [Field F]

/-- Evaluation at `x` of the multilinear polynomial with coefficient family `α`:
`Σ_T α T ∏_{i∈T} x i`, where `T` ranges over all subsets of `[n]`.
Source: arXiv:1105.3310v3, §1 p.1 (multilinear expansion). -/
noncomputable def multilinearEval (α : Finset (Fin n) → F) (x : Fin n → F) : F :=
  ∑ T : Finset (Fin n), α T * ∏ i ∈ T, x i

/-- Shift the point `x` by one along each coordinate on which `b` is true:
`x ↦ x + Σ_{i : b i} e_i`. -/
def shiftBool (b : Fin n → Bool) (x : Fin n → F) : Fin n → F :=
  fun j => x j + (if b j then (1 : F) else 0)

/-- The Boolean cube `{0,1}^S` as a finset of functions `[n] → Bool` that are `false`
off `S`.  This is the summation index of the paper's `f_S`. -/
def cubeFinset (S : Finset (Fin n)) : Finset (Fin n → Bool) :=
  Fintype.piFinset (fun i => if i ∈ S then (Finset.univ : Finset Bool) else {false})

/-- The sign `(-1)^{|S| - |β|}` of the paper, written coordinatewise as
`∏_{i∈S} (if b i then 1 else -1)` (each `false` contributes `-1`). -/
def signWeight (S : Finset (Fin n)) (b : Fin n → Bool) : F :=
  ∏ i : Fin n, (if i ∈ S then (if b i then (1 : F) else -1) else 1)

/-- The signed cube sum `f_S` of arXiv:1105.3310v3, §2 p.4. -/
noncomputable def fS (f : (Fin n → F) → F) (S : Finset (Fin n)) (x : Fin n → F) : F :=
  ∑ b ∈ cubeFinset S, signWeight S b * f (shiftBool b x)

/-- **Core cube-sum identity (Appendix B).** Summing the signed cube weight times a
monomial `∏_{i∈T} (x + b)_i` over `b ∈ {0,1}^S` extracts the derivative of the
monomial with respect to `S`: it is `∏_{i∈T\S} x_i` when `S ⊆ T` and `0` otherwise. -/
theorem cube_sum_mul_monomial (S T : Finset (Fin n)) (x : Fin n → F) :
    (∑ b ∈ cubeFinset S, signWeight S b * ∏ i ∈ T, shiftBool b x i)
      = if S ⊆ T then ∏ i ∈ T \ S, x i else 0 := by
  classical
  -- Move the monomial product into a product over all of `[n]`.
  have hprod : ∀ b, signWeight S b * ∏ i ∈ T, shiftBool b x i
      = ∏ i : Fin n, ((if i ∈ S then (if b i then (1 : F) else -1) else 1)
          * (if i ∈ T then x i + (if b i then (1 : F) else 0) else 1)) := by
    intro b
    rw [signWeight]
    rw [← Finset.prod_ite_mem_eq (s := T) (f := fun i => shiftBool b x i)]
    rw [← Finset.prod_mul_distrib]
    simp only [shiftBool]
  simp only [hprod]
  -- Turn the sum over the cube into a product of per-coordinate sums.
  simp only [cubeFinset]
  rw [← Finset.prod_univ_sum
      (fun i : Fin n => if i ∈ S then (Finset.univ : Finset Bool) else {false})
      (fun i β => (if i ∈ S then (if β then (1 : F) else -1) else 1)
          * (if i ∈ T then x i + (if β then (1 : F) else 0) else 1))]
  -- Evaluate each per-coordinate factor.
  have hfac : ∀ i : Fin n,
      (∑ β ∈ (if i ∈ S then (Finset.univ : Finset Bool) else {false}),
          (if i ∈ S then (if β then (1 : F) else -1) else 1)
            * (if i ∈ T then x i + (if β then (1 : F) else 0) else 1))
        = if i ∈ S then (if i ∈ T then (1 : F) else 0) else (if i ∈ T then x i else 1) := by
    intro i
    by_cases hiS : i ∈ S
    · simp only [hiS, if_true]
      rw [Fintype.sum_bool]
      by_cases hiT : i ∈ T <;> simp [hiT]
    · simp only [hiS, if_false]
      simp
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  -- Split the product into the `S` part and its complement.
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n)) (fun i => i ∈ S)]
  have hS : (∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S),
        (if i ∈ S then (if i ∈ T then (1 : F) else 0) else (if i ∈ T then x i else 1)))
      = if S ⊆ T then 1 else 0 := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S),
        (if i ∈ S then (if i ∈ T then (1 : F) else 0) else (if i ∈ T then x i else 1))
          = (if i ∈ T then (1 : F) else 0) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [hi]
    calc (∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S),
          (if i ∈ S then (if i ∈ T then (1 : F) else 0) else (if i ∈ T then x i else 1)))
        = ∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S),
            (if i ∈ T then (1 : F) else 0) := Finset.prod_congr rfl h1
      _ = if S ⊆ T then 1 else 0 := by
        rw [Finset.prod_ite_zero]
        simp only [Finset.prod_const_one]
        have hiff : (∀ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S), i ∈ T)
            ↔ S ⊆ T := by
          simp [Finset.subset_iff]
        by_cases hst : S ⊆ T
        · have h' : ∀ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S), i ∈ T :=
            hiff.mpr hst
          rw [if_pos h', if_pos hst]
        · have h' : ¬ (∀ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S), i ∈ T) :=
            fun hc => hst (hiff.mp hc)
          rw [if_neg h', if_neg hst]
  have hc : (∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ i ∈ S),
        (if i ∈ S then (if i ∈ T then (1 : F) else 0) else (if i ∈ T then x i else 1)))
      = ∏ i ∈ T \ S, x i := by
    rw [Finset.prod_filter]
    rw [← Finset.prod_ite_mem_eq (s := T \ S) (f := fun i => x i)]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp [hiS, hiT, Finset.mem_sdiff]
  rw [hS, hc]
  by_cases hST : S ⊆ T
  · simp [hST]
  · simp [hST]

/-- **The derivative-coefficient form of `f_S`.** Applied to a multilinear expansion,
`f_S` has coefficient family `U ↦ (if Disjoint S U then α (S ∪ U) else 0)`, i.e.
`f_S(x) = Σ_{U disjoint S} α_{S∪U} ∏_{i∈U} x_i`.  This is the content of the
derivative computation behind Lemma 4 (arXiv:1105.3310v3, §2 p.4 and Appendix B). -/
theorem fS_multilinearEval_coeff (α : Finset (Fin n) → F) (S : Finset (Fin n))
    (x : Fin n → F) :
    fS (multilinearEval α) S x
      = ∑ T : Finset (Fin n), α T * (if S ⊆ T then ∏ i ∈ T \ S, x i else 0) := by
  classical
  unfold fS multilinearEval
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  have hstep : ∀ b, signWeight S b * (α T * ∏ i ∈ T, shiftBool b x i)
      = α T * (signWeight S b * ∏ i ∈ T, shiftBool b x i) := by
    intro b; ring
  simp_rw [hstep]
  rw [← Finset.mul_sum, cube_sum_mul_monomial]

/-- **Lemma 4 of arXiv:1105.3310v3** (statement p.4, proof Appendix B p.6).
Let `f(x) = Σ_{|T| ≤ d} α_T ∏_{i∈T} x_i` be a multilinear polynomial of degree `d`
over a field `F` and let `|S| = d - 1`.  Then the signed cube sum `f_S` satisfies
`f_S(x) = α_S + Σ_{k ∉ S} α_{S∪{k}} x_k`. -/
theorem lemma4_expansion
    (α : Finset (Fin n) → F) (d : ℕ) (hdeg : ∀ T, d < T.card → α T = 0)
    (S : Finset (Fin n)) (hS : S.card = d - 1) (x : Fin n → F) :
    fS (multilinearEval α) S x
      = α S + ∑ k ∈ (Finset.univ \ S), α (S ∪ {k}) * x k := by
  classical
  rw [fS_multilinearEval_coeff]
  -- Restrict the `T`-sum to the support `{S} ∪ {S ∪ {k} : k ∉ S}`.
  let E : Finset (Finset (Fin n)) :=
    insert S ((Finset.univ \ S).image (fun k => insert k S))
  have hzero : ∀ T ∈ (Finset.univ : Finset (Finset (Fin n))), T ∉ E →
      α T * (if S ⊆ T then ∏ i ∈ T \ S, x i else 0) = 0 := by
    intro T _ hTE
    by_cases hST : S ⊆ T
    · have hcard : 2 ≤ (T \ S).card := by
        by_contra hcon
        have hle : (T \ S).card ≤ 1 := by omega
        rcases (show (T \ S).card = 0 ∨ (T \ S).card = 1 by omega) with h0 | h1
        · have hemp : T \ S = ∅ := Finset.card_eq_zero.mp h0
          have hTS : T ⊆ S := by
            intro i hi
            by_contra h'
            exact absurd (mem_sdiff.mpr ⟨hi, h'⟩) (by rw [hemp]; simp)
          have : T = S := Finset.Subset.antisymm hTS hST
          exact hTE (by rw [this]; exact Finset.mem_insert_self S _)
        · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
          have hkS : k ∉ S := by
            have : k ∈ T \ S := by rw [hk]; exact Finset.mem_singleton_self k
            exact (Finset.mem_sdiff.mp this).2
          have hT : T = insert k S := by
            have h1' : S ∪ T \ S = T := Finset.union_sdiff_of_subset hST
            rw [hk, Finset.union_singleton] at h1'
            exact h1'.symm
          refine hTE ?_
          rw [hT]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkS⟩, rfl⟩)
      have hTcard : d < T.card := by
        have hcs : (T \ S).card = T.card - S.card := Finset.card_sdiff_of_subset hST
        have hle'T : S.card ≤ T.card := Finset.card_le_card hST
        omega
      rw [hdeg T hTcard, zero_mul]
    · rw [if_neg hST, mul_zero]
  have hsumE : (∑ T : Finset (Fin n), α T * (if S ⊆ T then ∏ i ∈ T \ S, x i else 0))
      = ∑ T ∈ E, α T * (if S ⊆ T then ∏ i ∈ T \ S, x i else 0) := by
    refine (Finset.sum_subset (Finset.subset_univ E) ?_).symm
    intro T hTuniv hTE
    exact hzero T hTuniv hTE
  rw [hsumE]
  -- Evaluate the finite support sum.
  have hSnotin : S ∉ (Finset.univ \ S).image (fun k => insert k S) := by
    intro hmem
    obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp hmem
    have hkS : k ∉ S := (Finset.mem_sdiff.mp hk).2
    have : k ∈ insert k S := Finset.mem_insert_self k S
    rw [hkeq] at this
    exact hkS this
  dsimp only [E]
  rw [Finset.sum_insert hSnotin]
  have hinj : ∀ a ∈ (Finset.univ \ S), ∀ b ∈ (Finset.univ \ S),
      insert a S = insert b S → a = b := by
    intro a ha b hb hab
    have haS : a ∉ S := (Finset.mem_sdiff.mp ha).2
    have : a ∈ insert b S := by rw [← hab]; exact Finset.mem_insert_self a S
    rcases Finset.mem_insert.mp this with h | h
    · exact h
    · exact absurd h haS
  rw [Finset.sum_image hinj]
  -- Simplify the two kinds of terms.
  have htermS : α S * (if S ⊆ S then ∏ i ∈ S \ S, x i else 0) = α S := by
    rw [if_pos (Finset.Subset.refl S), Finset.sdiff_self, Finset.prod_empty, mul_one]
  rw [htermS]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkS : k ∉ S := (Finset.mem_sdiff.mp hk).2
  have hsub : S ⊆ insert k S := Finset.subset_insert k S
  rw [if_pos hsub]
  have hdiff : insert k S \ S = {k} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hi, hni⟩
      · rfl
      · exact absurd hi hni
    · rintro rfl
      exact ⟨Or.inl rfl, hkS⟩
  rw [hdiff, Finset.prod_singleton, Finset.union_singleton]

end Qatlib.Papers.Multilinear11.MainResults.MultilinearExpansion
