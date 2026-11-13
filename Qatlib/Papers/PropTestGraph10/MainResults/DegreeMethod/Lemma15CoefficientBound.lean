/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.AcceptancePolynomial
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Coefficient Bound for Quantum Acceptance Polynomials

This module proves Lemma 15: for any multilinear acceptance polynomial taking
values in `[0, 1]` on the Boolean cube, every monomial coefficient of support
size `k` has absolute value at most `2^k`.

## Main statements

* `lemma15_coefficient_bound`: `|P.poly.coeff d| ≤ 2^k` when `d.support.card = k`.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest], Lemma 15, p. 16.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.DegreeMethod

open Qatlib.Papers.PropTestGraph10.MainResults.Model

private lemma boolean_monomial {σ : Type*} [DecidableEq σ]
    (e : σ →₀ ℕ) (S : Finset σ) :
    (∏ i ∈ e.support, (if i ∈ S then (1 : ℝ) else 0) ^ e i) =
      if e.support ⊆ S then 1 else 0 := by
  by_cases h : e.support ⊆ S
  · simp only [h, ↓reduceIte]
    exact Finset.prod_eq_one fun i hi => by simp [h hi]
  · obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero hi (by simp [hiS, Finsupp.mem_support_iff.mp hi])

private lemma boolean_mobius_sum {σ : Type*} [DecidableEq σ]
    (D E : Finset σ) :
    (∑ S ∈ D.powerset, (-1 : ℝ) ^ (D.card - S.card) *
      (if E ⊆ S then 1 else 0)) = if E = D then 1 else 0 := by
  by_cases hED : E ⊆ D
  · have hdisj (T : Finset σ) (hT : T ⊆ D \ E) : Disjoint E T :=
      Finset.disjoint_left.mpr fun i hi hiT => (Finset.mem_sdiff.mp (hT hiT)).2 hi
    calc
      _ = ∑ S ∈ D.powerset.filter (E ⊆ ·), (-1 : ℝ) ^ (D.card - S.card) := by
        simp [Finset.sum_filter]
      _ = ∑ T ∈ (D \ E).powerset, (-1 : ℝ) ^ ((D \ E).card - T.card) := by
        symm
        refine Finset.sum_bij' (fun T _ => E ∪ T) (fun S _ => S \ E) ?_ ?_ ?_ ?_ ?_
        · intro T hT
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (Finset.union_subset hED ((Finset.mem_powerset.mp hT).trans
              Finset.sdiff_subset)), Finset.subset_union_left⟩
        · intro S hS
          exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff_left E
            (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1))
        · intro T hT
          exact Finset.union_sdiff_cancel_left (hdisj T (Finset.mem_powerset.mp hT))
        · intro S hS
          exact Finset.union_sdiff_of_subset (Finset.mem_filter.mp hS).2
        · intro T hT
          rw [Finset.card_union_of_disjoint (hdisj T (Finset.mem_powerset.mp hT)),
            Finset.card_sdiff_of_subset hED, Nat.sub_sub]
      _ = (1 + (-1 : ℝ)) ^ (D \ E).card := by
        simpa using Finset.sum_pow_mul_eq_add_pow (1 : ℝ) (-1) (D \ E)
      _ = if E = D then 1 else 0 := by
        by_cases h : E = D
        · simp [h]
        · have hne : D \ E ≠ ∅ := by
            intro hzero
            exact h (Finset.Subset.antisymm hED
              (Finset.sdiff_eq_empty_iff_subset.mp hzero))
          simp only [add_neg_cancel, zero_pow (Finset.card_eq_zero.not.mpr hne), h, ↓reduceIte]
  · have hne : E ≠ D := fun h => hED (by rw [h])
    simp only [hne, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro S hS
    have hES : ¬ E ⊆ S := fun h => hED (h.trans (Finset.mem_powerset.mp hS))
    simp [hES]

/-- **Lemma 15**: for an `AcceptancePolynomial` `P` over a finite variable type `σ`
and any exponent `d : σ →₀ ℕ` with `d.support.card = k`, `|P.poly.coeff d| ≤ 2^k`. -/
theorem lemma15_coefficient_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : AcceptancePolynomial σ) {k : ℕ} (d : σ →₀ ℕ)
    (hd : d.support.card = k) :
    |P.poly.coeff d| ≤ (2 : ℝ) ^ k := by
  by_cases hdeg : ∀ i : σ, d i ≤ 1
  · let indVec (S : Finset σ) : σ → ℝ := fun i => if i ∈ S then 1 else 0
    have hbound (S : Finset σ) : |MvPolynomial.eval (indVec S) P.poly| ≤ 1 := by
      have hbool : ∀ i, indVec S i = 0 ∨ indVec S i = 1 := by
        intro i
        by_cases hi : i ∈ S <;> simp [indVec, hi]
      exact abs_le.mpr ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (P.nonneg _ hbool),
        P.le_one _ hbool⟩
    have heval (S : Finset σ) :
        MvPolynomial.eval (indVec S) P.poly = ∑ e ∈ P.poly.support,
          P.poly.coeff e * (if e.support ⊆ S then 1 else 0) := by
      simp only [MvPolynomial.eval_eq, indVec, boolean_monomial]
    have hsupport (e : σ →₀ ℕ) (he : P.poly.coeff e ≠ 0) :
        e.support = d.support ↔ e = d := by
      constructor
      · intro h
        apply Finsupp.ext
        intro i
        have hmem : (e i ≠ 0) ↔ (d i ≠ 0) := by
          simpa only [Finsupp.mem_support_iff] using Finset.ext_iff.mp h i
        have := P.multilinear e he i
        have := hdeg i
        omega
      · rintro rfl
        rfl
    have hinversion : P.poly.coeff d = ∑ S ∈ d.support.powerset,
        (-1 : ℝ) ^ (d.support.card - S.card) * MvPolynomial.eval (indVec S) P.poly := by
      symm
      simp_rw [heval, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ e ∈ P.poly.support, P.poly.coeff e * (if e = d then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          simp_rw [mul_left_comm _ (P.poly.coeff e), ← Finset.mul_sum]
          rw [boolean_mobius_sum]
          simp only [hsupport e (MvPolynomial.mem_support_iff.mp he)]
        _ = P.poly.coeff d := by
          by_cases hm : d ∈ P.poly.support
          · simp [mul_ite, hm]
          · simp [mul_ite, hm, MvPolynomial.notMem_support_iff.mp hm]
    rw [hinversion]
    calc
      _ ≤ ∑ S ∈ d.support.powerset,
          |(-1 : ℝ) ^ (d.support.card - S.card) * MvPolynomial.eval (indVec S) P.poly| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ d.support.powerset, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro S _hS
        simpa only [abs_mul, abs_neg_one_pow, one_mul] using hbound S
      _ = (2 : ℝ) ^ k := by simp [Finset.card_powerset, hd]
  · have hz : P.poly.coeff d = 0 := by
      by_contra hne
      exact hdeg (P.multilinear d hne)
    rw [hz, abs_zero]
    positivity

end Qatlib.Papers.PropTestGraph10.MainResults.DegreeMethod
