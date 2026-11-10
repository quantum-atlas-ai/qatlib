/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LinearDiseq07.MainResults

open MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

def lemma7Degree (p k : ℕ) : ℕ := (p - 1) * ((2 * p - 2) ^ k - 1) / (2 * p - 3)

omit hp in

lemma lemma7Degree_one (h2 : 2 ≤ p) : lemma7Degree p 1 = p - 1 := by
  unfold lemma7Degree
  have h3 : 0 < 2 * p - 3 := by omega
  have hsub : (2 * p - 2) ^ 1 - 1 = 2 * p - 3 := by
    rw [pow_one]; omega
  rw [hsub, Nat.mul_div_cancel _ h3]

def linearForm (u : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ i, C (u i) * X i

lemma totalDegree_linearForm_le (u : Fin n → ZMod p) :
    (linearForm u).totalDegree ≤ 1 := by
  unfold linearForm
  refine totalDegree_finsetSum_le ?_
  intro i _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

def hyperplanePoly (u : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  linearForm u ^ (p - 1) - 1

lemma totalDegree_hyperplanePoly_le (u : Fin n → ZMod p) :
    (hyperplanePoly u).totalDegree ≤ lemma7Degree p 1 := by
  rw [lemma7Degree_one hp.out.two_le]
  have hpow : (linearForm u ^ (p - 1)).totalDegree ≤ p - 1 := by
    calc (linearForm u ^ (p - 1)).totalDegree
        ≤ (p - 1) * (linearForm u).totalDegree := totalDegree_pow _ _
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ (totalDegree_linearForm_le u)
      _ = p - 1 := Nat.mul_one _
  unfold hyperplanePoly
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_one]
  exact max_le hpow (Nat.zero_le _)

lemma eval_linearForm (a u : Fin n → ZMod p) :
    MvPolynomial.eval a (linearForm u) = ∑ i, u i * a i := by
  unfold linearForm
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, eval_C, eval_X]

lemma eval_hyperplanePoly (a u : Fin n → ZMod p) :
    MvPolynomial.eval a (hyperplanePoly u) = (∑ i, u i * a i) ^ (p - 1) - 1 := by
  unfold hyperplanePoly
  rw [map_sub, map_pow, eval_linearForm, map_one]

theorem hyperplanePoly_eval_eq_zero_iff (a u : Fin n → ZMod p) :
    MvPolynomial.eval a (hyperplanePoly u) = 0 ↔ ∑ i, u i * a i ≠ 0 := by
  rw [eval_hyperplanePoly, sub_eq_zero]
  constructor
  · intro h hzero
    rw [hzero, zero_pow (by have := hp.out.two_le; omega)] at h
    exact zero_ne_one h
  · exact ZMod.pow_card_sub_one_eq_one

theorem source_lemma7_at_k_one (u : Fin n → ZMod p) :
    ∃ Q : MvPolynomial (Fin n) (ZMod p),
      Q.totalDegree ≤ lemma7Degree p 1 ∧
      (∀ i, Q.degreeOf i ≤ p - 1) ∧
      ∀ a : Fin n → ZMod p, MvPolynomial.eval a Q = 0 ↔ ∑ i, u i * a i ≠ 0 := by
  refine ⟨hyperplanePoly u, totalDegree_hyperplanePoly_le u, ?_, fun a => ?_⟩
  · intro i
    refine (degreeOf_le_totalDegree _ i).trans ?_
    exact (totalDegree_hyperplanePoly_le u).trans (by rw [lemma7Degree_one hp.out.two_le])
  · exact hyperplanePoly_eval_eq_zero_iff a u

end Qatlib.Papers.LinearDiseq07.MainResults
