/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Action regularity for the sequential discrimination planner

For fixed beliefs and an observation, Lemmas 5.14 and 5.15 of
arXiv:2604.15393v1 control changes in its probability and posterior
across actions. The inputs are finite likelihood vectors for that
one observation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SeqQsdJeong26.Approximation

variable {ι : Type*} [Fintype ι]

/-- The probability of one outcome under the fixed prior. -/
def observationMass (belief likelihood : ι → ℝ) : ℝ :=
  ∑ i, belief i * likelihood i

/-- One posterior coordinate at a positive-probability observation. -/
def observationPosterior (belief likelihood : ι → ℝ) (i : ι) : ℝ :=
  belief i * likelihood i / observationMass belief likelihood

/-- Lemma 5.14. Averaging with one normalized nonnegative prior preserves
a pointwise bound on the likelihood variation. -/
theorem observationMass_lipschitz (belief p q : ι → ℝ)
    (hb : ∀ i, 0 ≤ belief i) (hnorm : ∑ i, belief i = 1)
    (radius : ℝ) (h : ∀ i, |p i - q i| ≤ radius) :
    |observationMass belief p - observationMass belief q| ≤ radius := by
  unfold observationMass
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ i, |belief i * (p i - q i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, belief i * radius := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hb i)]
      exact mul_le_mul_of_nonneg_left (h i) (hb i)
    _ = radius := by rw [← Finset.sum_mul, hnorm, one_mul]

/-- Lemma 5.15. When both outcome probabilities are at least eta, posterior
variation is controlled by the direct likelihood term and the normalization term. -/
theorem observationPosterior_lipschitz (belief p q : ι → ℝ)
    (hb : ∀ i, 0 ≤ belief i) (hnorm : ∑ i, belief i = 1)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (radius eta : ℝ)
    (hr : 0 ≤ radius) (heta : 0 < eta)
    (hpMass : eta ≤ observationMass belief p) (hqMass : eta ≤ observationMass belief q)
    (h : ∀ i, |p i - q i| ≤ radius) (i : ι) :
    |observationPosterior belief p i - observationPosterior belief q i| ≤
      radius / eta + radius / eta ^ 2 := by
  classical
  let x := observationMass belief p
  let y := observationMass belief q
  have hx : 0 < x := heta.trans_le hpMass
  have hy : 0 < y := heta.trans_le hqMass
  have hi : belief i ≤ 1 := by
    rw [← hnorm]
    exact Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
  have hcoeff : 0 ≤ belief i * q i := mul_nonneg (hb i) (hq i).1
  have hcoeff₁ : belief i * q i ≤ 1 := (mul_le_of_le_one_right (hb i) (hq i).2).trans hi
  have hmass : |y - x| ≤ radius := by
    rw [abs_sub_comm]
    exact observationMass_lipschitz belief p q hb hnorm radius h
  have hprod : eta ^ 2 ≤ x * y := by
    rw [sq]
    exact mul_le_mul hpMass hqMass heta.le hx.le
  have heq : observationPosterior belief p i - observationPosterior belief q i =
      belief i * (p i - q i) / x + belief i * q i * (y - x) / (x * y) := by
    change belief i * p i / x - belief i * q i / y = _
    field_simp [hx.ne', hy.ne']
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos hx, abs_mul, abs_of_nonneg (hb i)]
    have hnum : belief i * |p i - q i| ≤ radius :=
      (mul_le_mul_of_nonneg_left (h i) (hb i)).trans (mul_le_of_le_one_left hr hi)
    exact (div_le_div_of_nonneg_right hnum hx.le).trans
      (div_le_div_of_nonneg_left hr heta hpMass)
  · rw [abs_div, abs_of_pos (mul_pos hx hy), abs_mul, abs_of_nonneg hcoeff]
    have hnum : belief i * q i * |y - x| ≤ radius :=
      (mul_le_mul_of_nonneg_left hmass hcoeff).trans (mul_le_of_le_one_left hr hcoeff₁)
    exact (div_le_div_of_nonneg_right hnum (mul_nonneg hx.le hy.le)).trans
      (div_le_div_of_nonneg_left hr (sq_pos_of_pos heta) hprod)

end Qatlib.Papers.SeqQsdJeong26.Approximation
