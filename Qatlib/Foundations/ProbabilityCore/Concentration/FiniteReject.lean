/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # The finite rejection weights and exact conditional law

Demand: LinearOptics10 Lemmas 40--41. The algebra is separated from an
efficient random-bit implementation. Actual acceptance weights are proved
to lie between zero and one when the input weights are probabilities.
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.ProbabilityCore.Concentration.FiniteReject

/-- Dividing an actual multiplicative error by a positive head mass gives the ratio error. -/
theorem ratioBound (zeta h e : ℝ) (hh : 0 < h) (he : |zeta*h-h| ≤ e) :
    |zeta-1| ≤ e/h := by
  have hid : zeta-1 = (zeta*h-h)/h := by field_simp
  rw [hid, abs_div, abs_of_pos hh]
  exact div_le_div_of_nonneg_right he hh.le

/-- The actual acceptance weight used by the finite rejection procedure. -/
noncomputable def accept (p q zeta δ : ℝ) : ℝ := zeta*q/((1+δ)^2*p)

/-- Positive source mass cancels from the actual accepted joint weight. -/
theorem joint (p q zeta δ : ℝ) (hp : p ≠ 0) :
    p*accept p q zeta δ = zeta*q/(1+δ)^2 := by
  unfold accept
  calc
    _ = (p*(zeta*q))/(p*(1+δ)^2) := by ring
    _ = _ := mul_div_mul_left _ _ hp

/-- Summing the actual accepted joint weights gives their exact acceptance mass. -/
theorem total {I : Type*} [Fintype I] (p q : I → ℝ) (zeta δ : ℝ)
    (hp : ∀ i, p i ≠ 0) (hq : ∑ i, q i = 1) :
    (∑ i, p i*accept (p i) (q i) zeta δ) = zeta/(1+δ)^2 := by
  simp_rw [joint _ _ _ _ (hp _)]
  rw [← Finset.sum_div, ← Finset.mul_sum, hq, mul_one]

/-- Normalizing the actual accepted joint weights gives the exact target law. -/
theorem conditional {I : Type*} [Fintype I] (p q : I → ℝ) (zeta δ : ℝ)
    (hp : ∀ i, p i ≠ 0) (hq : ∑ i, q i = 1) (hz : zeta ≠ 0) (hd : 1+δ ≠ 0)
    (i : I) : (p i*accept (p i) (q i) zeta δ)/
      (∑ j, p j*accept (p j) (q j) zeta δ) = q i := by
  rw [joint _ _ _ _ (hp i), total p q zeta δ hp hq]
  field_simp

/-- Actual probability weights produce a nonnegative acceptance weight. -/
theorem acceptNonneg (p q zeta δ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hz : 0 ≤ zeta) :
    0 ≤ accept p q zeta δ :=
  div_nonneg (mul_nonneg hz hq) (mul_nonneg (sq_nonneg _) hp)

/-- The pointwise ratio and scalar scale bound force the actual acceptance weight to be at most one. -/
theorem acceptLeOne (p q zeta δ : ℝ) (hp : 0 < p) (hd : 0 ≤ δ)
    (hz0 : 0 ≤ zeta) (hz1 : zeta ≤ 1+δ) (hqp : q/p ≤ 1+δ) :
    accept p q zeta δ ≤ 1 := by
  have hdpos : 0 < 1+δ := by linarith
  have he : accept p q zeta δ = (zeta*(q/p))/(1+δ)^2 := by
    unfold accept
    field_simp
  rw [he]
  apply (div_le_one (sq_pos_of_pos hdpos)).mpr
  calc
    _ ≤ zeta*(1+δ) := mul_le_mul_of_nonneg_left hqp hz0
    _ ≤ (1+δ)*(1+δ) := mul_le_mul_of_nonneg_right hz1 hdpos.le
    _ = _ := by ring

/-- The exact rejection mass is at most four delta throughout the fixed finite-error domain. -/
theorem rejectionLe (zeta δ : ℝ) (hd0 : 0 ≤ δ) (hz : 1-δ ≤ zeta) :
    1-zeta/(1+δ)^2 ≤ 4*δ := by
  have hd : 0 < 1+δ := by linarith
  have hs : 0 < (1+δ)^2 := sq_pos_of_pos hd
  have hlo := div_le_div_of_nonneg_right hz hs.le
  have he : 1-4*δ ≤ (1-δ)/(1+δ)^2 := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [sq_nonneg δ, mul_nonneg hd0 (sq_nonneg δ)]
  linarith

end Qatlib.Foundations.ProbabilityCore.Concentration.FiniteReject
