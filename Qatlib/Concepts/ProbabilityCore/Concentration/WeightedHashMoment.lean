/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashData
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped BigOperators

private theorem hash_average_const
    {H : Type} [Fintype H] [Nonempty H] (c : ℝ) :
    finiteHashAverage (fun _ : H => c) = c := by
  have hn : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteHashAverage, nsmul_eq_mul, hn]

private theorem hash_average_add
    {H : Type} [Fintype H] (f g : H → ℝ) :
    finiteHashAverage (fun r => f r + g r) =
      finiteHashAverage f + finiteHashAverage g := by
  simp only [finiteHashAverage, Finset.sum_add_distrib, mul_add]

private theorem hash_average_sub
    {H : Type} [Fintype H] (f g : H → ℝ) :
    finiteHashAverage (fun r => f r - g r) =
      finiteHashAverage f - finiteHashAverage g := by
  simp only [finiteHashAverage, Finset.sum_sub_distrib, mul_sub]

private theorem hash_average_mul
    {H : Type} [Fintype H] (f : H → ℝ) (c : ℝ) :
    finiteHashAverage (fun r => f r * c) = finiteHashAverage f * c := by
  simp only [finiteHashAverage, ← Finset.sum_mul, mul_assoc]

private theorem hash_average_sum
    {H I : Type} [Fintype H] [Fintype I] (f : H → I → ℝ) :
    finiteHashAverage (fun r => ∑ i, f r i) =
      ∑ i, finiteHashAverage (fun r => f r i) := by
  unfold finiteHashAverage
  rw [Finset.sum_comm, Finset.mul_sum]

private noncomputable def realHashBucket
    {H X A : Type} [Fintype X] [DecidableEq A]
    (hash : H → X → A) (g : X → ℝ) (r : H) (a : A) : ℝ :=
  ∑ x, if hash r x = a then g x else 0

private theorem real_hash_bucket_mass
    {H X A : Type} [Fintype X] [Fintype A] [DecidableEq A]
    (hash : H → X → A) (g : X → ℝ) (r : H) :
    (∑ a, realHashBucket hash g r a) = ∑ x, g x := by
  unfold realHashBucket
  rw [Finset.sum_comm]
  simp

private theorem real_hash_bucket_energy
    {H X A : Type} [Fintype X] [Fintype A] [DecidableEq A]
    (hash : H → X → A) (g : X → ℝ) (r : H) :
    (∑ a, (realHashBucket hash g r a) ^ 2) =
      ∑ x, ∑ y, if hash r x = hash r y then g x * g y else 0 := by
  classical
  have hpair (x y : X) :
      (∑ a : A, (if hash r x = a then g x else 0) *
        (if hash r y = a then g y else 0)) =
      if hash r x = hash r y then g x * g y else 0 := by
    have hterm (a : A) :
        (if hash r x = a then g x else 0) *
          (if hash r y = a then g y else 0) =
        if hash r x = a then
          (if hash r x = hash r y then g x * g y else 0) else 0 := by
      by_cases hx : hash r x = a
      · rw [← hx]
        by_cases hxy : hash r x = hash r y <;> simp [hxy, eq_comm]
      · simp [hx]
    simp_rw [hterm]
    simp
  calc
    _ = ∑ a : A, ∑ x : X, ∑ y : X,
        (if hash r x = a then g x else 0) *
          (if hash r y = a then g y else 0) := by
      simp only [realHashBucket, pow_two, Fintype.sum_mul_sum]
    _ = ∑ x : X, ∑ y : X, ∑ a : A,
        (if hash r x = a then g x else 0) *
          (if hash r y = a then g y else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [hpair]

private theorem real_hash_centered_second_moment
    (H X A : Type) [Fintype H] [Nonempty H] [Fintype X]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (hash : H → X → A) (g : X → ℝ)
    (hcollision : ∀ x y : X, x ≠ y →
      finiteHashAverage (fun r : H => if hash r x = hash r y then 1 else 0) =
        (Fintype.card A : ℝ)⁻¹) :
    finiteHashAverage (fun r : H => ∑ a : A,
      (realHashBucket hash g r a -
        (Fintype.card A : ℝ)⁻¹ * ∑ x : X, g x) ^ 2) =
      (1 - (Fintype.card A : ℝ)⁻¹) * ∑ x : X, (g x) ^ 2 := by
  classical
  let α : ℝ := (Fintype.card A : ℝ)⁻¹
  let S : ℝ := ∑ x : X, g x
  have hn : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNa : (Fintype.card A : ℝ) * α = 1 := by
    exact mul_inv_cancel₀ hn
  have hcollision' (x y : X) :
      finiteHashAverage (fun r : H => if hash r x = hash r y then 1 else 0) =
        if x = y then 1 else α := by
    by_cases hxy : x = y
    · subst y
      simp only [if_true]
      exact hash_average_const 1
    · simp only [if_neg hxy]
      exact hcollision x y hxy
  have hweighted (x y : X) :
      finiteHashAverage (fun r : H =>
        if hash r x = hash r y then g x * g y else 0) =
        (if x = y then 1 else α) * (g x * g y) := by
    calc
      _ = finiteHashAverage (fun r : H =>
          (if hash r x = hash r y then 1 else 0) * (g x * g y)) := by
        congr 1
        funext r
        split <;> simp_all
      _ = _ := by rw [hash_average_mul, hcollision']
  have hscalar (x y : X) :
      (if x = y then 1 else α) * (g x * g y) =
        α * (g x * g y) + (1 - α) * (if x = y then (g x) ^ 2 else 0) := by
    by_cases hxy : x = y
    · subst y
      simp only [if_true]
      ring
    · simp only [if_neg hxy, mul_zero, add_zero]
  have hdiag : (∑ x : X, ∑ y : X, if x = y then (g x) ^ 2 else 0) =
      ∑ x : X, (g x) ^ 2 := by simp
  have henergy : finiteHashAverage (fun r : H =>
      ∑ a : A, (realHashBucket hash g r a) ^ 2) =
      α * S ^ 2 + (1 - α) * ∑ x : X, (g x) ^ 2 := by
    simp_rw [real_hash_bucket_energy, hash_average_sum, hweighted, hscalar,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hdiag]
    rw [← Finset.sum_mul]
    dsimp only [S]
    ring
  have hcenter (r : H) :
      (∑ a : A, (realHashBucket hash g r a - α * S) ^ 2) =
        (∑ a : A, (realHashBucket hash g r a) ^ 2) - α * S ^ 2 := by
    calc
      _ = ∑ a : A, ((realHashBucket hash g r a) ^ 2 -
          (2 * α * S) * realHashBucket hash g r a + α ^ 2 * S ^ 2) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ a : A, (realHashBucket hash g r a) ^ 2) -
          (2 * α * S) * S + (Fintype.card A : ℝ) * (α ^ 2 * S ^ 2) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, real_hash_bucket_mass, S, nsmul_eq_mul]
      _ = (∑ a : A, (realHashBucket hash g r a) ^ 2) +
          (α * S ^ 2) * ((Fintype.card A : ℝ) * α - 2) := by ring
      _ = _ := by rw [hNa]; ring
  change finiteHashAverage (fun r : H => ∑ a : A,
    (realHashBucket hash g r a - α * S) ^ 2) = _
  simp_rw [hcenter]
  rw [hash_average_sub, hash_average_const, henergy]
  ring

theorem weighted_hash_centered_second_moment
    (H X A : Type) [Fintype H] [Nonempty H] [Fintype X]
    [Fintype A] [Nonempty A] [DecidableEq A]
    (hash : H → X → A) (f : X → ℂ)
    (hcollision : ∀ x y : X, x ≠ y →
      finiteHashAverage (fun r : H => if hash r x = hash r y then 1 else 0) =
        (Fintype.card A : ℝ)⁻¹) :
    finiteHashAverage (fun r : H => ∑ a : A,
      Complex.normSq (weightedHashBucket hash f r a -
        (Fintype.card A : ℂ)⁻¹ * ∑ x : X, f x)) =
      (1 - (Fintype.card A : ℝ)⁻¹) * ∑ x : X, Complex.normSq (f x) := by
  classical
  have hre := real_hash_centered_second_moment H X A hash (fun x => (f x).re) hcollision
  have him := real_hash_centered_second_moment H X A hash (fun x => (f x).im) hcollision
  have hcast : (Fintype.card A : ℂ)⁻¹ = ((Fintype.card A : ℝ)⁻¹ : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  have hsplit (r : H) (a : A) :
      Complex.normSq (weightedHashBucket hash f r a -
        (Fintype.card A : ℂ)⁻¹ * ∑ x : X, f x) =
      (realHashBucket hash (fun x => (f x).re) r a -
        (Fintype.card A : ℝ)⁻¹ * ∑ x : X, (f x).re) ^ 2 +
      (realHashBucket hash (fun x => (f x).im) r a -
        (Fintype.card A : ℝ)⁻¹ * ∑ x : X, (f x).im) ^ 2 := by
    simp [weightedHashBucket, realHashBucket, hcast, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, pow_two, apply_ite]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hash_average_add, hre, him]
  simp only [Complex.normSq_apply, ← pow_two, Finset.sum_add_distrib]
  ring

end Qatlib.Concepts.ProbabilityCore.Concentration
