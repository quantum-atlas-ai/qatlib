/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Examples

open Matrix Polynomial

variable {q : ℂ}

lemma fiveRoot_ne_zero (hq5 : q ^ 5 = 1) : q ≠ 0 := by
  intro h
  rw [h] at hq5
  norm_num at hq5

lemma fiveRoot_ne_neg_one (hq5 : q ^ 5 = 1) : q ≠ -1 := by
  intro h
  rw [h] at hq5
  norm_num at hq5

lemma fiveRoot_add_one_ne_zero (hq5 : q ^ 5 = 1) : q + 1 ≠ 0 := by
  intro h
  exact fiveRoot_ne_neg_one hq5 (eq_neg_of_add_eq_zero_left h)

theorem fiveRoot_ratio_ne_pm_one (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1) :
    q / (-1) ≠ 1 ∧ q / (-1) ≠ -1 := by
  constructor
  · intro h
    have h' : q = -1 := by
      have hc : q / (-1) = -q := by ring
      rw [hc] at h
      linear_combination -h
    exact fiveRoot_ne_neg_one hq5 h'
  · intro h
    have h' : q = 1 := by
      have hc : q / (-1) = -q := by ring
      rw [hc] at h
      linear_combination -h
    exact hq1 h'

theorem negation_closed_two_element_forces_one
    (h : ∀ μ ∈ ({(-1 : ℂ), q} : Set ℂ), -μ ∈ ({(-1 : ℂ), q} : Set ℂ)) : q = 1 := by
  have h1 : -(-1 : ℂ) ∈ ({(-1 : ℂ), q} : Set ℂ) := h (-1) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, neg_neg] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by norm_num)
  · exact h1.symm

theorem not_mul_closed_two_element_fifth_root (ω : ℂ) (hω5 : ω ^ 5 = 1) (hω1 : ω ≠ 1) :
    ¬ ∀ μ ∈ ({(-1 : ℂ), q} : Set ℂ), ω * μ ∈ ({(-1 : ℂ), q} : Set ℂ) := by
  intro h
  have hω0 : ω ≠ 0 := fiveRoot_ne_zero hω5
  have hm1 : ω * (-1) ∈ ({(-1 : ℂ), q} : Set ℂ) := h (-1) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mul_neg, mul_one] at hm1
  rcases hm1 with hm1 | hm1
  · exact hω1 (neg_inj.mp hm1)
  · have hq : ω * (-ω) ∈ ({(-1 : ℂ), -ω} : Set ℂ) := by
      have h' : ω * (-ω) ∈ ({(-1 : ℂ), q} : Set ℂ) := h (-ω) (by rw [hm1]; simp)
      simpa only [← hm1] using h'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mul_neg] at hq
    rcases hq with hq | hq
    · have h2 : ω * ω = 1 := neg_inj.mp hq
      have hfac : (ω - 1) * (ω + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp hfac with h3 | h3
      · exact hω1 (sub_eq_zero.mp h3)
      · rw [eq_neg_of_add_eq_zero_left h3] at hω5
        norm_num at hω5
    · have h2 : ω * ω = ω := neg_inj.mp hq
      have hfac : ω * (ω - 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp hfac with h3 | h3
      · exact absurd h3 hω0
      · exact hω1 (sub_eq_zero.mp h3)

def sig1_21 : CM 2 := !![(-1 : ℂ), 0; 0, q]

def sig2_21 (s : ℂ) : CM 2 :=
  !![q ^ 2 / (q + 1), -(q * s) / (q + 1); -(q * s) / (q + 1), -(1 : ℂ) / (q + 1)]

@[simp] lemma sig1_21_zero_zero : sig1_21 (q := q) 0 0 = -1 := rfl

@[simp] lemma sig1_21_one_one : sig1_21 (q := q) 1 1 = q := rfl

lemma trace_sig2_21 (s : ℂ) (hq5 : q ^ 5 = 1) : (sig2_21 (q := q) s).trace = q - 1 := by
  have hq1 : q + 1 ≠ 0 := fiveRoot_add_one_ne_zero hq5
  rw [Matrix.trace_fin_two]
  simp only [sig2_21, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

lemma det_sig2_21 (s : ℂ) (hq5 : q ^ 5 = 1) (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    (sig2_21 (q := q) s).det = -q := by
  have hq0 : q ≠ 0 := fiveRoot_ne_zero hq5
  have hq1 : q + 1 ≠ 0 := fiveRoot_add_one_ne_zero hq5
  rw [Matrix.det_fin_two]
  simp only [sig2_21, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  linear_combination -hs

theorem charpoly_sig2_21 (s : ℂ) (hq5 : q ^ 5 = 1) (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    (sig2_21 (q := q) s).charpoly = (X - C (-1)) * (X - C q) := by
  rw [Matrix.charpoly_fin_two, trace_sig2_21 s hq5, det_sig2_21 s hq5 hs]
  have h1 : (C (q - 1) : ℂ[X]) = C q - 1 := by rw [map_sub, map_one]
  have h2 : (C (-q) : ℂ[X]) = -C q := by rw [map_neg]
  have h3 : (C (-1) : ℂ[X]) = -1 := by rw [map_neg, map_one]
  rw [h1, h2, h3]
  ring

theorem spectrum_sig2_21 (s : ℂ) (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1)
    (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    spectrum ℂ (sig2_21 (q := q) s) = {(-1 : ℂ), q} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_sig2_21 s hq5 hs]
  simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero,
    Set.mem_insert_iff, Set.mem_singleton_iff]

theorem hasEigenvalue_sig2_21 (s : ℂ) (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1)
    (hs : s ^ 2 * q = q ^ 2 + q + 1) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (sig2_21 (q := q) s)) μ ↔ μ = -1 ∨ μ = q := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    spectrum_sig2_21 s hq5 hq1 hs]
  simp

theorem braid_21 (s : ℂ) (hq5 : q ^ 5 = 1) (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    sig1_21 (q := q) * sig2_21 (q := q) s * sig1_21 (q := q) =
      sig2_21 (q := q) s * sig1_21 (q := q) * sig2_21 (q := q) s := by
  have hq1 : q + 1 ≠ 0 := fiveRoot_add_one_ne_zero hq5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sig1_21, sig2_21, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  all_goals simp
  all_goals field_simp
  all_goals first
    | linear_combination (-(1 + q ^ 2)) * hs
    | linear_combination (-(q ^ 2)) * hs
    | linear_combination q * hs
    | ring

def sig1_33 : CM 5 := Matrix.diagonal ![(-1 : ℂ), q, (-1), q, q]

def sig1_42 : CM 8 := Matrix.diagonal ![(-1 : ℂ), q, (-1), q, (-1), q, q, q]

theorem spectrum_sig1_33 : spectrum ℂ (sig1_33 (q := q)) = {(-1 : ℂ), q} := by
  rw [sig1_33, spectrum_diagonal]
  ext μ
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem spectrum_sig1_42 : spectrum ℂ (sig1_42 (q := q)) = {(-1 : ℂ), q} := by
  rw [sig1_42, spectrum_diagonal]
  ext μ
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem charpoly_sig1_42 :
    (sig1_42 (q := q)).charpoly = (X - C (-1)) ^ 3 * (X - C q) ^ 5 := by
  rw [sig1_42, Matrix.charpoly_diagonal]
  simp [Fin.prod_univ_eight]
  ring

theorem multiplicity_sig1_42 (hq5 : q ^ 5 = 1) :
    rootMultiplicity (-1) (sig1_42 (q := q)).charpoly = 3 ∧
      rootMultiplicity q (sig1_42 (q := q)).charpoly = 5 := by
  have hqm1 : q ≠ -1 := fiveRoot_ne_neg_one hq5
  have hne : ((X : ℂ[X]) - C q) ^ 5 ≠ 0 := pow_ne_zero 5 (monic_X_sub_C q).ne_zero
  have hne2 : ((X : ℂ[X]) - C (-1)) ^ 3 ≠ 0 := pow_ne_zero 3 (monic_X_sub_C (-1)).ne_zero
  have hroot : ¬ (((X : ℂ[X]) - C q) ^ 5).IsRoot (-1) := by
    intro hr
    rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C] at hr
    exact (pow_ne_zero 5 (by
      intro h0
      exact hqm1 (sub_eq_zero.mp h0).symm) : ((-1 : ℂ) - q) ^ 5 ≠ 0) hr
  have hroot2 : ¬ (((X : ℂ[X]) - C (-1)) ^ 3).IsRoot q := by
    intro hr
    rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C] at hr
    exact (pow_ne_zero 3 (by
      intro h0
      exact hqm1 (sub_eq_zero.mp h0)) : (q - (-1 : ℂ)) ^ 3 ≠ 0) hr
  constructor
  · rw [charpoly_sig1_42, mul_comm, rootMultiplicity_mul_X_sub_C_pow (p := ((X : ℂ[X]) - C q) ^ 5)
        (a := (-1)) (n := 3) hne, rootMultiplicity_eq_zero hroot]
  · rw [charpoly_sig1_42, rootMultiplicity_mul_X_sub_C_pow (p := ((X : ℂ[X]) - C (-1)) ^ 3)
        (a := q) (n := 5) hne2, rootMultiplicity_eq_zero hroot2]

end Qatlib.Papers.ModularFunct00.MainResults.Examples
