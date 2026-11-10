/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Superposition02.MainResults

namespace DyadicSource

def levelSize : ℕ → ℕ
  | 0 => 1
  | m + 1 => levelSize m * 2

@[simp] theorem levelSize_zero : levelSize 0 = 1 := rfl

@[simp] theorem levelSize_succ (m : ℕ) : levelSize (m + 1) = levelSize m * 2 := rfl

theorem levelSize_eq_pow (m : ℕ) : levelSize m = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [levelSize_succ, ih, pow_succ]

theorem levelSize_pos (m : ℕ) : 0 < levelSize m := by
  induction m with
  | zero => exact Nat.one_pos
  | succ m ih => rw [levelSize_succ]; exact Nat.mul_pos ih (by norm_num)

def leftChild (_m k : ℕ) : ℕ := 2 * k

def rightChild (_m k : ℕ) : ℕ := 2 * k + 1

@[simp] theorem leftChild_eq (m k : ℕ) : leftChild m k = 2 * k := rfl

@[simp] theorem rightChild_eq (m k : ℕ) : rightChild m k = 2 * k + 1 := rfl

theorem sum_range_even_odd (g : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), g k) =
      (∑ k ∈ Finset.range n, g (2 * k)) +
        (∑ k ∈ Finset.range n, g (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (fun k => g (2 * k)) n,
      Finset.sum_range_succ (fun k => g (2 * k + 1)) n, ih]
    ring

structure DyadicMass where

  mass : ℕ → ℕ → ℝ

  nonneg : ∀ (m k : ℕ), 0 ≤ mass m k

  total_zero : mass 0 0 = 1

  refine : ∀ (m k : ℕ), mass m k = mass (m + 1) (2 * k) + mass (m + 1) (2 * k + 1)

theorem level_total (D : DyadicMass) (m : ℕ) :
    (∑ k ∈ Finset.range (levelSize m), D.mass m k) = 1 := by
  induction m with
  | zero => simpa using D.total_zero
  | succ m ih =>
    have hsplit :
        (∑ k ∈ Finset.range (levelSize (m + 1)), D.mass (m + 1) k) =
          (∑ k ∈ Finset.range (levelSize m), D.mass (m + 1) (2 * k)) +
            (∑ k ∈ Finset.range (levelSize m), D.mass (m + 1) (2 * k + 1)) := by
      rw [levelSize_succ, Nat.mul_comm (levelSize m) 2]
      exact sum_range_even_odd (fun k => D.mass (m + 1) k) (levelSize m)
    rw [hsplit, ← Finset.sum_add_distrib, ← ih]
    exact Finset.sum_congr rfl (fun k _ => (D.refine m k).symm)

def DyadicMass.amplitude (D : DyadicMass) (m k : ℕ) : ℂ :=
  (Real.sqrt (D.mass m k) : ℂ)

theorem born_amplitude (D : DyadicMass) (m k : ℕ) :
    ‖D.amplitude m k‖ ^ 2 = D.mass m k := by
  rw [DyadicMass.amplitude, Complex.sq_norm, Complex.normSq_ofReal,
    Real.mul_self_sqrt (D.nonneg m k)]

theorem encodedState_normalized (D : DyadicMass) (m : ℕ) :
    (∑ k ∈ Finset.range (levelSize m), ‖D.amplitude m k‖ ^ 2) = 1 := by
  simp_rw [born_amplitude]
  exact level_total D m

def DyadicMass.ofCDF (F : ℝ → ℝ) (hmono : Monotone F) (h0 : F 0 = 0) (h1 : F 1 = 1) :
    DyadicMass where
  mass m k := F (((k : ℝ) + 1) / (levelSize m : ℝ)) - F ((k : ℝ) / (levelSize m : ℝ))
  nonneg m k := by
    apply sub_nonneg.mpr
    apply hmono
    have hL : (0 : ℝ) < (levelSize m : ℝ) := by exact_mod_cast levelSize_pos m
    apply div_le_div_of_nonneg_right _ (le_of_lt hL)
    linarith
  total_zero := by
    have harg1 : (((0 : ℕ) : ℝ) + 1) / (levelSize 0 : ℝ) = 1 := by
      norm_num [levelSize_zero]
    have harg0 : (((0 : ℕ) : ℝ)) / (levelSize 0 : ℝ) = 0 := by
      norm_num [levelSize_zero]
    rw [harg1, harg0, h0, h1]
    norm_num
  refine m k := by
    have hL : (levelSize m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (levelSize_pos m)
    have hleft : ((2 * k : ℕ) : ℝ) / (levelSize (m + 1) : ℝ) =
        (k : ℝ) / (levelSize m : ℝ) := by
      rw [levelSize_succ]
      push_cast
      field_simp
      try ring
    have hright : (((2 * k + 1 : ℕ) : ℝ) + 1) / (levelSize (m + 1) : ℝ) =
        ((k : ℝ) + 1) / (levelSize m : ℝ) := by
      rw [levelSize_succ]
      push_cast
      field_simp
      ring
    have hmid : (((2 * k : ℕ) : ℝ) + 1) / (levelSize (m + 1) : ℝ) =
        ((2 * k + 1 : ℕ) : ℝ) / (levelSize (m + 1) : ℝ) := by
      push_cast
      ring
    show F (((k : ℝ) + 1) / (levelSize m : ℝ)) - F ((k : ℝ) / (levelSize m : ℝ))
        = (F ((((2 * k : ℕ) : ℝ) + 1) / (levelSize (m + 1) : ℝ))
            - F (((2 * k : ℕ) : ℝ) / (levelSize (m + 1) : ℝ)))
          + (F ((((2 * k + 1 : ℕ) : ℝ) + 1) / (levelSize (m + 1) : ℝ))
            - F (((2 * k + 1 : ℕ) : ℝ) / (levelSize (m + 1) : ℝ)))
    rw [hleft, hright, hmid]
    ring

end DyadicSource

namespace ControlledRotation

open DyadicSource

def leftFraction (pL pR : ℝ) : ℝ := pL / (pL + pR)

theorem leftFraction_nonneg (pL pR : ℝ) (hL : 0 ≤ pL) (hp : 0 < pL + pR) :
    0 ≤ leftFraction pL pR :=
  div_nonneg hL (le_of_lt hp)

theorem leftFraction_le_one (pL pR : ℝ) (hR : 0 ≤ pR) (hp : 0 < pL + pR) :
    leftFraction pL pR ≤ 1 := by
  rw [leftFraction, div_le_one hp]
  linarith

theorem one_sub_leftFraction (pL pR : ℝ) (hp : 0 < pL + pR) :
    1 - leftFraction pL pR = pR / (pL + pR) := by
  rw [leftFraction]
  field_simp
  ring

def cosTheta (pL pR : ℝ) : ℝ := Real.sqrt (leftFraction pL pR)

def sinTheta (pL pR : ℝ) : ℝ := Real.sqrt (1 - leftFraction pL pR)

theorem cosTheta_sq (pL pR : ℝ) (hL : 0 ≤ pL) (hp : 0 < pL + pR) :
    cosTheta pL pR ^ 2 = leftFraction pL pR :=
  Real.sq_sqrt (leftFraction_nonneg pL pR hL hp)

theorem sinTheta_sq (pL pR : ℝ) (hR : 0 ≤ pR) (hp : 0 < pL + pR) :
    sinTheta pL pR ^ 2 = 1 - leftFraction pL pR :=
  Real.sq_sqrt (sub_nonneg.mpr (leftFraction_le_one pL pR hR hp))

theorem cos_sq_add_sin_sq (pL pR : ℝ) (hL : 0 ≤ pL) (hR : 0 ≤ pR)
    (hp : 0 < pL + pR) :
    cosTheta pL pR ^ 2 + sinTheta pL pR ^ 2 = 1 := by
  rw [cosTheta_sq pL pR hL hp, sinTheta_sq pL pR hR hp]
  ring

def rotate (pL pR x y : ℝ) : ℝ × ℝ :=
  (x * cosTheta pL pR - y * sinTheta pL pR,
   x * sinTheta pL pR + y * cosTheta pL pR)

theorem rotate_norm_sq (pL pR x y : ℝ) (hL : 0 ≤ pL) (hR : 0 ≤ pR)
    (hp : 0 < pL + pR) :
    (rotate pL pR x y).1 ^ 2 + (rotate pL pR x y).2 ^ 2 = x ^ 2 + y ^ 2 := by
  have hsum := cos_sq_add_sin_sq pL pR hL hR hp
  simp only [rotate]
  set c := cosTheta pL pR
  set s := sinTheta pL pR
  have h : (x * c - y * s) ^ 2 + (x * s + y * c) ^ 2 = (x ^ 2 + y ^ 2) * (c ^ 2 + s ^ 2) := by
    ring
  rw [h, hsum]
  ring

theorem refined_left_amplitude (a pL pR : ℝ) (ha : 0 ≤ a) (hp : 0 < pL + pR)
    (ha2 : a ^ 2 = pL + pR) :
    a * cosTheta pL pR = Real.sqrt pL := by
  have hfac : a = Real.sqrt (pL + pR) := by rw [← ha2, Real.sqrt_sq ha]
  rw [hfac, cosTheta, leftFraction, ← Real.sqrt_mul (le_of_lt hp)]
  congr 1
  field_simp

theorem refined_right_amplitude (a pL pR : ℝ) (ha : 0 ≤ a) (hp : 0 < pL + pR)
    (ha2 : a ^ 2 = pL + pR) :
    a * sinTheta pL pR = Real.sqrt pR := by
  have hfac : a = Real.sqrt (pL + pR) := by rw [← ha2, Real.sqrt_sq ha]
  rw [hfac, sinTheta, one_sub_leftFraction pL pR hp,
    ← Real.sqrt_mul (le_of_lt hp)]
  congr 1
  field_simp

theorem dyadic_refined_left_amplitude (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    D.amplitude m k *
        (cosTheta (D.mass (m + 1) (2 * k))
          (D.mass (m + 1) (2 * k + 1)) : ℂ) =
      D.amplitude (m + 1) (2 * k) := by
  set pL := D.mass (m + 1) (2 * k)
  set pR := D.mass (m + 1) (2 * k + 1)
  have hden : 0 < pL + pR := by rw [← D.refine m k]; exact hp
  have hreal : Real.sqrt (D.mass m k) * cosTheta pL pR = Real.sqrt pL :=
    refined_left_amplitude _ pL pR (Real.sqrt_nonneg _) hden (by
      rw [Real.sq_sqrt (D.nonneg m k), D.refine m k])
  have := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simpa [DyadicMass.amplitude, pL, pR, Complex.ofReal_mul] using this

theorem dyadic_refined_right_amplitude (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    D.amplitude m k *
        (sinTheta (D.mass (m + 1) (2 * k))
          (D.mass (m + 1) (2 * k + 1)) : ℂ) =
      D.amplitude (m + 1) (2 * k + 1) := by
  set pL := D.mass (m + 1) (2 * k)
  set pR := D.mass (m + 1) (2 * k + 1)
  have hden : 0 < pL + pR := by rw [← D.refine m k]; exact hp
  have hreal : Real.sqrt (D.mass m k) * sinTheta pL pR = Real.sqrt pR :=
    refined_right_amplitude _ pL pR (Real.sqrt_nonneg _) hden (by
      rw [Real.sq_sqrt (D.nonneg m k), D.refine m k])
  have := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simpa [DyadicMass.amplitude, pL, pR, Complex.ofReal_mul] using this

theorem dyadic_left_branch_probability (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    cosTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) ^ 2 =
      D.mass (m + 1) (2 * k) / D.mass m k := by
  rw [cosTheta_sq _ _ (D.nonneg _ _) (by rw [← D.refine m k]; exact hp),
    leftFraction, ← D.refine m k]

theorem dyadic_right_branch_probability (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    sinTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) ^ 2 =
      D.mass (m + 1) (2 * k + 1) / D.mass m k := by
  rw [sinTheta_sq _ _ (D.nonneg _ _) (by rw [← D.refine m k]; exact hp),
    one_sub_leftFraction _ _ (by rw [← D.refine m k]; exact hp),
    ← D.refine m k]

end ControlledRotation

open DyadicSource ControlledRotation

def sourceState (D : DyadicMass) (n : ℕ) : ℕ → ℂ :=
  fun i => if i < 2 ^ n then (Real.sqrt (D.mass n i) : ℂ) else 0

theorem sourceState_eq (D : DyadicMass) (n i : ℕ) (hi : i < 2 ^ n) :
    sourceState D n i = (Real.sqrt (D.mass n i) : ℂ) := by
  simp [sourceState, hi]

theorem sourceState_normalized (D : DyadicMass) (n : ℕ) :
    (∑ i ∈ Finset.range (2 ^ n), ‖sourceState D n i‖ ^ 2) = 1 := by
  rw [← levelSize_eq_pow]
  refine Eq.trans ?_ (encodedState_normalized D n)
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < 2 ^ n := by
    have h := Finset.mem_range.mp hi
    rwa [levelSize_eq_pow] at h
  have hstate : sourceState D n i = D.amplitude n i := by
    rw [sourceState_eq D n i hi', DyadicMass.amplitude]
  rw [hstate]

theorem source_encodedState_spec (D : DyadicMass) (n : ℕ) :
    (∀ i < 2 ^ n, sourceState D n i = (Real.sqrt (D.mass n i) : ℂ)) ∧
      (∑ i ∈ Finset.range (2 ^ n), ‖sourceState D n i‖ ^ 2) = 1 :=
  ⟨fun i hi => sourceState_eq D n i hi, sourceState_normalized D n⟩

theorem source_encodedState_spec_of_cdf
    (F : ℝ → ℝ) (hmono : Monotone F) (h0 : F 0 = 0) (h1 : F 1 = 1) (n : ℕ) :
    ∃ ψ : ℕ → ℂ,
      (∀ i < 2 ^ n, ψ i =
        (Real.sqrt (((DyadicMass.ofCDF F hmono h0 h1).mass n) i) : ℂ)) ∧
      (∑ i ∈ Finset.range (2 ^ n), ‖ψ i‖ ^ 2) = 1 :=
  ⟨sourceState (DyadicMass.ofCDF F hmono h0 h1) n,
    fun i hi => sourceState_eq (DyadicMass.ofCDF F hmono h0 h1) n i hi,
    sourceState_normalized (DyadicMass.ofCDF F hmono h0 h1) n⟩

theorem source_refinement_step (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    (D.amplitude m k *
        (cosTheta (D.mass (m + 1) (2 * k))
          (D.mass (m + 1) (2 * k + 1)) : ℂ) =
        D.amplitude (m + 1) (2 * k) ∧
      D.amplitude m k *
        (sinTheta (D.mass (m + 1) (2 * k))
          (D.mass (m + 1) (2 * k + 1)) : ℂ) =
        D.amplitude (m + 1) (2 * k + 1) ∧
      cosTheta (D.mass (m + 1) (2 * k))
          (D.mass (m + 1) (2 * k + 1)) ^ 2 =
        D.mass (m + 1) (2 * k) / D.mass m k ∧
      sinTheta (D.mass (m + 1) (2 * k))
          (D.mass (m + 1) (2 * k + 1)) ^ 2 =
        D.mass (m + 1) (2 * k + 1) / D.mass m k) :=
  ⟨dyadic_refined_left_amplitude D m k hp,
    dyadic_refined_right_amplitude D m k hp,
    dyadic_left_branch_probability D m k hp,
    dyadic_right_branch_probability D m k hp⟩

theorem discretization_size (n : ℕ) : levelSize n = 2 ^ n :=
  levelSize_eq_pow n

theorem refinement_rounds_strictMono : StrictMono levelSize := by
  intro a b hab
  rw [levelSize_eq_pow, levelSize_eq_pow]
  exact Nat.pow_lt_pow_right (by norm_num) hab

end Qatlib.Papers.Superposition02.MainResults
