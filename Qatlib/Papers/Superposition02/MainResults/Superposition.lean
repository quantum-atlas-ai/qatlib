/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Sqrt

/-!
# Dyadic probability amplitudes and refinement

This module models the dyadic probability masses and local amplitude refinements of
[GroverRudolph2002]. `DyadicMass` records nonnegative masses, unit root mass, and binary
refinement; `DyadicMass.ofCDF` constructs such data from a monotone function with prescribed
endpoint values.

Square roots of these masses define normalized complex amplitudes. The branch factors `cosTheta`
and `sinTheta` split positive parent masses into the corresponding child amplitudes and
conditional branch probabilities.

## Main statements

* `level_total`: the masses at each dyadic level sum to one.
* `encodedState_normalized`: the level amplitudes have unit squared norm.
* `source_encodedState_spec_of_cdf`: constructs normalized amplitudes from a cumulative
  distribution function.
* `source_refinement_step`: collects the amplitude and branch-probability identities.

## References

* [Grover and Rudolph, 2002][GroverRudolph2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Superposition02.MainResults

namespace DyadicSource

/-- The number of bins at a dyadic level, starting at one and doubling at each successor. -/
def levelSize : ℕ → ℕ
  | 0 => 1
  | m + 1 => levelSize m * 2

/-- The initial dyadic level contains one bin. -/
@[simp] theorem levelSize_zero : levelSize 0 = 1 := rfl

/-- Each successor dyadic level has twice as many bins as its predecessor. -/
@[simp] theorem levelSize_succ (m : ℕ) : levelSize (m + 1) = levelSize m * 2 := rfl

/-- The size of dyadic level `m` equals `2 ^ m`. -/
theorem levelSize_eq_pow (m : ℕ) : levelSize m = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [levelSize_succ, ih, pow_succ]

/-- Every dyadic level has positive size. -/
theorem levelSize_pos (m : ℕ) : 0 < levelSize m := by
  induction m with
  | zero => exact Nat.one_pos
  | succ m ih => rw [levelSize_succ]; exact Nat.mul_pos ih (by norm_num)

/-- The left-child index `2 * k`; the level parameter does not affect the index. -/
def leftChild (_m k : ℕ) : ℕ := 2 * k

/-- The right-child index `2 * k + 1`; the level parameter does not affect the index. -/
def rightChild (_m k : ℕ) : ℕ := 2 * k + 1

/-- The left-child index of `k` equals `2 * k`. -/
@[simp] theorem leftChild_eq (m k : ℕ) : leftChild m k = 2 * k := rfl

/-- The right-child index of `k` equals `2 * k + 1`. -/
@[simp] theorem rightChild_eq (m k : ℕ) : rightChild m k = 2 * k + 1 := rfl

/-- Splits a sum over the first `2 * n` natural numbers into its even-indexed and odd-indexed
sums. -/
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

/-- Nonnegative masses on dyadic nodes with unit root mass and each parent mass equal to the sum
of its two child masses. -/
structure DyadicMass where

  mass : ℕ → ℕ → ℝ

  nonneg : ∀ (m k : ℕ), 0 ≤ mass m k

  total_zero : mass 0 0 = 1

  refine : ∀ (m k : ℕ), mass m k = mass (m + 1) (2 * k) + mass (m + 1) (2 * k + 1)

/-- At each level, the dyadic bin masses sum to one [GroverRudolph2002]. -/
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

/-- The complex amplitude given by the nonnegative real square root of a dyadic mass. -/
def DyadicMass.amplitude (D : DyadicMass) (m k : ℕ) : ℂ :=
  (Real.sqrt (D.mass m k) : ℂ)

/-- The squared norm of a dyadic amplitude equals its mass [GroverRudolph2002]. -/
theorem born_amplitude (D : DyadicMass) (m k : ℕ) :
    ‖D.amplitude m k‖ ^ 2 = D.mass m k := by
  rw [DyadicMass.amplitude, Complex.sq_norm, Complex.normSq_ofReal,
    Real.mul_self_sqrt (D.nonneg m k)]

/-- The squared norms of the amplitudes at each dyadic level sum to one [GroverRudolph2002]. -/
theorem encodedState_normalized (D : DyadicMass) (m : ℕ) :
    (∑ k ∈ Finset.range (levelSize m), ‖D.amplitude m k‖ ^ 2) = 1 := by
  simp_rw [born_amplitude]
  exact level_total D m

/-- Constructs dyadic masses as successive increments of a monotone real function satisfying `F
0 = 0` and `F 1 = 1` [GroverRudolph2002]. -/
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

/-- The left branch fraction `pL / (pL + pR)` [GroverRudolph2002]. -/
def leftFraction (pL pR : ℝ) : ℝ := pL / (pL + pR)

/-- The left branch fraction is nonnegative when `pL ≥ 0` and the total mass is positive. -/
theorem leftFraction_nonneg (pL pR : ℝ) (hL : 0 ≤ pL) (hp : 0 < pL + pR) :
    0 ≤ leftFraction pL pR :=
  div_nonneg hL (le_of_lt hp)

/-- The left branch fraction is at most one when `pR ≥ 0` and the total mass is positive. -/
theorem leftFraction_le_one (pL pR : ℝ) (hR : 0 ≤ pR) (hp : 0 < pL + pR) :
    leftFraction pL pR ≤ 1 := by
  rw [leftFraction, div_le_one hp]
  linarith

/-- For positive total mass, the complement of the left branch fraction equals the right branch
fraction. -/
theorem one_sub_leftFraction (pL pR : ℝ) (hp : 0 < pL + pR) :
    1 - leftFraction pL pR = pR / (pL + pR) := by
  rw [leftFraction]
  field_simp
  ring

/-- The nonnegative square root of the left branch fraction [GroverRudolph2002]. -/
def cosTheta (pL pR : ℝ) : ℝ := Real.sqrt (leftFraction pL pR)

/-- The nonnegative square root of the complement of the left branch fraction
[GroverRudolph2002]. -/
def sinTheta (pL pR : ℝ) : ℝ := Real.sqrt (1 - leftFraction pL pR)

/-- For nonnegative left mass and positive total mass, the square of the cosine branch factor
equals the left branch fraction. -/
theorem cosTheta_sq (pL pR : ℝ) (hL : 0 ≤ pL) (hp : 0 < pL + pR) :
    cosTheta pL pR ^ 2 = leftFraction pL pR :=
  Real.sq_sqrt (leftFraction_nonneg pL pR hL hp)

/-- For nonnegative right mass and positive total mass, the square of the sine branch factor
equals the complement of the left branch fraction. -/
theorem sinTheta_sq (pL pR : ℝ) (hR : 0 ≤ pR) (hp : 0 < pL + pR) :
    sinTheta pL pR ^ 2 = 1 - leftFraction pL pR :=
  Real.sq_sqrt (sub_nonneg.mpr (leftFraction_le_one pL pR hR hp))

/-- For nonnegative branch masses with positive sum, the squares of the two branch factors sum
to one [GroverRudolph2002]. -/
theorem cos_sq_add_sin_sq (pL pR : ℝ) (hL : 0 ≤ pL) (hR : 0 ≤ pR)
    (hp : 0 < pL + pR) :
    cosTheta pL pR ^ 2 + sinTheta pL pR ^ 2 = 1 := by
  rw [cosTheta_sq pL pR hL hp, sinTheta_sq pL pR hR hp]
  ring

/-- Applies the real two-coordinate rotation formula using `cosTheta pL pR` and `sinTheta pL
pR`. -/
def rotate (pL pR x y : ℝ) : ℝ × ℝ :=
  (x * cosTheta pL pR - y * sinTheta pL pR,
   x * sinTheta pL pR + y * cosTheta pL pR)

/-- For nonnegative branch masses with positive sum, `rotate` preserves the sum of squares of
the two coordinates [GroverRudolph2002]. -/
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

/-- If `a` is nonnegative and `a ^ 2 = pL + pR > 0`, then `a * cosTheta pL pR = √pL`. -/
theorem refined_left_amplitude (a pL pR : ℝ) (ha : 0 ≤ a) (hp : 0 < pL + pR)
    (ha2 : a ^ 2 = pL + pR) :
    a * cosTheta pL pR = Real.sqrt pL := by
  have hfac : a = Real.sqrt (pL + pR) := by rw [← ha2, Real.sqrt_sq ha]
  rw [hfac, cosTheta, leftFraction, ← Real.sqrt_mul (le_of_lt hp)]
  congr 1
  field_simp

/-- If `a` is nonnegative and `a ^ 2 = pL + pR > 0`, then `a * sinTheta pL pR = √pR`. -/
theorem refined_right_amplitude (a pL pR : ℝ) (ha : 0 ≤ a) (hp : 0 < pL + pR)
    (ha2 : a ^ 2 = pL + pR) :
    a * sinTheta pL pR = Real.sqrt pR := by
  have hfac : a = Real.sqrt (pL + pR) := by rw [← ha2, Real.sqrt_sq ha]
  rw [hfac, sinTheta, one_sub_leftFraction pL pR hp,
    ← Real.sqrt_mul (le_of_lt hp)]
  congr 1
  field_simp

/-- For positive parent mass, the parent amplitude times the cosine branch factor equals the
left-child amplitude [GroverRudolph2002]. -/
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

/-- For positive parent mass, the parent amplitude times the sine branch factor equals the
right-child amplitude [GroverRudolph2002]. -/
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

/-- For positive parent mass, the squared cosine branch factor equals the ratio of left-child
mass to parent mass [GroverRudolph2002]. -/
theorem dyadic_left_branch_probability (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    cosTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) ^ 2 =
      D.mass (m + 1) (2 * k) / D.mass m k := by
  rw [cosTheta_sq _ _ (D.nonneg _ _) (by rw [← D.refine m k]; exact hp),
    leftFraction, ← D.refine m k]

/-- For positive parent mass, the squared sine branch factor equals the ratio of right-child
mass to parent mass [GroverRudolph2002]. -/
theorem dyadic_right_branch_probability (D : DyadicMass) (m k : ℕ)
    (hp : 0 < D.mass m k) :
    sinTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) ^ 2 =
      D.mass (m + 1) (2 * k + 1) / D.mass m k := by
  rw [sinTheta_sq _ _ (D.nonneg _ _) (by rw [← D.refine m k]; exact hp),
    one_sub_leftFraction _ _ (by rw [← D.refine m k]; exact hp),
    ← D.refine m k]

end ControlledRotation

open DyadicSource ControlledRotation

/-- The complex amplitude function equal to the square root of each level-`n` mass on indices
below `2 ^ n` and zero elsewhere [GroverRudolph2002]. -/
def sourceState (D : DyadicMass) (n : ℕ) : ℕ → ℂ :=
  fun i => if i < 2 ^ n then (Real.sqrt (D.mass n i) : ℂ) else 0

/-- On indices below `2 ^ n`, `sourceState D n` equals the square root of the corresponding
dyadic mass [GroverRudolph2002]. -/
theorem sourceState_eq (D : DyadicMass) (n i : ℕ) (hi : i < 2 ^ n) :
    sourceState D n i = (Real.sqrt (D.mass n i) : ℂ) := by
  simp [sourceState, hi]

/-- The squared norms of `sourceState D n` over the first `2 ^ n` indices sum to one
[GroverRudolph2002]. -/
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

/-- The source state has the prescribed square-root amplitudes on its dyadic level and unit
total squared norm [GroverRudolph2002]. -/
theorem source_encodedState_spec (D : DyadicMass) (n : ℕ) :
    (∀ i < 2 ^ n, sourceState D n i = (Real.sqrt (D.mass n i) : ℂ)) ∧
      (∑ i ∈ Finset.range (2 ^ n), ‖sourceState D n i‖ ^ 2) = 1 :=
  ⟨fun i hi => sourceState_eq D n i hi, sourceState_normalized D n⟩

/-- A monotone real function with values zero and one at the endpoints yields a normalized
amplitude function for its level-`n` dyadic masses [GroverRudolph2002]. -/
theorem source_encodedState_spec_of_cdf
    (F : ℝ → ℝ) (hmono : Monotone F) (h0 : F 0 = 0) (h1 : F 1 = 1) (n : ℕ) :
    ∃ ψ : ℕ → ℂ,
      (∀ i < 2 ^ n, ψ i =
        (Real.sqrt (((DyadicMass.ofCDF F hmono h0 h1).mass n) i) : ℂ)) ∧
      (∑ i ∈ Finset.range (2 ^ n), ‖ψ i‖ ^ 2) = 1 :=
  ⟨sourceState (DyadicMass.ofCDF F hmono h0 h1) n,
    fun i hi => sourceState_eq (DyadicMass.ofCDF F hmono h0 h1) n i hi,
    sourceState_normalized (DyadicMass.ofCDF F hmono h0 h1) n⟩

/-- For positive parent mass, collects both child-amplitude identities and both conditional
branch-probability identities [GroverRudolph2002]. -/
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

/-- A level with `n` binary refinements has exactly `2 ^ n` bins [GroverRudolph2002]. -/
theorem discretization_size (n : ℕ) : levelSize n = 2 ^ n :=
  levelSize_eq_pow n

/-- The number of dyadic bins is strictly increasing with the refinement level
[GroverRudolph2002]. -/
theorem refinement_rounds_strictMono : StrictMono levelSize := by
  intro a b hab
  rw [levelSize_eq_pow, levelSize_eq_pow]
  exact Nat.pow_lt_pow_right (by norm_num) hab

end Qatlib.Papers.Superposition02.MainResults
