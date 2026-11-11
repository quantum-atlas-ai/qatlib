/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.BooleanCubeFourier

/-!
# Fourier characters on the Boolean hypercube

This module fixes the hypercube characters `chi`, uniform and parity mass functions, and total
variation expressions used in [MooreRussell2001]. It proves orthogonality, Fourier synthesis,
and a lower bound on total variation from a nonempty Fourier coefficient.

## Main statements

* `sum_chi_mul`: proves character orthogonality.
* `fourierCoeff_synthesis`: recovers coefficients from their Fourier synthesis.
* `abs_fourierCoeff_le_two_tv`: bounds a nonempty Fourier coefficient by twice the distance from
  uniform.

## References

* [Moore and Russell, 2001][MooreRussell2001]
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

/-- The Boolean hypercube of dimension `n`, represented by functions `Fin n → Bool`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- The real cube character indexed by `S`, with each selected true coordinate contributing `1`
and each selected false coordinate contributing `-1`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := cubeChar S x

/-- The uniform mass `1 / 2 ^ n` at a vertex of the `n`-dimensional cube. -/
noncomputable def uniformMass (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- The mass function equal to `1 / 2 ^ (n - 1)` at vertices of even true-coordinate weight and
zero at odd weight. -/
noncomputable def parityUniformMass (n : ℕ) (x : Cube n) : ℝ :=
  if (∑ i, if x i then (1 : ℕ) else 0) % 2 = 0 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0

/-- Half the sum of absolute differences between `P` and the uniform mass function. -/
noncomputable def tvDist {n : ℕ} (P : Cube n → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |P x - uniformMass n|

/-- Half the sum of absolute differences between `P` and the even-parity mass function. -/
noncomputable def tvDistParity {n : ℕ} (P : Cube n → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |P x - parityUniformMass n x|

/-- The unnormalized Fourier coefficient `∑ x, P x * chi S x`. -/
noncomputable def fourierCoeff {n : ℕ} (P : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ x, P x * chi S x

/-- The absolute value of every cube character is at most one. -/
lemma chi_abs_le_one {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : |chi S x| ≤ 1 := by
  have hfac : ∀ i ∈ S, |(if x i then (1 : ℝ) else -1)| = 1 := by
    intro i _
    cases x i <;> simp
  simp only [chi, cubeChar]
  rw [Finset.abs_prod, Finset.prod_congr rfl hfac, Finset.prod_const_one]

/-- The product of the characters indexed by `S` and `T` is the character indexed by their
symmetric difference. -/
lemma chi_mul {n : ℕ} (S T : Finset (Fin n)) (x : Cube n) :
    chi S x * chi T x = chi (S ∆ T) x := by
  simp only [chi]
  exact cubeChar_mul S T x

/-- Updating coordinate `i` factors the character into its updated coordinate sign and the
character indexed by `S.erase i`. -/
lemma chi_update {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (b : Bool) (x : Cube n) :
    chi S (Function.update x i b) =
      (if i ∈ S then (if b then (1 : ℝ) else -1) else 1) * chi (S.erase i) x := by
  classical
  by_cases hi : i ∈ S
  · have hleft : chi S (Function.update x i b)
        = (∏ j ∈ S.erase i, (if x j then (1 : ℝ) else -1)) * (if b then (1 : ℝ) else -1) := by
      simp only [chi, cubeChar]
      rw [← Finset.prod_erase_mul S
        (fun j => if Function.update x i b j then (1 : ℝ) else -1) hi]
      congr 1
      · refine Finset.prod_congr rfl fun j hj => ?_
        have hji : j ≠ i := fun h => (Finset.notMem_erase i S) (h ▸ hj)
        simp [hji]
      · simp
    have hright : chi (S.erase i) x = ∏ j ∈ S.erase i, (if x j then (1 : ℝ) else -1) := by
      simp only [chi, cubeChar]
    rw [hleft, hright, if_pos hi, mul_comm]
  · have herase : S.erase i = S := Finset.erase_eq_of_notMem hi
    have hleft : chi S (Function.update x i b) = chi S x := by
      simp only [chi, cubeChar]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [hji]
    rw [hleft, herase, if_neg hi, one_mul]

/-- Flipping a coordinate belonging to `S` negates the character `chi S`. -/
lemma chi_flip {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (x : Cube n) :
    chi S (Function.update x i (!x i)) = - chi S x := by
  have hx : chi S x
      = (if i ∈ S then (if x i then (1 : ℝ) else -1) else 1) * chi (S.erase i) x := by
    conv_lhs => rw [← Function.update_eq_self (f := x) (a := i)]
    exact chi_update S i (x i) x
  rw [chi_update, hx, if_pos hi, if_pos hi]
  have hsign : (if (!x i) then (1 : ℝ) else -1) = - (if x i then (1 : ℝ) else -1) := by
    cases x i <;> simp
  rw [hsign]
  ring

/-- The sum of a character indexed by a nonempty subset over the whole cube is zero. -/
theorem sum_chi_eq_zero {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    ∑ x : Cube n, chi S x = 0 := by
  classical
  obtain ⟨i, hi⟩ := hS
  refine Finset.sum_ninvolution (f := fun x : Cube n => chi S x)
    (fun x => Function.update x i (!x i)) ?_ ?_ ?_ ?_
  · intro x
    change chi S x + chi S (Function.update x i (!x i)) = 0
    rw [chi_flip S i hi x]
    ring
  · intro x _ hfix
    have hcoord := congrFun hfix i
    simp at hcoord
  · intro x
    exact Finset.mem_univ _
  · intro x
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]

/-- A nonempty Fourier coefficient is unchanged when the uniform mass is subtracted from `P`. -/
theorem fourierCoeff_eq_centered {n : ℕ} {P : Cube n → ℝ} {S : Finset (Fin n)}
    (hS : S.Nonempty) :
    fourierCoeff P S = ∑ x, (P x - uniformMass n) * chi S x := by
  classical
  have hzero : ∑ x : Cube n, chi S x = 0 := sum_chi_eq_zero hS
  have hsplit : (∑ x, (P x - uniformMass n) * chi S x)
      = (∑ x, P x * chi S x) - (∑ x, uniformMass n * chi S x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hsplit, ← Finset.mul_sum, hzero, mul_zero, sub_zero]
  rfl

/-- The absolute value of every nonempty Fourier coefficient is at most twice `tvDist P`. -/
theorem abs_fourierCoeff_le_two_tv {n : ℕ} (P : Cube n → ℝ) {S : Finset (Fin n)}
    (hS : S.Nonempty) :
    |fourierCoeff P S| ≤ 2 * tvDist P := by
  classical
  rw [fourierCoeff_eq_centered hS]
  have hstep : |∑ x, (P x - uniformMass n) * chi S x|
      ≤ ∑ x, |P x - uniformMass n| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_mul]
    calc |P x - uniformMass n| * |chi S x|
        ≤ |P x - uniformMass n| * 1 :=
          mul_le_mul_of_nonneg_left (chi_abs_le_one S x) (abs_nonneg _)
      _ = |P x - uniformMass n| := mul_one _
  have htv : 2 * tvDist P = ∑ x, |P x - uniformMass n| := by
    rw [tvDist]
    ring
  rw [htv]
  exact hstep

/-- The sum of `chi S x * chi T x` over the cube is `2 ^ n` when `S = T` and zero otherwise. -/
theorem sum_chi_mul {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Cube n, chi S x * chi T x) = if S = T then (2 : ℝ) ^ n else 0 := by
  classical
  have hprod : ∀ x : Cube n, chi S x * chi T x = chi (S ∆ T) x := fun x => chi_mul S T x
  simp only [hprod]
  by_cases hST : S = T
  · subst hST
    have hsym : S ∆ S = (∅ : Finset (Fin n)) := by simp
    rw [hsym, if_pos rfl]
    simp only [chi, cubeChar, Finset.prod_empty]
    rw [Finset.sum_const, Finset.card_univ]
    simp
  · have hnonempty : (S ∆ T).Nonempty :=
      Finset.symmDiff_nonempty.mpr hST
    rw [if_neg hST, sum_chi_eq_zero hnonempty]

/-- Fourier synthesis with the factor `uniformMass n` recovers each supplied coefficient
exactly. -/
theorem fourierCoeff_synthesis {n : ℕ} (c : Finset (Fin n) → ℝ) (T : Finset (Fin n)) :
    fourierCoeff (fun x => uniformMass n * ∑ S, c S * chi S x) T = c T := by
  classical
  have hcard : uniformMass n * (2 : ℝ) ^ n = 1 := by
    rw [uniformMass]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    exact inv_mul_cancel₀ h2
  rw [fourierCoeff]
  have hexp : ∀ x : Cube n,
      (uniformMass n * ∑ S, c S * chi S x) * chi T x
        = ∑ S, uniformMass n * (c S * (chi S x * chi T x)) := by
    intro x
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  simp only [hexp]
  rw [Finset.sum_comm]
  have hinner : ∀ S : Finset (Fin n),
      (∑ x : Cube n, uniformMass n * (c S * (chi S x * chi T x)))
        = c S * (uniformMass n * (if S = T then (2 : ℝ) ^ n else 0)) := by
    intro S
    have hstep : ∀ x : Cube n,
        uniformMass n * (c S * (chi S x * chi T x))
          = (uniformMass n * c S) * (chi S x * chi T x) := by
      intro x
      ring
    simp only [hstep]
    rw [← Finset.mul_sum, sum_chi_mul]
    ring
  simp only [hinner]
  rw [Finset.sum_eq_single T]
  · rw [if_pos rfl, hcard, mul_one]
  · intro S _ hST
    rw [if_neg hST, mul_zero, mul_zero]
  · intro hT
    exact absurd (Finset.mem_univ T) hT

end Qatlib.Papers.HypercubeWalk01.MainResults
