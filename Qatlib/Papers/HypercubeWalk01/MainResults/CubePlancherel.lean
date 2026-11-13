/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypercubeWalk01.MainResults.CubeFourier
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Plancherel identities for the hypercube

This module establishes dual character orthogonality and Plancherel identities for the Fourier
convention used in [MooreRussell2001]. It bounds squared total variation by nonempty squared
Fourier coefficients and groups subset sums by cardinality.

## Main statements

* `sum_fourierCoeff_mul`: proves the bilinear Plancherel identity.
* `tvDist_sq_le`: bounds squared distance from uniform for a function of total mass one.
* `sum_by_card_nonempty`: rewrites nonempty-subset sums using binomial coefficients.

## References

* [Moore and Russell, 2001][MooreRussell2001]
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

/-- The cube vertex whose coordinates are all true. -/
def allTrue (n : ℕ) : Cube n := fun _ => true

/-- The sum of all subset characters at `z` is `2 ^ n` if `z = allTrue n` and zero otherwise. -/
theorem sum_chi_all (n : ℕ) (z : Cube n) :
    (∑ S : Finset (Fin n), chi S z) = if z = allTrue n then (2 : ℝ) ^ n else 0 := by
  classical
  have hfac : (∏ i : Fin n, ((if z i then (1 : ℝ) else -1) + 1))
      = ∑ S : Finset (Fin n), chi S z := by
    have hprod := Fintype.prod_add (fun i : Fin n => (if z i then (1 : ℝ) else -1))
      (fun _ => (1 : ℝ))
    rw [hprod]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [Finset.prod_const_one, mul_one]
    rfl
  rw [← hfac]
  by_cases hz : z = allTrue n
  · subst hz
    rw [if_pos rfl]
    have : ∀ i : Fin n, ((if (allTrue n) i then (1 : ℝ) else -1) + 1) = 2 := by
      intro i; norm_num [allTrue]
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const]
    simp [Fintype.card_fin]
  · rw [if_neg hz]
    have hne : ∃ i : Fin n, z i = false := by
      by_contra h
      apply hz
      funext i
      have hzi : z i = true := by
        cases hzi' : z i
        · exact absurd ⟨i, hzi'⟩ h
        · rfl
      simp [allTrue, hzi]
    obtain ⟨i, hi⟩ := hne
    have hif : ((if z i then (1 : ℝ) else -1) + 1) = 0 := by
      rw [hi]; norm_num
    exact Finset.prod_eq_zero (Finset.mem_univ i) hif

/-- Summing `chi S x * chi S y` over subsets gives `2 ^ n` for `x = y` and zero otherwise. -/
theorem sum_chi_mul_dual {n : ℕ} (x y : Cube n) :
    (∑ S : Finset (Fin n), chi S x * chi S y) = if x = y then (2 : ℝ) ^ n else 0 := by
  classical
  have hxy : ∀ S : Finset (Fin n),
      chi S x * chi S y = chi S (fun i => x i == y i) := by
    intro S
    simp only [chi]
    exact cubeChar_pair S x y
  simp only [hxy]
  have heq : ((fun i => x i == y i) = allTrue n) ↔ (x = y) := by
    constructor
    · intro h
      funext i
      have hi : (x i == y i) = true := congrFun h i
      simpa using hi
    · intro h
      subst h
      funext i
      simp [allTrue]
  rw [sum_chi_all, if_congr heq rfl rfl]

/-- The Fourier coefficient of a pointwise difference is the difference of the Fourier
coefficients. -/
theorem fourierCoeff_sub {n : ℕ} (P Q : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => P x - Q x) S = fourierCoeff P S - fourierCoeff Q S := by
  simp only [fourierCoeff, sub_mul, Finset.sum_sub_distrib]

/-- The Fourier coefficient of the constant function `c` is `c` times the sum of the
corresponding character. -/
theorem fourierCoeff_const {n : ℕ} (c : ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun _ : Cube n => c) S = c * (∑ x : Cube n, chi S x) := by
  simp only [fourierCoeff]
  rw [Finset.mul_sum]

/-- The uniform mass function has coefficient one at the empty subset and zero elsewhere. -/
theorem fourierCoeff_uniform {n : ℕ} (S : Finset (Fin n)) :
    fourierCoeff (fun _ : Cube n => uniformMass n) S = if S = ∅ then 1 else 0 := by
  rw [fourierCoeff_const]
  by_cases hS : S = ∅
  · subst hS
    rw [if_pos rfl]
    have hsum : (∑ x : Cube n, chi (∅ : Finset (Fin n)) x) = (2 : ℝ) ^ n := by
      simp only [chi, cubeChar, Finset.prod_empty]
      rw [Finset.sum_const, Finset.card_univ]
      simp [Cube]
    rw [hsum, uniformMass]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  · rw [if_neg hS]
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rw [sum_chi_eq_zero hne, mul_zero]

/-- The sum of products of matching Fourier coefficients equals `2 ^ n` times the pointwise
inner-product sum. -/
theorem sum_fourierCoeff_mul {n : ℕ} (P Q : Cube n → ℝ) :
    (∑ S : Finset (Fin n), fourierCoeff P S * fourierCoeff Q S)
      = (2 : ℝ) ^ n * ∑ x, P x * Q x := by
  classical
  have expand : (∑ S : Finset (Fin n), fourierCoeff P S * fourierCoeff Q S)
      = ∑ x : Cube n, ∑ y : Cube n,
          P x * Q y * (∑ S : Finset (Fin n), chi S x * chi S y) := by
    have h1 : (∑ S : Finset (Fin n), fourierCoeff P S * fourierCoeff Q S)
        = ∑ S, ∑ x : Cube n, ∑ y : Cube n,
            (P x * Q y) * (chi S x * chi S y) := by
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [fourierCoeff]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [h1]
    calc (∑ S : Finset (Fin n), ∑ x : Cube n, ∑ y : Cube n,
            (P x * Q y) * (chi S x * chi S y))
        = ∑ x : Cube n, ∑ y : Cube n, ∑ S : Finset (Fin n),
            (P x * Q y) * (chi S x * chi S y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ x : Cube n, ∑ y : Cube n,
            P x * Q y * (∑ S : Finset (Fin n), chi S x * chi S y) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
  rw [expand]
  have key : (∑ x : Cube n, ∑ y : Cube n,
        P x * Q y * (∑ S : Finset (Fin n), chi S x * chi S y))
      = ∑ x : Cube n, ∑ y : Cube n,
          P x * Q y * (if x = y then (2 : ℝ) ^ n else 0) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [sum_chi_mul_dual]
  rw [key]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl]; ring
  · intro y _ hyx
    rw [if_neg (fun h => hyx h.symm)]; ring
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The sum of squared Fourier coefficients equals `2 ^ n` times the sum of squared function
values. -/
theorem sum_fourierCoeff_sq {n : ℕ} (P : Cube n → ℝ) :
    (∑ S : Finset (Fin n), (fourierCoeff P S) ^ 2)
      = (2 : ℝ) ^ n * ∑ x, (P x) ^ 2 := by
  have h := sum_fourierCoeff_mul P P
  simpa [pow_two] using h

/-- The Boolean cube of dimension `n` has `2 ^ n` vertices. -/
theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  rw [Fintype.card_fun]
  simp

/-- The Fourier coefficient at the empty subset is the total sum of the function. -/
theorem fourierCoeff_empty {n : ℕ} (P : Cube n → ℝ) :
    fourierCoeff P (∅ : Finset (Fin n)) = ∑ x, P x := by
  simp [fourierCoeff, chi, cubeChar]

/-- For a real function of total mass one, squared distance from uniform is at most one quarter
of the sum of squared nonempty Fourier coefficients. -/
theorem tvDist_sq_le {n : ℕ} (P : Cube n → ℝ) (hP : ∑ x, P x = 1) :
    (tvDist P) ^ 2 ≤ (1 / 4) * ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
        (fourierCoeff P S) ^ 2 := by
  classical
  set f : Cube n → ℝ := fun x => P x - uniformMass n with hf
  have hfourier : ∀ S : Finset (Fin n),
      fourierCoeff f S = fourierCoeff P S - (if S = ∅ then 1 else 0) := by
    intro S
    rw [hf, fourierCoeff_sub, fourierCoeff_uniform]
  have hf_empty : fourierCoeff f (∅ : Finset (Fin n)) = 0 := by
    rw [hfourier, if_pos rfl, fourierCoeff_empty, hP]; ring

  have hparse := sum_fourierCoeff_sq f

  have hsq : (∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2)
      = ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), (fourierCoeff P S) ^ 2 := by
    have hsplit := Finset.sum_erase_add (Finset.univ) (fun S => (fourierCoeff f S) ^ 2)
      (Finset.mem_univ (∅ : Finset (Fin n)))
    have hcongr : ∀ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
        (fourierCoeff f S) ^ 2 = (fourierCoeff P S) ^ 2 := by
      intro S hS
      have hSne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
      rw [hfourier, if_neg hSne, sub_zero]
    rw [← hsplit, hf_empty, zero_pow two_ne_zero, add_zero]
    exact Finset.sum_congr rfl hcongr
  have hsum_f_sq : (∑ x : Cube n, (f x) ^ 2)
      = uniformMass n * ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
          (fourierCoeff P S) ^ 2 := by
    rw [hsq] at hparse
    rw [hparse, uniformMass]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp

  have hcs : (∑ x : Cube n, |f x|) ^ 2
      ≤ (2 : ℝ) ^ n * ∑ x : Cube n, (f x) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Cube n)))
      (f := fun x => |f x|)
    have hcard : ((Finset.univ : Finset (Cube n)).card : ℝ) = (2 : ℝ) ^ n := by
      rw [Finset.card_univ, card_cube]; push_cast; ring
    have habs : (∑ x : Cube n, |f x| ^ 2) = ∑ x : Cube n, (f x) ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sq_abs]
    calc (∑ x : Cube n, |f x|) ^ 2
        ≤ ((Finset.univ : Finset (Cube n)).card : ℝ) * ∑ x : Cube n, |f x| ^ 2 := h
      _ = (2 : ℝ) ^ n * ∑ x : Cube n, (f x) ^ 2 := by rw [hcard, habs]
  have htv : (tvDist P) ^ 2 = (1 / 4) * (∑ x : Cube n, |f x|) ^ 2 := by
    rw [tvDist, hf]
    ring
  rw [htv]
  calc (1 / 4) * (∑ x : Cube n, |f x|) ^ 2
      ≤ (1 / 4) * ((2 : ℝ) ^ n * ∑ x : Cube n, (f x) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = (1 / 4) * ((2 : ℝ) ^ n *
          (uniformMass n * ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
            (fourierCoeff P S) ^ 2)) := by rw [hsum_f_sq]
    _ = (1 / 4) * ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
          (fourierCoeff P S) ^ 2 := by
        rw [uniformMass]
        have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
        field_simp

/-- A sum over all subsets of a function of subset cardinality equals the corresponding
binomially weighted sum over cardinalities from zero to `n`. -/
theorem sum_by_card {n : ℕ} (g : ℕ → ℝ) :
    (∑ S : Finset (Fin n), g S.card)
      = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * g k := by
  classical
  have hunivp : (Finset.univ : Finset (Finset (Fin n))) = Finset.univ.powerset := by
    ext S
    simp
  rw [hunivp, Finset.sum_powerset_apply_card]
  simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A sum over nonempty subsets of a function of cardinality equals the binomially weighted sum
over cardinalities from one to `n`. -/
theorem sum_by_card_nonempty {n : ℕ} (g : ℕ → ℝ) :
    (∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), g S.card)
      = ∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℝ) * g (k + 1) := by
  classical
  have hsplit : (∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), g S.card) + g 0
      = ∑ S : Finset (Fin n), g S.card := by
    simpa only [Finset.card_empty] using
      Finset.sum_erase_add (Finset.univ) (fun S => g S.card)
        (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [sum_by_card] at hsplit

  have hshift : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * g k)
      = (∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℝ) * g (k + 1)) + g 0 := by
    rw [Finset.sum_range_succ']
    simp
  rw [hshift] at hsplit
  linarith

end Qatlib.Papers.HypercubeWalk01.MainResults
