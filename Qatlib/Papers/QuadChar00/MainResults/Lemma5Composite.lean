/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Lemma1FullAmplitude
import Qatlib.Papers.QuadChar00.MainResults.Lemma5GaussSums
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Quadratic Gauss sums for composite moduli

This module relates `jacobiGaussSum` to a Dirichlet character Gauss sum and computes its square
and norm for odd squarefree moduli. Congruence classes modulo four determine its value up to
sign. See [VanDamHallgren2000].

## Main statements

* `jacobiGaussSum_sq`: For odd squarefree `n > 1`, the square of the Jacobi Gauss sum is the
  Jacobi character at minus one times `n`.
* `jacobiGaussSum_norm`: For odd squarefree `n > 1`, the Jacobi Gauss sum has norm `Real.sqrt
  n`.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators
open MulChar ZMod

/-- The Jacobi Gauss sum equals the Gauss sum of `jacobiDirichlet` against the standard additive
character. -/
theorem jacobiGaussSum_eq_dirichlet (n : ℕ) [NeZero n] :
    jacobiGaussSum n =
      gaussSum (jacobiDirichlet n) (ZMod.stdAddChar (N := n)) := by
  rw [jacobiGaussSum]
  rfl

/-- For an odd nonzero modulus, the Jacobi character at minus one equals `χ₄ n`. -/
lemma jacobiCharZMod_neg_one_eq_chi4 (n : ℕ) [NeZero n] (hn : Odd n) :
    jacobiCharZMod n (-1) = χ₄ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    have := NeZero.ne n
    omega⟩
  rw [jacobiCharZMod, ZMod.val_neg_one]
  have hmod : (m : ℤ) % ((m : ℤ) + 1) = (-1 : ℤ) % ((m : ℤ) + 1) := by
    apply Int.modEq_iff_dvd.mpr
    have h : (-1 : ℤ) - (m : ℤ) = -((m : ℤ) + 1) := by ring
    rw [h]
    exact dvd_neg.mpr (dvd_refl _)
  rw [jacobiSym.mod_left' hmod]
  exact jacobiSym.at_neg_one (by simpa using hn)

/-- For odd squarefree `n > 1`, the square of the Jacobi Gauss sum is the Jacobi character at
minus one times `n`. See [VanDamHallgren2000]. -/
theorem jacobiGaussSum_sq (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (h1 : 1 < n) :
    jacobiGaussSum n ^ 2 = ((jacobiCharZMod n (-1) : ℤ) : ℂ) * (n : ℂ) := by
  classical
  set χ : DirichletCharacter ℂ n := jacobiDirichlet n with hχdef
  have hχq : χ⁻¹ = χ := by
    rw [hχdef]
    exact jacobiDirichlet_inv n
  have hχprim : DirichletCharacter.IsPrimitive χ := by
    rw [hχdef]
    exact jacobiDirichlet_isPrimitive n hn hsq h1
  set G : ℂ := gaussSum χ (ZMod.stdAddChar (N := n)) with hG
  have hdft : ZMod.dft χ = fun k : ZMod n => χ (-k) * G := by
    funext k
    have h := DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχprim k
    rw [hχq, ← hG] at h
    exact h
  have hcomp := congrFun (ZMod.dft_dft χ) (1 : ZMod n)
  rw [hdft, ZMod.dft_apply] at hcomp
  have hLHS : (∑ j : ZMod n, ZMod.stdAddChar (-(j * 1)) • (χ (-j) * G)) = G * G := by
    have hstep : (∑ j : ZMod n, ZMod.stdAddChar (-(j * 1)) • (χ (-j) * G))
        = (∑ j : ZMod n, ZMod.stdAddChar (-j) * χ (-j)) * G := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_eq_mul, mul_one]
      ring
    rw [hstep]
    have hre : (∑ j : ZMod n, ZMod.stdAddChar (-j) * χ (-j))
        = ∑ u : ZMod n, ZMod.stdAddChar u * χ u := by
      simpa using Equiv.sum_comp (Equiv.neg (ZMod n))
        (fun u : ZMod n => ZMod.stdAddChar u * χ u)
    rw [hre]
    have hGsum : G = ∑ u : ZMod n, ZMod.stdAddChar u * χ u := by
      rw [hG]
      simp only [gaussSum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [← hGsum]
  have hRHS : (n : ℂ) • χ (-1 : ZMod n) =
      ((jacobiCharZMod n (-1) : ℤ) : ℂ) * (n : ℂ) := by
    rw [smul_eq_mul, hχdef, jacobiDirichlet_apply]
    ring
  rw [hLHS, hRHS] at hcomp
  have hGJ : G = jacobiGaussSum n := by
    rw [hG]
    exact (jacobiGaussSum_eq_dirichlet n).symm
  rw [hGJ, ← pow_two] at hcomp
  exact hcomp

/-- For odd squarefree `n > 1`, the Jacobi Gauss sum has norm `Real.sqrt n`. See
[VanDamHallgren2000]. -/
theorem jacobiGaussSum_norm (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (h1 : 1 < n) :
    ‖jacobiGaussSum n‖ = Real.sqrt (n : ℝ) := by
  have hsqr := jacobiGaussSum_sq n hn hsq h1
  have hχnorm : ‖((jacobiCharZMod n (-1) : ℤ) : ℂ)‖ = 1 := by
    have hodd : n % 2 = 1 := by
      obtain ⟨k, hk⟩ := hn
      omega
    have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · rw [jacobiCharZMod_neg_one_eq_chi4 n hn, χ₄_nat_one_mod_four h4]; norm_num
    · rw [jacobiCharZMod_neg_one_eq_chi4 n hn, χ₄_nat_three_mod_four h4]; norm_num
  have hnorm : ‖jacobiGaussSum n‖ ^ 2 = (n : ℝ) := by
    have h := congrArg norm hsqr
    rw [norm_pow, norm_mul, hχnorm, Complex.norm_natCast, one_mul] at h
    exact h
  rw [eq_comm]
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr hnorm.symm

/-- For odd squarefree `n > 1` congruent to one modulo four, the Jacobi Gauss sum is either `√n`
or `-√n`. See [VanDamHallgren2000]. -/
theorem jacobiGaussSum_eq_or_neg_sqrt (n : ℕ) [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) (h4 : n % 4 = 1) :
    jacobiGaussSum n = (Real.sqrt (n : ℝ) : ℂ) ∨
      jacobiGaussSum n = -(Real.sqrt (n : ℝ) : ℂ) := by
  have hchi : ((jacobiCharZMod n (-1) : ℤ) : ℂ) = 1 := by
    rw [jacobiCharZMod_neg_one_eq_chi4 n hn, χ₄_nat_one_mod_four h4]
    norm_num
  have hsqr := jacobiGaussSum_sq n hn hsq h1
  rw [hchi] at hsqr
  have hsqrt_sq : ((Real.sqrt (n : ℝ) : ℂ)) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq : jacobiGaussSum n ^ 2 = ((Real.sqrt (n : ℝ) : ℂ)) ^ 2 := by
    rw [hsqr, hsqrt_sq]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

/-- For odd squarefree `n > 1` congruent to three modulo four, the Jacobi Gauss sum is either `I
* √n` or its negative. See [VanDamHallgren2000]. -/
theorem jacobiGaussSum_eq_or_neg_I_sqrt (n : ℕ) [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) (h4 : n % 4 = 3) :
    jacobiGaussSum n = Complex.I * (Real.sqrt (n : ℝ) : ℂ) ∨
      jacobiGaussSum n = -(Complex.I * (Real.sqrt (n : ℝ) : ℂ)) := by
  have hchi : ((jacobiCharZMod n (-1) : ℤ) : ℂ) = -1 := by
    rw [jacobiCharZMod_neg_one_eq_chi4 n hn, χ₄_nat_three_mod_four h4]
    norm_num
  have hsqr := jacobiGaussSum_sq n hn hsq h1
  rw [hchi] at hsqr
  have hsqrt_sq : ((Real.sqrt (n : ℝ) : ℂ)) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq : jacobiGaussSum n ^ 2 =
      (Complex.I * (Real.sqrt (n : ℝ) : ℂ)) ^ 2 := by
    rw [hsqr, mul_pow, Complex.I_sq, hsqrt_sq]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

end Qatlib.Papers.QuadChar00.MainResults
