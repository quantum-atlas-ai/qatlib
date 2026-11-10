/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Qatlib.Papers.QuadChar00.MainResults.Lemma4JacobiSum
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators
open MulChar ZMod

def legendreDirichlet (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

@[simp]
lemma legendreDirichlet_apply (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    legendreDirichlet p a = ((quadCharZMod p a : ℤ) : ℂ) := rfl

lemma legendreDirichlet_isQuadratic (p : ℕ) [Fact p.Prime] :
    IsQuadratic (legendreDirichlet p) :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

lemma legendreDirichlet_ne_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreDirichlet p ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by
    rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hunit : IsUnit a := isUnit_iff_ne_zero.mpr (by
    intro h0
    rw [h0] at ha
    norm_num at ha)
  have hval : ((quadCharZMod p a : ℤ) : ℂ) = (1 : ℂ) := by
    have h1 : legendreDirichlet p a = 1 := by
      rw [h]
      exact MulChar.one_apply hunit
    rwa [legendreDirichlet_apply] at h1
  rw [quadCharZMod, ha] at hval
  norm_num at hval

lemma stdAddChar_star (n : ℕ) [NeZero n] (x : ZMod n) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
  have hneg : ((ZMod.toCircle (-x) : Circle) : ℂ) = (((ZMod.toCircle x)⁻¹ : Circle) : ℂ) := by
    rw [AddChar.map_neg_eq_inv]
  rw [hneg, Circle.coe_inv_eq_conj, Complex.star_def]

theorem jacobiGaussSum_star (n : ℕ) [NeZero n] :
    star (jacobiGaussSum n)
      = ((jacobiCharZMod n (-1) : ℤ) : ℂ) * jacobiGaussSum n := by
  classical
  rw [jacobiGaussSum]
  have hsum : star (∑ x : ZMod n,
        ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar x)
      = ∑ x : ZMod n,
        ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar (-x) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [star_mul, stdAddChar_star, star_intCast]
    ring
  rw [hsum]
  have hreindex : (∑ x : ZMod n,
        ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar (-x))
      = ∑ x : ZMod n,
        ((jacobiCharZMod n (-x) : ℤ) : ℂ) * ZMod.stdAddChar x := by
    have h := Equiv.sum_comp (Equiv.neg (ZMod n))
      (fun x : ZMod n => ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar (-x))
    simpa using h.symm
  rw [hreindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hmul : jacobiCharZMod n (-x) = jacobiCharZMod n (-1) * jacobiCharZMod n x := by
    rw [show (-x : ZMod n) = (-1) * x by ring]
    exact jacobiCharZMod_mul n (-1) x
  rw [hmul]
  push_cast
  ring

theorem legendreGaussSum_sq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreGaussSum p ^ 2 = ((quadCharZMod p (-1) : ℤ) : ℂ) * (p : ℂ) := by
  have hψ : AddChar.IsPrimitive (ZMod.stdAddChar (N := p)) := ZMod.isPrimitive_stdAddChar p
  have h := gaussSum_sq (χ := legendreDirichlet p) (legendreDirichlet_ne_one p hp2)
    (legendreDirichlet_isQuadratic p) (ψ := ZMod.stdAddChar (N := p)) hψ
  have h' : legendreGaussSum p ^ 2 =
      legendreDirichlet p (-1) * (Fintype.card (ZMod p) : ℂ) := by
    simpa only [gaussSum, legendreGaussSum, legendreDirichlet_apply] using h
  rw [h', ZMod.card, legendreDirichlet_apply]

theorem legendreGaussSum_norm (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ‖legendreGaussSum p‖ = Real.sqrt p := by
  have hsqr := legendreGaussSum_sq p hp2
  have hχneg : ‖((quadCharZMod p (-1) : ℤ) : ℂ)‖ = 1 := by
    have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    rcases quadraticChar_dichotomy hne with h | h
    · rw [quadCharZMod, h]; norm_num
    · rw [quadCharZMod, h]; norm_num
  have hnorm : ‖legendreGaussSum p‖ ^ 2 = (p : ℝ) := by
    have h := congrArg norm hsqr
    rw [norm_pow, norm_mul, hχneg, Complex.norm_natCast, one_mul] at h
    exact h
  rw [eq_comm]
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr hnorm.symm

lemma quadCharZMod_neg_one_of_one_mod_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp4 : p % 4 = 1) : quadCharZMod p (-1) = 1 := by
  rw [quadCharZMod]
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [quadraticChar_neg_one (F := ZMod p) hF, ZMod.card]
  exact χ₄_nat_one_mod_four hp4

lemma quadCharZMod_neg_one_of_three_mod_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp4 : p % 4 = 3) : quadCharZMod p (-1) = -1 := by
  rw [quadCharZMod]
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [quadraticChar_neg_one (F := ZMod p) hF, ZMod.card]
  exact χ₄_nat_three_mod_four hp4

theorem legendreGaussSum_eq_or_neg_sqrt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp4 : p % 4 = 1) :
    legendreGaussSum p = (Real.sqrt p : ℂ) ∨
      legendreGaussSum p = -(Real.sqrt p : ℂ) := by
  have hchi := quadCharZMod_neg_one_of_one_mod_four p hp2 hp4
  have hsqr := legendreGaussSum_sq p hp2
  rw [hchi] at hsqr
  have hsqrt_sq : ((Real.sqrt p : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq : legendreGaussSum p ^ 2 = ((Real.sqrt p : ℂ)) ^ 2 := by
    rw [hsqr, hsqrt_sq]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

theorem legendreGaussSum_eq_or_neg_I_sqrt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp4 : p % 4 = 3) :
    legendreGaussSum p = Complex.I * (Real.sqrt p : ℂ) ∨
      legendreGaussSum p = -(Complex.I * (Real.sqrt p : ℂ)) := by
  have hchi := quadCharZMod_neg_one_of_three_mod_four p hp2 hp4
  have hsqr := legendreGaussSum_sq p hp2
  rw [hchi] at hsqr
  have hsqrt_sq : ((Real.sqrt p : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq : legendreGaussSum p ^ 2 = (Complex.I * (Real.sqrt p : ℂ)) ^ 2 := by
    rw [hsqr, mul_pow, Complex.I_sq, hsqrt_sq]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

end Qatlib.Papers.QuadChar00.MainResults
