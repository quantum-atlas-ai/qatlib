/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.FieldTheory.Finite.Trace
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators
open MulChar ZMod

def finiteFieldDirichlet (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp]
lemma finiteFieldDirichlet_apply (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a : F) : finiteFieldDirichlet F a = ((quadraticChar F a : ℤ) : ℂ) := rfl

lemma finiteFieldDirichlet_isQuadratic (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    IsQuadratic (finiteFieldDirichlet F) :=
  (quadraticChar_isQuadratic (F := F)).comp (Int.castRingHom ℂ)

lemma finiteFieldDirichlet_ne_one (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF2 : ringChar F ≠ 2) : finiteFieldDirichlet F ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := F) hF2
  have hunit : IsUnit a := isUnit_iff_ne_zero.mpr (by
    intro h0
    rw [h0] at ha
    norm_num at ha)
  have hval : ((quadraticChar F a : ℤ) : ℂ) = (1 : ℂ) := by
    have h1 : finiteFieldDirichlet F a = 1 := by
      rw [h]
      exact MulChar.one_apply hunit
    rwa [finiteFieldDirichlet_apply] at h1
  rw [ha] at hval
  norm_num at hval

lemma traceAddChar_ne_one (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : traceAddChar p F ≠ 1 := by
  have hchar : p = ringChar F := by
    rw [← ZMod.ringChar_zmod_n p, Algebra.ringChar_eq (ZMod p) F]
  subst hchar
  intro h
  have hzero : ∀ x : F, Algebra.trace (ZMod (ringChar F)) F x = 0 := by
    intro x
    have hx : traceAddChar (ringChar F) F x = 1 := DFunLike.congr_fun h x
    have hx' : ZMod.stdAddChar (Algebra.trace (ZMod (ringChar F)) F x) = 1 := hx
    have h0 : ZMod.stdAddChar (Algebra.trace (ZMod (ringChar F)) F x) =
        ZMod.stdAddChar (N := ringChar F) 0 := by simpa using hx'
    exact ZMod.injective_stdAddChar h0
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F (a := 1) one_ne_zero
  exact hb (by simpa using hzero b)

lemma traceAddChar_isPrimitive (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : (traceAddChar p F).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (traceAddChar_ne_one p F)

lemma gaussSum_traceAddChar_eq_finiteFieldGaussSum (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] :
    gaussSum (finiteFieldDirichlet F) (traceAddChar p F) = finiteFieldGaussSum p F := by
  simp [gaussSum, finiteFieldGaussSum, finiteFieldDirichlet_apply, finiteFieldQuadChar]

theorem finiteFieldGaussSum_sq (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2) :
    finiteFieldGaussSum p F ^ 2 =
      ((quadraticChar F (-1) : ℤ) : ℂ) * (Fintype.card F : ℂ) := by
  have h := gaussSum_sq (χ := finiteFieldDirichlet F) (finiteFieldDirichlet_ne_one F hF2)
    (finiteFieldDirichlet_isQuadratic F) (ψ := traceAddChar p F)
    (traceAddChar_isPrimitive p F)
  rw [gaussSum_traceAddChar_eq_finiteFieldGaussSum] at h
  simpa [finiteFieldDirichlet_apply] using h

theorem finiteFieldGaussSum_sq_chi4 (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2) :
    finiteFieldGaussSum p F ^ 2 = ((χ₄ (Fintype.card F) : ℤ) : ℂ) * (Fintype.card F : ℂ) := by
  rw [finiteFieldGaussSum_sq p F hF2, quadraticChar_neg_one hF2]

lemma chi4_card_eq_one_or_neg_one (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF2 : ringChar F ≠ 2) :
    χ₄ (Fintype.card F) = 1 ∨ χ₄ (Fintype.card F) = -1 := by
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF2
  have hlt : Fintype.card F % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · exact Or.inl (χ₄_nat_one_mod_four h4)
  · exact Or.inr (χ₄_nat_three_mod_four h4)

theorem finiteFieldGaussSum_norm (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2) :
    ‖finiteFieldGaussSum p F‖ = Real.sqrt (Fintype.card F) := by
  have hsqr := finiteFieldGaussSum_sq_chi4 p F hF2
  have hχnorm : ‖((χ₄ (Fintype.card F) : ℤ) : ℂ)‖ = 1 := by
    rcases chi4_card_eq_one_or_neg_one F hF2 with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hnorm : ‖finiteFieldGaussSum p F‖ ^ 2 = (Fintype.card F : ℝ) := by
    have h := congrArg norm hsqr
    rw [norm_pow, norm_mul, hχnorm, Complex.norm_natCast, one_mul] at h
    exact h
  rw [eq_comm]
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr hnorm.symm

theorem finiteFieldGaussSum_eq_or_neg_sqrt (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2)
    (hq : Fintype.card F % 4 = 1) :
    finiteFieldGaussSum p F = (Real.sqrt (Fintype.card F) : ℂ) ∨
      finiteFieldGaussSum p F = -(Real.sqrt (Fintype.card F) : ℂ) := by
  have hchi := χ₄_nat_one_mod_four hq
  have hsqr := finiteFieldGaussSum_sq_chi4 p F hF2
  rw [hchi] at hsqr
  have hsqrt_sq : ((Real.sqrt (Fintype.card F) : ℂ)) ^ 2 = (Fintype.card F : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq : finiteFieldGaussSum p F ^ 2 = ((Real.sqrt (Fintype.card F) : ℂ)) ^ 2 := by
    rw [hsqr, hsqrt_sq]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

theorem finiteFieldGaussSum_eq_or_neg_I_sqrt (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2)
    (hq : Fintype.card F % 4 = 3) :
    finiteFieldGaussSum p F = Complex.I * (Real.sqrt (Fintype.card F) : ℂ) ∨
      finiteFieldGaussSum p F = -(Complex.I * (Real.sqrt (Fintype.card F) : ℂ)) := by
  have hchi := χ₄_nat_three_mod_four hq
  have hsqr := finiteFieldGaussSum_sq_chi4 p F hF2
  rw [hchi] at hsqr
  have hsqrt_sq : ((Real.sqrt (Fintype.card F) : ℂ)) ^ 2 = (Fintype.card F : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq : finiteFieldGaussSum p F ^ 2 =
      (Complex.I * (Real.sqrt (Fintype.card F) : ℂ)) ^ 2 := by
    rw [hsqr, mul_pow, Complex.I_sq, hsqrt_sq]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

private lemma odd_prime_pow (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (p ^ r) % 2 = 1 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hpodd
  have hp2' : p % 2 = 1 := by omega
  rw [Nat.pow_mod, hp2']
  simp

private lemma pow_mod_four_of_one (p : ℕ) (hp : p % 4 = 1) (r : ℕ) :
    (p ^ r) % 4 = 1 := by
  rw [Nat.pow_mod, hp]
  simp

private lemma pow_three_shift (k c : ℕ) :
    (3 : ℕ) ^ (4 * k + c) % 4 = (3 : ℕ) ^ c % 4 := by
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod,
    show (3 : ℕ) ^ 4 % 4 = 1 by norm_num]
  simp

private lemma ringChar_ne_two_of_card (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] (hcard : Fintype.card F = p ^ r) :
    ringChar F ≠ 2 := by
  intro h2
  have heven := FiniteField.even_card_of_char_two h2
  rw [hcard, odd_prime_pow p r hp2] at heven
  omega

theorem finiteFieldGaussSum_row_one (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hcard : Fintype.card F = p ^ r) (hp4 : p % 4 = 1) (_hr : Even r) :
    finiteFieldGaussSum p F = -(Real.sqrt (p ^ r : ℝ) : ℂ) ∨
      finiteFieldGaussSum p F = (Real.sqrt (p ^ r : ℝ) : ℂ) := by
  have hF2 := ringChar_ne_two_of_card p r hp2 F hcard
  have hq : Fintype.card F % 4 = 1 := by
    rw [hcard, pow_mod_four_of_one p hp4]
  have h := finiteFieldGaussSum_eq_or_neg_sqrt p F hF2 hq
  rw [hcard] at h
  simpa [or_comm] using h

theorem finiteFieldGaussSum_row_two (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hcard : Fintype.card F = p ^ r) (hp4 : p % 4 = 1) (_hr : Odd r) :
    finiteFieldGaussSum p F = (Real.sqrt (p ^ r : ℝ) : ℂ) ∨
      finiteFieldGaussSum p F = -(Real.sqrt (p ^ r : ℝ) : ℂ) := by
  have hF2 := ringChar_ne_two_of_card p r hp2 F hcard
  have hq : Fintype.card F % 4 = 1 := by
    rw [hcard, pow_mod_four_of_one p hp4]
  have h := finiteFieldGaussSum_eq_or_neg_sqrt p F hF2 hq
  rw [hcard] at h
  simpa using h

theorem finiteFieldGaussSum_row_three (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hcard : Fintype.card F = p ^ r) (hp4 : p % 4 = 3) (hr : r % 4 = 0) :
    finiteFieldGaussSum p F = -(Real.sqrt (p ^ r : ℝ) : ℂ) ∨
      finiteFieldGaussSum p F = (Real.sqrt (p ^ r : ℝ) : ℂ) := by
  have hF2 := ringChar_ne_two_of_card p r hp2 F hcard
  have hq : Fintype.card F % 4 = 1 := by
    rw [hcard, Nat.pow_mod, hp4]
    obtain ⟨k, hk⟩ : ∃ k, r = 4 * k := ⟨r / 4, by omega⟩
    rw [hk, pow_mul, Nat.pow_mod,
      show (3 : ℕ) ^ 4 % 4 = 1 by norm_num]
    simp
  have h := finiteFieldGaussSum_eq_or_neg_sqrt p F hF2 hq
  rw [hcard] at h
  simpa [or_comm] using h

theorem finiteFieldGaussSum_row_four (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hcard : Fintype.card F = p ^ r) (hp4 : p % 4 = 3) (hr : r % 4 = 1) :
    finiteFieldGaussSum p F = Complex.I * (Real.sqrt (p ^ r : ℝ) : ℂ) ∨
      finiteFieldGaussSum p F = -(Complex.I * (Real.sqrt (p ^ r : ℝ) : ℂ)) := by
  have hF2 := ringChar_ne_two_of_card p r hp2 F hcard
  have hq : Fintype.card F % 4 = 3 := by
    rw [hcard, Nat.pow_mod, hp4]
    obtain ⟨k, hk⟩ : ∃ k, r = 4 * k + 1 := ⟨r / 4, by omega⟩
    rw [hk, pow_three_shift, show (3 : ℕ) ^ 1 = 3 by norm_num]
  have h := finiteFieldGaussSum_eq_or_neg_I_sqrt p F hF2 hq
  rw [hcard] at h
  simpa using h

theorem finiteFieldGaussSum_row_five (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hcard : Fintype.card F = p ^ r) (hp4 : p % 4 = 3) (hr : r % 4 = 2) :
    finiteFieldGaussSum p F = (Real.sqrt (p ^ r : ℝ) : ℂ) ∨
      finiteFieldGaussSum p F = -(Real.sqrt (p ^ r : ℝ) : ℂ) := by
  have hF2 := ringChar_ne_two_of_card p r hp2 F hcard
  have hq : Fintype.card F % 4 = 1 := by
    rw [hcard, Nat.pow_mod, hp4]
    obtain ⟨k, hk⟩ : ∃ k, r = 4 * k + 2 := ⟨r / 4, by omega⟩
    rw [hk, pow_three_shift, show (3 : ℕ) ^ 2 = 9 by norm_num]
  have h := finiteFieldGaussSum_eq_or_neg_sqrt p F hF2 hq
  rw [hcard] at h
  simpa using h

theorem finiteFieldGaussSum_row_six (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hcard : Fintype.card F = p ^ r) (hp4 : p % 4 = 3) (hr : r % 4 = 3) :
    finiteFieldGaussSum p F = -(Complex.I * (Real.sqrt (p ^ r : ℝ) : ℂ)) ∨
      finiteFieldGaussSum p F = Complex.I * (Real.sqrt (p ^ r : ℝ) : ℂ) := by
  have hF2 := ringChar_ne_two_of_card p r hp2 F hcard
  have hq : Fintype.card F % 4 = 3 := by
    rw [hcard, Nat.pow_mod, hp4]
    obtain ⟨k, hk⟩ : ∃ k, r = 4 * k + 3 := ⟨r / 4, by omega⟩
    rw [hk, pow_three_shift, show (3 : ℕ) ^ 3 = 27 by norm_num]
  have h := finiteFieldGaussSum_eq_or_neg_I_sqrt p F hF2 hq
  rw [hcard] at h
  simpa [or_comm] using h

end Qatlib.Papers.QuadChar00.MainResults
