/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.FieldTheory.Finite.Trace

/-!
# Quadratic Gauss sums over finite fields

The complex quadratic character `finiteFieldDirichlet` and the trace additive character express
`finiteFieldGaussSum` as a standard Gauss sum. The module proves square and norm identities and
lists congruence cases that determine the sum up to sign. See [VanDamHallgren2000].

## Main statements

* `finiteFieldGaussSum_sq`: In characteristic other than two, the square of the finite field
  Gauss sum is the field cardinality times its quadratic character at minus one.
* `finiteFieldGaussSum_norm`: In characteristic other than two, the finite field Gauss sum has
  norm equal to the square root of the field cardinality.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators
open MulChar ZMod

/-- The complex valued multiplicative character obtained by casting the quadratic character of
`F`. -/
def finiteFieldDirichlet (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

/-- Evaluating `finiteFieldDirichlet` gives the integer quadratic character cast to `ℂ`. -/
@[simp]
lemma finiteFieldDirichlet_apply (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a : F) : finiteFieldDirichlet F a = ((quadraticChar F a : ℤ) : ℂ) := rfl

/-- The complex valued character `finiteFieldDirichlet F` is quadratic. -/
lemma finiteFieldDirichlet_isQuadratic (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    IsQuadratic (finiteFieldDirichlet F) :=
  (quadraticChar_isQuadratic (F := F)).comp (Int.castRingHom ℂ)

/-- The quadratic character of a finite field of characteristic other than two is nontrivial
after casting to `ℂ`. -/
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

/-- The trace additive character of a finite extension of `ZMod p` is nontrivial. -/
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

/-- The trace additive character of a finite field over `ZMod p` is primitive. -/
lemma traceAddChar_isPrimitive (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : (traceAddChar p F).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (traceAddChar_ne_one p F)

/-- The Gauss sum of the complex quadratic character and trace additive character equals
`finiteFieldGaussSum p F`. -/
lemma gaussSum_traceAddChar_eq_finiteFieldGaussSum (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] :
    gaussSum (finiteFieldDirichlet F) (traceAddChar p F) = finiteFieldGaussSum p F := by
  simp [gaussSum, finiteFieldGaussSum, finiteFieldDirichlet_apply, finiteFieldQuadChar]

/-- In characteristic other than two, the square of the finite field Gauss sum is the field
cardinality times its quadratic character at minus one. See [VanDamHallgren2000]. -/
theorem finiteFieldGaussSum_sq (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2) :
    finiteFieldGaussSum p F ^ 2 =
      ((quadraticChar F (-1) : ℤ) : ℂ) * (Fintype.card F : ℂ) := by
  have h := gaussSum_sq (χ := finiteFieldDirichlet F) (finiteFieldDirichlet_ne_one F hF2)
    (finiteFieldDirichlet_isQuadratic F) (ψ := traceAddChar p F)
    (traceAddChar_isPrimitive p F)
  rw [gaussSum_traceAddChar_eq_finiteFieldGaussSum] at h
  simpa [finiteFieldDirichlet_apply] using h

/-- In characteristic other than two, the square of the finite field Gauss sum equals `χ₄` of
the field cardinality times that cardinality. -/
theorem finiteFieldGaussSum_sq_chi4 (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] (hF2 : ringChar F ≠ 2) :
    finiteFieldGaussSum p F ^ 2 = ((χ₄ (Fintype.card F) : ℤ) : ℂ) * (Fintype.card F : ℂ) := by
  rw [finiteFieldGaussSum_sq p F hF2, quadraticChar_neg_one hF2]

/-- For a finite field of characteristic other than two, `χ₄` of its cardinality is either one
or minus one. -/
lemma chi4_card_eq_one_or_neg_one (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF2 : ringChar F ≠ 2) :
    χ₄ (Fintype.card F) = 1 ∨ χ₄ (Fintype.card F) = -1 := by
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF2
  have hlt : Fintype.card F % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · exact Or.inl (χ₄_nat_one_mod_four h4)
  · exact Or.inr (χ₄_nat_three_mod_four h4)

/-- In characteristic other than two, the finite field Gauss sum has norm equal to the square
root of the field cardinality. See [VanDamHallgren2000]. -/
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

/-- If the field cardinality is one modulo four and its characteristic is not two, the Gauss sum
equals the positive or negative square root of that cardinality. See [VanDamHallgren2000]. -/
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

/-- If the field cardinality is three modulo four and its characteristic is not two, the Gauss
sum equals `I` times the square root of that cardinality, up to sign. See
[VanDamHallgren2000]. -/
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

/-- Every natural power of a prime other than two is odd. -/
private lemma odd_prime_pow (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (p ^ r) % 2 = 1 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hpodd
  have hp2' : p % 2 = 1 := by omega
  rw [Nat.pow_mod, hp2']
  simp

/-- Every power of a natural number congruent to one modulo four is congruent to one modulo
four. -/
private lemma pow_mod_four_of_one (p : ℕ) (hp : p % 4 = 1) (r : ℕ) :
    (p ^ r) % 4 = 1 := by
  rw [Nat.pow_mod, hp]
  simp

/-- Adding a multiple of four to an exponent of three leaves its residue modulo four unchanged. -/
private lemma pow_three_shift (k c : ℕ) :
    (3 : ℕ) ^ (4 * k + c) % 4 = (3 : ℕ) ^ c % 4 := by
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod,
    show (3 : ℕ) ^ 4 % 4 = 1 by norm_num]
  simp

/-- A finite field of cardinality `p ^ r`, with `p` an odd prime, has characteristic other than
two. -/
private lemma ringChar_ne_two_of_card (p r : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (F : Type*) [Field F] [Fintype F] (hcard : Fintype.card F = p ^ r) :
    ringChar F ≠ 2 := by
  intro h2
  have heven := FiniteField.even_card_of_char_two h2
  rw [hcard, odd_prime_pow p r hp2] at heven
  omega

/-- For `p ≡ 1` modulo four and even `r`, the Gauss sum over a field of cardinality `p ^ r`
equals `√(p ^ r)` up to sign. See [VanDamHallgren2000]. -/
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

/-- For `p ≡ 1` modulo four and odd `r`, the Gauss sum over a field of cardinality `p ^ r`
equals `√(p ^ r)` up to sign. See [VanDamHallgren2000]. -/
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

/-- For `p ≡ 3` modulo four and `r ≡ 0` modulo four, the Gauss sum over a field of cardinality
`p ^ r` equals `√(p ^ r)` up to sign. See [VanDamHallgren2000]. -/
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

/-- For `p ≡ 3` modulo four and `r ≡ 1` modulo four, the Gauss sum equals `I * √(p ^ r)` up to
sign. See [VanDamHallgren2000]. -/
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

/-- For `p ≡ 3` modulo four and `r ≡ 2` modulo four, the Gauss sum equals `√(p ^ r)` up to sign.
See [VanDamHallgren2000]. -/
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

/-- For `p ≡ 3` modulo four and `r ≡ 3` modulo four, the Gauss sum equals `I * √(p ^ r)` up to
sign. See [VanDamHallgren2000]. -/
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
