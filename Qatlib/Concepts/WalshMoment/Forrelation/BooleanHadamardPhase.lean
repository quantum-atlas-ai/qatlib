/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardCoordinates
import Qatlib.Concepts.WalshMoment.Forrelation.FiniteAbelian

/-!
# Boolean character phases and Fourier entries

This module evaluates the standard additive character of `ZMod 2` as a sign and derives the
corresponding product formula for Boolean characters. It also computes the Fourier normalization
on `BooleanVec n`, yielding Fourier matrix entries as a product of Boolean signs times `(1 /
sqrt 2)^n`.

These formulas give the coordinate expression underlying the Boolean Hadamard transform; see
[NielsenChuang2010] for the quantum Fourier and Hadamard background.

## Key declarations

* `zmod2_stdAddChar_one` and `zmod2_stdAddChar_boolZModEquiv` evaluate the scalar phases.
* `booleanCharacter_regBooleanEquiv_sign` and its conjugate form give the sign product.
* `fourierScale_booleanVec` and `booleanFourierMatrix_regBooleanEquiv_apply` compute the
  normalization and matrix entries.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.WalshMoment.Forrelation

open scoped ComplexConjugate Classical

/-- The standard additive character of `ZMod 2` takes the value `-1` at one. -/
@[simp] theorem zmod2_stdAddChar_one :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 1 <;> ring

/-- The standard additive character of a converted Boolean bit is `-1` for `true` and `1` for
`false`. -/
@[simp] theorem zmod2_stdAddChar_boolZModEquiv (b : Bool) :
    ZMod.stdAddChar (boolZModEquiv b) = if b then (-1 : ℂ) else 1 := by
  cases b <;> simp

/-- The standard additive character sends a finite sum in `ZMod 2` to the product of the
individual character values. -/
private theorem stdAddChar_sum_eq_prod {ι : Type*} [Fintype ι]
    (f : ι → ZMod 2) :
    ZMod.stdAddChar (∑ i, f i) = ∏ i, ZMod.stdAddChar (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ZMod.stdAddChar.map_add_eq_mul,
        Finset.prod_insert ha, ih]

/-- The character value for two converted registers is the product of `-1` at coordinates where
both bits are true and `1` elsewhere. -/
theorem booleanCharacter_regBooleanEquiv_sign {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z) =
      ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  rw [booleanCharacter_regBooleanEquiv_apply, stdAddChar_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact zmod2_stdAddChar_boolZModEquiv (y i && z i)

/-- The conjugate character value for two converted registers equals the same product of real
signs as the character value itself. -/
theorem conj_booleanCharacter_regBooleanEquiv_sign {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    conj (booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z)) =
      ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  rw [booleanCharacter_regBooleanEquiv_sign, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases hy : y i <;> cases hz : z i <;> simp [hy, hz]

/-- The Fourier normalization for Boolean vectors of length `n` equals `(1 / sqrt 2)^n`, viewed
in the complex numbers. -/
theorem fourierScale_booleanVec (n : ℕ) :
    fourierScale (BooleanVec n) = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  have hsqrt : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  have hcard : Fintype.card (BooleanVec n) = 2 ^ n := by
    simp [BooleanVec]
  simp only [fourierScale, hcard]
  rw [show ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n by norm_num, hsqrt]
  push_cast
  rw [inv_pow]

/-- A Boolean Fourier matrix entry in register coordinates is `(1 / sqrt 2)^n` times the product
of the coordinatewise conjunction signs. -/
theorem booleanFourierMatrix_regBooleanEquiv_apply {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    fourierMatrix (BooleanVec n)
        (booleanCharacter (regBooleanEquiv n y)) (regBooleanEquiv n z) =
      ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
        ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  rw [fourierMatrix, fourierScale_booleanVec,
    conj_booleanCharacter_regBooleanEquiv_sign]

end Qatlib.Concepts.WalshMoment.Forrelation
