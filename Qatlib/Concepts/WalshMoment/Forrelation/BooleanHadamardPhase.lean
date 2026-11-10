/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardCoordinates
import Qatlib.Concepts.WalshMoment.Forrelation.FiniteAbelian
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.WalshMoment.Forrelation

open scoped ComplexConjugate Classical

@[simp] theorem zmod2_stdAddChar_one :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 1 <;> ring

@[simp] theorem zmod2_stdAddChar_boolZModEquiv (b : Bool) :
    ZMod.stdAddChar (boolZModEquiv b) = if b then (-1 : ℂ) else 1 := by
  cases b <;> simp

private theorem stdAddChar_sum_eq_prod {ι : Type*} [Fintype ι]
    (f : ι → ZMod 2) :
    ZMod.stdAddChar (∑ i, f i) = ∏ i, ZMod.stdAddChar (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ZMod.stdAddChar.map_add_eq_mul,
        Finset.prod_insert ha, ih]

theorem booleanCharacter_regBooleanEquiv_sign {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z) =
      ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  rw [booleanCharacter_regBooleanEquiv_apply, stdAddChar_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact zmod2_stdAddChar_boolZModEquiv (y i && z i)

theorem conj_booleanCharacter_regBooleanEquiv_sign {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    conj (booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z)) =
      ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  rw [booleanCharacter_regBooleanEquiv_sign, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases hy : y i <;> cases hz : z i <;> simp [hy, hz]

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

theorem booleanFourierMatrix_regBooleanEquiv_apply {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    fourierMatrix (BooleanVec n)
        (booleanCharacter (regBooleanEquiv n y)) (regBooleanEquiv n z) =
      ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
        ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  rw [fourierMatrix, fourierScale_booleanVec,
    conj_booleanCharacter_regBooleanEquiv_sign]

end Qatlib.Concepts.WalshMoment.Forrelation
