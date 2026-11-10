/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod (RatEnc)

structure WordRat where
  negative : Bool
  numerator : Bits
  denominator : Bits
  positive : 0 < binaryValue denominator

def WordRat.toEnc (a : WordRat) : RatEnc where
  num := if a.negative then -(binaryValue a.numerator : ℤ) else (binaryValue a.numerator : ℤ)
  den := binaryValue a.denominator
  den_pos := a.positive

def WordRat.toRat (a : WordRat) : ℚ := a.toEnc.toRat

def quotient (a b : WordRat) (hb : 0 < binaryValue b.numerator) : WordRat where
  negative := a.negative ^^ b.negative
  numerator := mulAcc a.numerator b.denominator b.denominator.length
  denominator := mulAcc a.denominator b.numerator b.numerator.length
  positive := by rw [mulProgram_value]; exact Nat.mul_pos a.positive hb

theorem quotient_value (a b : WordRat) (hb : 0 < binaryValue b.numerator) :
    (quotient a b hb).toRat = a.toRat / b.toRat := by
  have hA : (binaryValue a.denominator : ℚ) ≠ 0 := by exact_mod_cast a.positive.ne'
  have hB : (binaryValue b.denominator : ℚ) ≠ 0 := by exact_mod_cast b.positive.ne'
  have hN : (binaryValue b.numerator : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  cases ha : a.negative <;> cases hb' : b.negative
  all_goals
    simp only [WordRat.toRat,WordRat.toEnc,quotient,RatEnc.toRat,ha,hb',
      Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      if_false,if_true,mulProgram_value,Int.cast_neg,Int.cast_natCast,Nat.cast_mul]
    field_simp [hA,hB,hN]
    simp only [Int.cast_mul,Int.cast_natCast]

theorem quotient_interval (a b : WordRat) (hb : 0 < binaryValue b.numerator)
    (gap : ℚ) (k : ℕ) (hg : 0 < gap) (hgap : gap ≤ (nativeInterval b.toEnc k).lo) :
    ∃ c, nativeDiv a.toEnc b.toEnc gap k = some c ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.Valid c ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.Contains c ((quotient a b hb).toRat : ℝ) ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.width c ≤ 1/(2 : ℚ)^k/gap +
        Qatlib.Foundations.IntervalArith.IntervalOps.radius (nativeInterval a.toEnc k)*
          (1/(2 : ℚ)^k)/gap^2 := by
  obtain ⟨c,hc,hv,_,hh,_⟩ := nativeDiv_certified a.toEnc b.toEnc gap k hg hgap
  refine ⟨c,hc,hv,?_,nativeDiv_rounding_account a.toEnc b.toEnc gap k hg hgap c hc⟩
  rw [quotient_value]
  simpa only [WordRat.toRat,Rat.cast_div] using! hh

end Qatlib.Concepts.QueryComplexity.DegreeMethod
