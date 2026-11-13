/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs

/-!
# Values and intervals for binary rational quotients

This module defines `WordRat`, a signed numerator word and a denominator word with positive
binary value. The construction `quotient` forms cross products and is proved to represent
rational division by `quotient_value`; `quotient_interval` connects that value to a certified
interval with an explicit width bound. Finite representations of numerical inputs have
computational background in [KitaevShenVyalyi2002].

## Main statements

* `WordRat.toEnc`: converts word data to a rational encoding.
* `quotient_value`: identifies the exact rational quotient.
* `quotient_interval`: certifies enclosure under a positive denominator interval gap.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod (RatEnc)

/-- A signed binary numerator and denominator word together with a proof that the denominator
has positive binary value. -/
structure WordRat where
  negative : Bool
  numerator : Bits
  denominator : Bits
  positive : 0 < binaryValue denominator

/-- Converts a word rational to `RatEnc` by interpreting its sign, numerator word, and positive
denominator word. -/
def WordRat.toEnc (a : WordRat) : RatEnc where
  num := if a.negative then -(binaryValue a.numerator : ℤ) else (binaryValue a.numerator : ℤ)
  den := binaryValue a.denominator
  den_pos := a.positive

/-- The rational value represented by a word rational via its `RatEnc` conversion. -/
def WordRat.toRat (a : WordRat) : ℚ := a.toEnc.toRat

/-- Forms a word rational for division using the exclusive or of the signs and binary cross
products, assuming the divisor numerator has positive binary value. -/
def quotient (a b : WordRat) (hb : 0 < binaryValue b.numerator) : WordRat where
  negative := a.negative ^^ b.negative
  numerator := mulAcc a.numerator b.denominator b.denominator.length
  denominator := mulAcc a.denominator b.numerator b.numerator.length
  positive := by rw [mulProgram_value]; exact Nat.mul_pos a.positive hb

/-- The rational value of `quotient a b hb` equals `a.toRat / b.toRat`. -/
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

/-- If `gap` is positive and bounded by the lower endpoint of the divisor's native interval,
`nativeDiv` returns a valid interval containing the quotient value. Its width is bounded by
`2⁻ᵏ / gap` plus the numerator interval radius times `2⁻ᵏ / gap²`. -/
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
