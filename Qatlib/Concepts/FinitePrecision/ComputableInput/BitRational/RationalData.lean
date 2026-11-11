/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Reduction

/-!
# Counted signed rational arithmetic

This module defines signed magnitude arithmetic and rational addition, subtraction,
multiplication, and division using Boolean-list computations. Each operation returns its value
together with a gate count; `binomialRatOpGateCap` and `binomialRatAddGateCap` supply polynomial
bounds used in later correctness results.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `binomialSignedAddBits`: combines signed bit magnitudes.
* `binomialRatMulBits` and `binomialRatDivBits`: counted rational product and quotient.
* `binomialRatAddBits`: counted rational addition by cross multiplication.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- Interprets a natural magnitude as a signed integer, with `true` selecting the negative sign. -/
def binomialSignedMagnitude (negative : Bool) (magnitude : ℕ) : ℤ :=
  if negative then -(magnitude : ℤ) else (magnitude : ℤ)

/-- Reduces a signed integer numerator over a natural denominator and returns the rational with
its reduction gate count, returning `(0, 0)` for a zero denominator. -/
def binomialSignedRat (a : ℤ) (d : ℕ) : ℚ × ℕ :=
  if hd : d = 0 then (0,0) else
    let q := binomialReducedRat a.natAbs d (Nat.pos_of_ne_zero hd)
    (if a < 0 then -q.1 else q.1,q.2)

/-- Computes a rational product by bitwise numerator and denominator multiplication and signed
reduction, accumulating gate costs. -/
def binomialRatMulBits (a b : ℚ) : ℚ × ℕ :=
  let n := binomialBitMul a.num.natAbs.bits b.num.natAbs.bits
  let d := binomialBitMul a.den.bits b.den.bits
  let sign := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  let q := binomialSignedRat (binomialSignedMagnitude sign (binomialBitValue n.1))
    (binomialBitValue d.1)
  (q.1,n.2+d.2+1+q.2)

/-- Computes a rational quotient by bitwise cross multiplication and signed reduction,
accumulating gate costs. -/
def binomialRatDivBits (a b : ℚ) : ℚ × ℕ :=
  let n := binomialBitMul a.num.natAbs.bits b.den.bits
  let d := binomialBitMul a.den.bits b.num.natAbs.bits
  let sign := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  let q := binomialSignedRat (binomialSignedMagnitude sign (binomialBitValue n.1))
    (binomialBitValue d.1)
  (q.1,n.2+d.2+1+q.2)

/-- The polynomial gate cap `w * (44 * w ^ 2 + 2 * w) + 66 * w ^ 2 + 1` for rational
multiplication and division. -/
def binomialRatOpGateCap (w : ℕ) : ℕ := w*(44*w^2+2*w)+66*w^2+1

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- Combines two signed bit-list magnitudes by addition or magnitude comparison and subtraction,
returning an integer and gate count. -/
def binomialSignedAddBits (s t : Bool) (xs ys : List Bool) : ℤ × ℕ :=
  let k := max xs.length ys.length
  if Bool.xor s t then
    let cmp := binomialBitCompare k xs ys true
    if cmp.1 then
      let sub := binomialBitSubtract k ys xs true
      (binomialSignedMagnitude t (binomialBitValue sub.1.1),1+cmp.2+sub.2)
    else
      let sub := binomialBitSubtract k xs ys true
      (binomialSignedMagnitude s (binomialBitValue sub.1.1),1+cmp.2+sub.2)
  else
    let add := binomialBitAdd k xs ys false
    (binomialSignedMagnitude s (binomialBitValue add.1),1+add.2)

/-- Computes a rational sum by cross multiplication, signed magnitude addition, and reduction,
accumulating the gate costs. -/
def binomialRatAddBits (a b : ℚ) : ℚ × ℕ :=
  let x := binomialBitMul a.num.natAbs.bits b.den.bits
  let y := binomialBitMul b.num.natAbs.bits a.den.bits
  let d := binomialBitMul a.den.bits b.den.bits
  let n := binomialSignedAddBits (decide (a.num < 0)) (decide (b.num < 0)) x.1 y.1
  let r := binomialSignedRat n.1 (binomialBitValue d.1)
  (r.1,x.2+y.2+d.2+n.2+r.2)

/-- Computes counted rational subtraction by adding the negation of the second operand. -/
def binomialRatSubBits (a b : ℚ) : ℚ × ℕ := binomialRatAddBits a (-b)

/-- The polynomial gate cap `w * (44 * w ^ 2 + 2 * w) + 77 * w ^ 2 + 22 * w + 1` for rational
addition. -/
def binomialRatAddGateCap (w : ℕ) : ℕ := w*(44*w^2+2*w)+77*w^2+22*w+1

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
