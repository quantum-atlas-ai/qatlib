/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Reduction
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

def binomialSignedMagnitude (negative : Bool) (magnitude : ℕ) : ℤ :=
  if negative then -(magnitude : ℤ) else (magnitude : ℤ)

def binomialSignedRat (a : ℤ) (d : ℕ) : ℚ × ℕ :=
  if hd : d = 0 then (0,0) else
    let q := binomialReducedRat a.natAbs d (Nat.pos_of_ne_zero hd)
    (if a < 0 then -q.1 else q.1,q.2)

def binomialRatMulBits (a b : ℚ) : ℚ × ℕ :=
  let n := binomialBitMul a.num.natAbs.bits b.num.natAbs.bits
  let d := binomialBitMul a.den.bits b.den.bits
  let sign := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  let q := binomialSignedRat (binomialSignedMagnitude sign (binomialBitValue n.1))
    (binomialBitValue d.1)
  (q.1,n.2+d.2+1+q.2)

def binomialRatDivBits (a b : ℚ) : ℚ × ℕ :=
  let n := binomialBitMul a.num.natAbs.bits b.den.bits
  let d := binomialBitMul a.den.bits b.num.natAbs.bits
  let sign := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  let q := binomialSignedRat (binomialSignedMagnitude sign (binomialBitValue n.1))
    (binomialBitValue d.1)
  (q.1,n.2+d.2+1+q.2)

def binomialRatOpGateCap (w : ℕ) : ℕ := w*(44*w^2+2*w)+66*w^2+1

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

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

def binomialRatAddBits (a b : ℚ) : ℚ × ℕ :=
  let x := binomialBitMul a.num.natAbs.bits b.den.bits
  let y := binomialBitMul b.num.natAbs.bits a.den.bits
  let d := binomialBitMul a.den.bits b.den.bits
  let n := binomialSignedAddBits (decide (a.num < 0)) (decide (b.num < 0)) x.1 y.1
  let r := binomialSignedRat n.1 (binomialBitValue d.1)
  (r.1,x.2+y.2+d.2+n.2+r.2)

def binomialRatSubBits (a b : ℚ) : ℚ × ℕ := binomialRatAddBits a (-b)

def binomialRatAddGateCap (w : ℕ) : ℕ := w*(44*w^2+2*w)+77*w^2+22*w+1

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
