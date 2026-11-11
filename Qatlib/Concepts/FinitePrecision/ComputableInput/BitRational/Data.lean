/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Counted Boolean arithmetic data

This module defines little-endian Boolean-list arithmetic with explicit gate counters, including
addition, multiplication, comparison, subtraction, long division, and a bounded Euclidean GCD
routine. `binomialRatHeight` records the maximum of a rational number's absolute numerator and
denominator. Bit-level arithmetic supplies classical components for computation as discussed in
[KitaevShenVyalyi2002].

`BinomialDivisionResult` and `BinomialGcdResult` retain intermediate accounting data.
`binomialReduceFraction` computes a GCD and divides the numerator and denominator by its
returned bits, accumulating the three routine costs.

## Main statements

* `binomialBitValue`: interprets a Boolean list as a little-endian natural number.
* `binomialBitDivmod`: performs long division while recording quotient, remainder, gates, and
  columns.
* `binomialBitGcd`: runs the bounded GCD routine at the maximum input width.
* `binomialReduceFraction`: computes numerator and denominator quotients and their accumulated
  gate count.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- The maximum of a rational number's absolute numerator and positive denominator. -/
def binomialRatHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

/-- Interprets a Boolean list as a little-endian natural number, with the empty list
representing zero. -/
def binomialBitValue : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*binomialBitValue bs

/-- Returns the sum bit and carry bit for two Boolean input bits and a carry-in. -/
def binomialFullAdder (x y c : Bool) : Bool × Bool :=
  let p := Bool.xor x y
  (Bool.xor p c, Bool.or (Bool.and x y) (Bool.and p c))

/-- Runs a width-bounded ripple-carry addition, padding missing input bits by false and
returning the final carry as an extra bit together with a gate count. -/
def binomialBitAdd : ℕ → List Bool → List Bool → Bool → List Bool × ℕ
  | 0, _, _, c => ([c],0)
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (ys.headD false) c
    let r := binomialBitAdd k xs.tail ys.tail f.2
    (f.1::r.1,5+r.2)

/-- Conjoins every bit with a fixed Boolean mask and records one gate per input bit. -/
def binomialBitMask (b : Bool) : List Bool → List Bool × ℕ
  | [] => ([],0)
  | y::ys => let r := binomialBitMask b ys; (Bool.and b y::r.1,1+r.2)

/-- Computes a Boolean-list product by recursive shift, mask, and addition operations,
accumulating their gate counts. -/
def binomialBitMul : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([],0)
  | b::bs, ys =>
    let r := binomialBitMul bs ys
    let m := binomialBitMask b ys
    let a := binomialBitAdd (2*bs.length+ys.length+1) (false::r.1) m.1 false
    (a.1,r.2+m.2+a.2)

/-- Computes the Boolean carry used to propagate a binary comparison from lower to higher bits. -/
def binomialCompareCarry (x y c : Bool) : Bool :=
  let nx := Bool.not x
  Bool.or (Bool.and nx y) (Bool.and (Bool.or nx y) c)

/-- Propagates the comparison carry through a specified number of bit positions, padding missing
bits by false and recording five gates per position. -/
def binomialBitCompare : ℕ → List Bool → List Bool → Bool → Bool × ℕ
  | 0, _, _, c => (c,0)
  | k+1, xs, ys, c =>
    let b := binomialCompareCarry (xs.headD false) (ys.headD false) c
    let r := binomialBitCompare k xs.tail ys.tail b
    (r.1,5+r.2)

/-- Adds natural-number binary digit lists at the maximum operand width and returns the decoded
result with its gate count. -/
def binomialNatAdd (a b : ℕ) : ℕ × ℕ :=
  let r := binomialBitAdd (max a.size b.size) a.bits b.bits false
  (binomialBitValue r.1,r.2)

/-- Compares natural-number digit lists at the maximum operand width, using initial comparison
carry true and returning the decision with its gate count. -/
def binomialNatLE (a b : ℕ) : Bool × ℕ :=
  binomialBitCompare (max a.size b.size) a.bits b.bits true

/-- Computes width-bounded subtraction by adding the complemented second input with a carry,
returning output bits, final carry, and gate count. -/
def binomialBitSubtract : ℕ → List Bool → List Bool → Bool → (List Bool × Bool) × ℕ
  | 0, _, _, c => (([],c),0)
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (Bool.not (ys.headD false)) c
    let r := binomialBitSubtract k xs.tail ys.tail f.2
    ((f.1::r.1.1,r.1.2),6+r.2)

/-- Stores Boolean-list quotient and remainder together with the long-division gate and column
counts. -/
structure BinomialDivisionResult where
  quotient : List Bool
  remainder : List Bool
  gates : ℕ
  columns : ℕ
  deriving DecidableEq, Repr

/-- Runs binary long division by recursively forming a trial remainder, comparing it with the
divisor, and conditionally subtracting, while recording gates and columns. -/
def binomialBitDivmod (ds : List Bool) : List Bool → BinomialDivisionResult
  | [] => ⟨[],[],0,0⟩
  | b::bs =>
    let r := binomialBitDivmod ds bs
    let candidate := b::r.remainder
    let k := max candidate.length ds.length
    let cmp := binomialBitCompare k ds candidate true
    if cmp.1 then
      let sub := binomialBitSubtract k candidate ds true
      ⟨true::r.quotient,sub.1.1,r.gates+cmp.2+sub.2,r.columns+1⟩
    else ⟨false::r.quotient,candidate,r.gates+cmp.2,r.columns+1⟩

/-- Computes the disjunction of all input bits and records one gate per bit. -/
def binomialBitAny : List Bool → Bool × ℕ
  | [] => (false,0)
  | b::bs => let r := binomialBitAny bs; (Bool.or b r.1,1+r.2)

/-- Stores the returned GCD bits, number of divisions, and accumulated gate count. -/
structure BinomialGcdResult where
  bits : List Bool
  divisions : ℕ
  gates : ℕ
  deriving DecidableEq, Repr

/-- Runs a fuel-bounded Euclidean procedure with remainders truncated to width `w`, performing
up to two divisions per recursive step and accumulating their costs. -/
def binomialGcdRun (w : ℕ) : ℕ → List Bool → List Bool → BinomialGcdResult
  | 0, xs, _ => ⟨xs,0,0⟩
  | k+1, xs, ys =>
    let nz := binomialBitAny ys
    if nz.1 then
      let d := binomialBitDivmod ys xs
      let r := d.remainder.take w
      let nr := binomialBitAny r
      if nr.1 then
        let e := binomialBitDivmod r ys
        let t := binomialGcdRun w k r (e.remainder.take w)
        ⟨t.bits,2+t.divisions,nz.2+d.gates+nr.2+e.gates+t.gates⟩
      else ⟨ys,1,nz.2+d.gates+nr.2⟩
    else ⟨xs,0,nz.2⟩

/-- Runs the bounded Boolean-list GCD procedure with width and fuel both equal to the maximum
input length. -/
def binomialBitGcd (xs ys : List Bool) : BinomialGcdResult :=
  let w := max xs.length ys.length
  binomialGcdRun w w xs ys

/-- Defines the polynomial GCD gate cap `w * (44 * w ^ 2 + 2 * w)`. -/
def binomialGcdGateCap (w : ℕ) : ℕ := w*(44*w^2+2*w)

/-- Computes a Boolean-list GCD, divides both natural inputs by the returned bits, and returns
the decoded quotients with the accumulated GCD and division gate counts. -/
def binomialReduceFraction (a d : ℕ) : (ℕ × ℕ) × ℕ :=
  let g := binomialBitGcd a.bits d.bits
  let n := binomialBitDivmod g.bits a.bits
  let b := binomialBitDivmod g.bits d.bits
  ((binomialBitValue n.quotient,binomialBitValue b.quotient),g.gates+n.gates+b.gates)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
