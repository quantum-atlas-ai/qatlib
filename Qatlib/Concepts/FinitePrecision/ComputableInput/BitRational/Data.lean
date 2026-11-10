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

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

def binomialRatHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

def binomialBitValue : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*binomialBitValue bs

def binomialFullAdder (x y c : Bool) : Bool × Bool :=
  let p := Bool.xor x y
  (Bool.xor p c, Bool.or (Bool.and x y) (Bool.and p c))

def binomialBitAdd : ℕ → List Bool → List Bool → Bool → List Bool × ℕ
  | 0, _, _, c => ([c],0)
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (ys.headD false) c
    let r := binomialBitAdd k xs.tail ys.tail f.2
    (f.1::r.1,5+r.2)

def binomialBitMask (b : Bool) : List Bool → List Bool × ℕ
  | [] => ([],0)
  | y::ys => let r := binomialBitMask b ys; (Bool.and b y::r.1,1+r.2)

def binomialBitMul : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([],0)
  | b::bs, ys =>
    let r := binomialBitMul bs ys
    let m := binomialBitMask b ys
    let a := binomialBitAdd (2*bs.length+ys.length+1) (false::r.1) m.1 false
    (a.1,r.2+m.2+a.2)

def binomialCompareCarry (x y c : Bool) : Bool :=
  let nx := Bool.not x
  Bool.or (Bool.and nx y) (Bool.and (Bool.or nx y) c)

def binomialBitCompare : ℕ → List Bool → List Bool → Bool → Bool × ℕ
  | 0, _, _, c => (c,0)
  | k+1, xs, ys, c =>
    let b := binomialCompareCarry (xs.headD false) (ys.headD false) c
    let r := binomialBitCompare k xs.tail ys.tail b
    (r.1,5+r.2)

def binomialNatAdd (a b : ℕ) : ℕ × ℕ :=
  let r := binomialBitAdd (max a.size b.size) a.bits b.bits false
  (binomialBitValue r.1,r.2)

def binomialNatLE (a b : ℕ) : Bool × ℕ :=
  binomialBitCompare (max a.size b.size) a.bits b.bits true

def binomialBitSubtract : ℕ → List Bool → List Bool → Bool → (List Bool × Bool) × ℕ
  | 0, _, _, c => (([],c),0)
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (Bool.not (ys.headD false)) c
    let r := binomialBitSubtract k xs.tail ys.tail f.2
    ((f.1::r.1.1,r.1.2),6+r.2)

structure BinomialDivisionResult where
  quotient : List Bool
  remainder : List Bool
  gates : ℕ
  columns : ℕ
  deriving DecidableEq, Repr

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

def binomialBitAny : List Bool → Bool × ℕ
  | [] => (false,0)
  | b::bs => let r := binomialBitAny bs; (Bool.or b r.1,1+r.2)

structure BinomialGcdResult where
  bits : List Bool
  divisions : ℕ
  gates : ℕ
  deriving DecidableEq, Repr

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

def binomialBitGcd (xs ys : List Bool) : BinomialGcdResult :=
  let w := max xs.length ys.length
  binomialGcdRun w w xs ys

def binomialGcdGateCap (w : ℕ) : ℕ := w*(44*w^2+2*w)

def binomialReduceFraction (a d : ℕ) : (ℕ × ℕ) × ℕ :=
  let g := binomialBitGcd a.bits d.bits
  let n := binomialBitDivmod g.bits a.bits
  let b := binomialBitDivmod g.bits d.bits
  ((binomialBitValue n.quotient,binomialBitValue b.quotient),g.gates+n.gates+b.gates)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
