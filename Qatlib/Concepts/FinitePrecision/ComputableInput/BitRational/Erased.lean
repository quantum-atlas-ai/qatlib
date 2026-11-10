/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Addition
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

def add : ℕ → List Bool → List Bool → Bool → List Bool
  | 0, _, _, c => [c]
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (ys.headD false) c
    f.1 :: add k xs.tail ys.tail f.2

def mask (b : Bool) : List Bool → List Bool
  | [] => []
  | y::ys => Bool.and b y :: mask b ys

def mul : List Bool → List Bool → List Bool
  | [], _ => []
  | b::bs, ys => add (2*bs.length+ys.length+1) (false::mul bs ys) (mask b ys) false

def compare : ℕ → List Bool → List Bool → Bool → Bool
  | 0, _, _, c => c
  | k+1, xs, ys, c => compare k xs.tail ys.tail
      (binomialCompareCarry (xs.headD false) (ys.headD false) c)

def subtract : ℕ → List Bool → List Bool → Bool → List Bool × Bool
  | 0, _, _, c => ([],c)
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (!(ys.headD false)) c
    let r := subtract k xs.tail ys.tail f.2
    (f.1::r.1,r.2)

def any : List Bool → Bool
  | [] => false
  | b::bs => Bool.or b (any bs)

def divmod (ds : List Bool) : List Bool → List Bool × List Bool
  | [] => ([],[])
  | b::bs =>
    let r := divmod ds bs
    let candidate := b::r.2
    let k := max candidate.length ds.length
    if compare k ds candidate true then
      (true::r.1,(subtract k candidate ds true).1)
    else (false::r.1,candidate)

def gcdRun (w : ℕ) : ℕ → List Bool → List Bool → List Bool
  | 0, xs, _ => xs
  | k+1, xs, ys =>
    if any ys then
      let r := (divmod ys xs).2.take w
      if any r then gcdRun w k r ((divmod r ys).2.take w) else ys
    else xs

def gcd (xs ys : List Bool) : List Bool :=
    gcdRun (max xs.length ys.length) (max xs.length ys.length) xs ys

def reduce (a d : ℕ) : ℕ × ℕ :=
  let g := gcd a.bits d.bits
  (binomialBitValue (divmod g a.bits).1,binomialBitValue (divmod g d.bits).1)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

theorem add_eq (k : ℕ) (xs ys : List Bool) (c : Bool) :
    add k xs ys c = (binomialBitAdd k xs ys c).1 := by
  induction k generalizing xs ys c with
  | zero => rfl
  | succ k ih => simp only [add,binomialBitAdd,ih]

theorem mask_eq (b : Bool) (xs : List Bool) : mask b xs = (binomialBitMask b xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mask,binomialBitMask,ih]

theorem mul_eq (xs ys : List Bool) : mul xs ys = (binomialBitMul xs ys).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mul,binomialBitMul,ih,mask_eq,add_eq]

theorem compare_eq (k : ℕ) (xs ys : List Bool) (c : Bool) :
    compare k xs ys c = (binomialBitCompare k xs ys c).1 := by
  induction k generalizing xs ys c with
  | zero => rfl
  | succ k ih => simp only [compare,binomialBitCompare,ih]

theorem subtract_eq (k : ℕ) (xs ys : List Bool) (c : Bool) :
    subtract k xs ys c = (binomialBitSubtract k xs ys c).1 := by
  induction k generalizing xs ys c with
  | zero => rfl
  | succ k ih => simp only [subtract,binomialBitSubtract,ih]

theorem any_eq (xs : List Bool) : any xs = (binomialBitAny xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [any,binomialBitAny,ih]

theorem divmod_eq (xs ys : List Bool) : divmod xs ys =
    ((binomialBitDivmod xs ys).quotient,(binomialBitDivmod xs ys).remainder) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [divmod,binomialBitDivmod,ih,compare_eq,subtract_eq]
    split <;> rfl

theorem gcdRun_eq (w k : ℕ) (xs ys : List Bool) :
    gcdRun w k xs ys = (binomialGcdRun w k xs ys).bits := by
  induction k generalizing xs ys with
  | zero => rfl
  | succ k ih =>
    simp only [gcdRun,binomialGcdRun,any_eq,divmod_eq]
    split
    · split <;> simp only [ih]
    · rfl

theorem gcd_eq (xs ys : List Bool) : gcd xs ys = (binomialBitGcd xs ys).bits :=
  gcdRun_eq _ _ _ _

theorem reduce_eq (a d : ℕ) : reduce a d = (binomialReduceFraction a d).1 := by
  simp only [reduce,binomialReduceFraction,gcd_eq,divmod_eq]

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

def reduced (a d : ℕ) (hd : 0 < d) : ℚ :=
  let r := reduce a d
  ⟨(r.1 : ℤ),r.2,
    by change (reduce a d).2 ≠ 0; rw [reduce_eq]; exact (binomial_reduce_fraction a d hd).2.2.1.ne',
    by change ((reduce a d).1 : ℤ).natAbs.Coprime (reduce a d).2
       rw [reduce_eq]; simpa only [Int.natAbs_natCast] using (binomial_reduce_fraction a d hd).2.1⟩

theorem reduced_eq (a d : ℕ) (hd : 0 < d) : reduced a d hd = (binomialReducedRat a d hd).1 := by
  simp only [reduced,binomialReducedRat,reduce_eq]

def signed (a : ℤ) (d : ℕ) : ℚ :=
  if hd : d = 0 then 0 else
    let q := reduced a.natAbs d (Nat.pos_of_ne_zero hd)
    if a < 0 then -q else q

theorem signed_eq (a : ℤ) (d : ℕ) : signed a d = (binomialSignedRat a d).1 := by
  simp only [signed,binomialSignedRat,reduced_eq]
  split <;> rfl

def signedAdd (s t : Bool) (xs ys : List Bool) : ℤ :=
  let k := max xs.length ys.length
  if Bool.xor s t then
    if compare k xs ys true then binomialSignedMagnitude t (binomialBitValue (subtract k ys xs true).1)
    else binomialSignedMagnitude s (binomialBitValue (subtract k xs ys true).1)
  else binomialSignedMagnitude s (binomialBitValue (add k xs ys false))

theorem signedAdd_eq (s t : Bool) (xs ys : List Bool) :
    signedAdd s t xs ys = (binomialSignedAddBits s t xs ys).1 := by
  simp only [signedAdd,binomialSignedAddBits,compare_eq,subtract_eq,add_eq]
  split
  · split <;> rfl
  · rfl

def ratMul (a b : ℚ) : ℚ :=
  let n := mul a.num.natAbs.bits b.num.natAbs.bits
  let d := mul a.den.bits b.den.bits
  let s := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  signed (binomialSignedMagnitude s (binomialBitValue n)) (binomialBitValue d)

def ratDiv (a b : ℚ) : ℚ :=
  let n := mul a.num.natAbs.bits b.den.bits
  let d := mul a.den.bits b.num.natAbs.bits
  let s := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  signed (binomialSignedMagnitude s (binomialBitValue n)) (binomialBitValue d)

def ratAdd (a b : ℚ) : ℚ :=
  let x := mul a.num.natAbs.bits b.den.bits
  let y := mul b.num.natAbs.bits a.den.bits
  let d := mul a.den.bits b.den.bits
  signed (signedAdd (decide (a.num < 0)) (decide (b.num < 0)) x y) (binomialBitValue d)

def ratSub (a b : ℚ) : ℚ := ratAdd a (-b)

theorem ratMul_eq (a b : ℚ) : ratMul a b = (binomialRatMulBits a b).1 := by
  simp only [ratMul,binomialRatMulBits,mul_eq,signed_eq]

theorem ratDiv_eq (a b : ℚ) : ratDiv a b = (binomialRatDivBits a b).1 := by
  simp only [ratDiv,binomialRatDivBits,mul_eq,signed_eq]

theorem ratAdd_eq (a b : ℚ) : ratAdd a b = (binomialRatAddBits a b).1 := by
  simp only [ratAdd,binomialRatAddBits,mul_eq,signed_eq,signedAdd_eq]

theorem ratSub_eq (a b : ℚ) : ratSub a b = (binomialRatSubBits a b).1 := ratAdd_eq _ _

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased
