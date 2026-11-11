/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Addition

/-!
# Erased bit and rational arithmetic

`BinomialErased` implements Boolean-list arithmetic and rational operations with the gate
counters removed. The equality theorems identify each erased computation with the value
component of its corresponding counted computation, including Euclidean reduction and signed
rational arithmetic.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `divmod_eq`: erased division returns the counted quotient and remainder.
* `gcd_eq`: erased and counted GCD computations return the same bits.
* `ratAdd_eq`: erasure preserves the result of rational addition.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

/-- Adds `k` little-endian bit positions with initial carry `c`, appending the final carry and
padding missing input bits with `false`. -/
def add : ℕ → List Bool → List Bool → Bool → List Bool
  | 0, _, _, c => [c]
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (ys.headD false) c
    f.1 :: add k xs.tail ys.tail f.2

/-- Conjoins each input bit with `b`, preserving the length of the bit list. -/
def mask (b : Bool) : List Bool → List Bool
  | [] => []
  | y::ys => Bool.and b y :: mask b ys

/-- Computes a bit-list product by recursive shifts, Boolean masking, and addition, without
tracking gate counts. -/
def mul : List Bool → List Bool → List Bool
  | [], _ => []
  | b::bs, ys => add (2*bs.length+ys.length+1) (false::mul bs ys) (mask b ys) false

/-- Iterates the comparison-carry recurrence over `k` bit positions, using `c` as the initial
comparison state. -/
def compare : ℕ → List Bool → List Bool → Bool → Bool
  | 0, _, _, c => c
  | k+1, xs, ys, c => compare k xs.tail ys.tail
      (binomialCompareCarry (xs.headD false) (ys.headD false) c)

/-- Processes `k` positions by adding the complemented second input with initial carry `c`,
returning the output bits and final carry. -/
def subtract : ℕ → List Bool → List Bool → Bool → List Bool × Bool
  | 0, _, _, c => ([],c)
  | k+1, xs, ys, c =>
    let f := binomialFullAdder (xs.headD false) (!(ys.headD false)) c
    let r := subtract k xs.tail ys.tail f.2
    (f.1::r.1,r.2)

/-- Returns the Boolean disjunction of all bits in the list. -/
def any : List Bool → Bool
  | [] => false
  | b::bs => Bool.or b (any bs)

/-- Computes quotient and remainder bit lists by recursive binary division with divisor `ds`. -/
def divmod (ds : List Bool) : List Bool → List Bool × List Bool
  | [] => ([],[])
  | b::bs =>
    let r := divmod ds bs
    let candidate := b::r.2
    let k := max candidate.length ds.length
    if compare k ds candidate true then
      (true::r.1,(subtract k candidate ds true).1)
    else (false::r.1,candidate)

/-- Runs at most `k` rounds of the erased Euclidean procedure, truncating intermediate
remainders to `w` bits. -/
def gcdRun (w : ℕ) : ℕ → List Bool → List Bool → List Bool
  | 0, xs, _ => xs
  | k+1, xs, ys =>
    if any ys then
      let r := (divmod ys xs).2.take w
      if any r then gcdRun w k r ((divmod r ys).2.take w) else ys
    else xs

/-- Runs the erased GCD procedure with width and round budget equal to the larger input length. -/
def gcd (xs ys : List Bool) : List Bool :=
    gcdRun (max xs.length ys.length) (max xs.length ys.length) xs ys

/-- Divides the bit representations of `a` and `d` by their computed GCD and returns the decoded
quotients. -/
def reduce (a d : ℕ) : ℕ × ℕ :=
  let g := gcd a.bits d.bits
  (binomialBitValue (divmod g a.bits).1,binomialBitValue (divmod g d.bits).1)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

/-- Erased addition equals the value component of `binomialBitAdd`. -/
theorem add_eq (k : ℕ) (xs ys : List Bool) (c : Bool) :
    add k xs ys c = (binomialBitAdd k xs ys c).1 := by
  induction k generalizing xs ys c with
  | zero => rfl
  | succ k ih => simp only [add,binomialBitAdd,ih]

/-- Erased masking equals the value component of `binomialBitMask`. -/
theorem mask_eq (b : Bool) (xs : List Bool) : mask b xs = (binomialBitMask b xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mask,binomialBitMask,ih]

/-- Erased multiplication equals the value component of `binomialBitMul`. -/
theorem mul_eq (xs ys : List Bool) : mul xs ys = (binomialBitMul xs ys).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mul,binomialBitMul,ih,mask_eq,add_eq]

/-- Erased comparison equals the Boolean result of `binomialBitCompare`. -/
theorem compare_eq (k : ℕ) (xs ys : List Bool) (c : Bool) :
    compare k xs ys c = (binomialBitCompare k xs ys c).1 := by
  induction k generalizing xs ys c with
  | zero => rfl
  | succ k ih => simp only [compare,binomialBitCompare,ih]

/-- Erased subtraction returns the same output bits and final carry as `binomialBitSubtract`. -/
theorem subtract_eq (k : ℕ) (xs ys : List Bool) (c : Bool) :
    subtract k xs ys c = (binomialBitSubtract k xs ys c).1 := by
  induction k generalizing xs ys c with
  | zero => rfl
  | succ k ih => simp only [subtract,binomialBitSubtract,ih]

/-- Erased disjunction equals the Boolean result of `binomialBitAny`. -/
theorem any_eq (xs : List Bool) : any xs = (binomialBitAny xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [any,binomialBitAny,ih]

/-- Erased division returns the quotient and remainder of `binomialBitDivmod`. -/
theorem divmod_eq (xs ys : List Bool) : divmod xs ys =
    ((binomialBitDivmod xs ys).quotient,(binomialBitDivmod xs ys).remainder) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [divmod,binomialBitDivmod,ih,compare_eq,subtract_eq]
    split <;> rfl

/-- The erased bounded Euclidean procedure returns the bits of `binomialGcdRun`. -/
theorem gcdRun_eq (w k : ℕ) (xs ys : List Bool) :
    gcdRun w k xs ys = (binomialGcdRun w k xs ys).bits := by
  induction k generalizing xs ys with
  | zero => rfl
  | succ k ih =>
    simp only [gcdRun,binomialGcdRun,any_eq,divmod_eq]
    split
    · split <;> simp only [ih]
    · rfl

/-- Erased GCD returns the bits of `binomialBitGcd`. -/
theorem gcd_eq (xs ys : List Bool) : gcd xs ys = (binomialBitGcd xs ys).bits :=
  gcdRun_eq _ _ _ _

/-- Erased fraction reduction equals the value component of `binomialReduceFraction`. -/
theorem reduce_eq (a d : ℕ) : reduce a d = (binomialReduceFraction a d).1 := by
  simp only [reduce,binomialReduceFraction,gcd_eq,divmod_eq]

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased

/-- Constructs a rational from the erased reduced numerator and denominator, using positivity of
`d` to certify the denominator. -/
def reduced (a d : ℕ) (hd : 0 < d) : ℚ :=
  let r := reduce a d
  ⟨(r.1 : ℤ),r.2,
    by change (reduce a d).2 ≠ 0; rw [reduce_eq]; exact (binomial_reduce_fraction a d hd).2.2.1.ne',
    by change ((reduce a d).1 : ℤ).natAbs.Coprime (reduce a d).2
       rw [reduce_eq]; simpa only [Int.natAbs_natCast] using (binomial_reduce_fraction a d hd).2.1⟩

/-- The rational constructed by erased reduction equals the value component of
`binomialReducedRat`. -/
theorem reduced_eq (a d : ℕ) (hd : 0 < d) : reduced a d hd = (binomialReducedRat a d hd).1 := by
  simp only [reduced,binomialReducedRat,reduce_eq]

/-- Constructs a signed rational by reducing the numerator magnitude and restoring its sign,
returning zero when `d` is zero. -/
def signed (a : ℤ) (d : ℕ) : ℚ :=
  if hd : d = 0 then 0 else
    let q := reduced a.natAbs d (Nat.pos_of_ne_zero hd)
    if a < 0 then -q else q

/-- Erased signed rational construction equals the value component of `binomialSignedRat`. -/
theorem signed_eq (a : ℤ) (d : ℕ) : signed a d = (binomialSignedRat a d).1 := by
  simp only [signed,binomialSignedRat,reduced_eq]
  split <;> rfl

/-- Adds two signed bit-list magnitudes by magnitude addition or comparison and subtraction
according to their sign bits. -/
def signedAdd (s t : Bool) (xs ys : List Bool) : ℤ :=
  let k := max xs.length ys.length
  if Bool.xor s t then
    if compare k xs ys true then binomialSignedMagnitude t (binomialBitValue (subtract k ys xs true).1)
    else binomialSignedMagnitude s (binomialBitValue (subtract k xs ys true).1)
  else binomialSignedMagnitude s (binomialBitValue (add k xs ys false))

/-- Erased signed addition equals the integer result of `binomialSignedAddBits`. -/
theorem signedAdd_eq (s t : Bool) (xs ys : List Bool) :
    signedAdd s t xs ys = (binomialSignedAddBits s t xs ys).1 := by
  simp only [signedAdd,binomialSignedAddBits,compare_eq,subtract_eq,add_eq]
  split
  · split <;> rfl
  · rfl

/-- Multiplies rationals through erased numerator and denominator bit multiplication followed by
signed reduction. -/
def ratMul (a b : ℚ) : ℚ :=
  let n := mul a.num.natAbs.bits b.num.natAbs.bits
  let d := mul a.den.bits b.den.bits
  let s := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  signed (binomialSignedMagnitude s (binomialBitValue n)) (binomialBitValue d)

/-- Divides rationals through erased cross multiplication and signed reduction. -/
def ratDiv (a b : ℚ) : ℚ :=
  let n := mul a.num.natAbs.bits b.den.bits
  let d := mul a.den.bits b.num.natAbs.bits
  let s := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  signed (binomialSignedMagnitude s (binomialBitValue n)) (binomialBitValue d)

/-- Adds rationals through erased cross multiplication, signed magnitude addition, and
reduction. -/
def ratAdd (a b : ℚ) : ℚ :=
  let x := mul a.num.natAbs.bits b.den.bits
  let y := mul b.num.natAbs.bits a.den.bits
  let d := mul a.den.bits b.den.bits
  signed (signedAdd (decide (a.num < 0)) (decide (b.num < 0)) x y) (binomialBitValue d)

/-- Computes rational subtraction by erased addition of the negated second operand. -/
def ratSub (a b : ℚ) : ℚ := ratAdd a (-b)

/-- Erased rational multiplication equals the value component of `binomialRatMulBits`. -/
theorem ratMul_eq (a b : ℚ) : ratMul a b = (binomialRatMulBits a b).1 := by
  simp only [ratMul,binomialRatMulBits,mul_eq,signed_eq]

/-- Erased rational division equals the value component of `binomialRatDivBits`. -/
theorem ratDiv_eq (a b : ℚ) : ratDiv a b = (binomialRatDivBits a b).1 := by
  simp only [ratDiv,binomialRatDivBits,mul_eq,signed_eq]

/-- Erased rational addition equals the value component of `binomialRatAddBits`. -/
theorem ratAdd_eq (a b : ℚ) : ratAdd a b = (binomialRatAddBits a b).1 := by
  simp only [ratAdd,binomialRatAddBits,mul_eq,signed_eq,signedAdd_eq]

/-- Erased rational subtraction equals the value component of `binomialRatSubBits`. -/
theorem ratSub_eq (a b : ℚ) : ratSub a b = (binomialRatSubBits a b).1 := ratAdd_eq _ _

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.BinomialErased
