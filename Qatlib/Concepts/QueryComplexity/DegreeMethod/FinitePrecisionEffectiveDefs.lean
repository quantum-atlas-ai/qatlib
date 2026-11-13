/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
import Qatlib.Concepts.ScaledSqrt.SqrtBounds.ScaledRationalSqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Effective arithmetic and complete parameter words

This module defines `mulProgram`, a six-stack binary multiplication program, together with its
register state, intermediate configurations, accumulator model, and step counts. The definitions
supply the operational data for the multiplication correctness proofs; [KitaevShenVyalyi2002]
gives general background on classical and quantum computation.

The interval operations `nativeInterval`, `nativeDiv`, and `nativeSqrt` support finite-precision
arithmetic on encoded rationals. `NameCode` represents rational approximations, and
`CompleteWord` pairs every parameter slot with an amplification factor so that product
evaluation and error accounting use complete slot data.

## Main definitions

* `MulLabel`, `MulVar`, and `mulStacks`: control labels, registers, and stack layout.
* `mulProgram`, `mulAcc`, and `mulTotalTicks`: multiplication code, accumulator, and step-count
  model.
* `nativeDiv` and `nativeSqrt`: optional interval arithmetic operations.
* `NameCode`: binary numerator and denominator words with a precision parameter.
* `CompleteWord`, `completeWordReadProduct`, and `completeWordErrorActual`: matched slot data,
  evaluated products, and error accounts.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.EmitterCore
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ValidatorSemantics
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.ScaledSqrt.SqrtBounds

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open Qatlib.Foundations.IntervalArith.IntervalOps (Interval rounded divPositive)
open Turing

/-- The six control labels of the binary multiplication stack program: outer iteration,
duplication, restoration, addition, flipping, and completion. -/
inductive MulLabel where

  | outer

  | dup

  | restore

  | add

  | flip

  | done
  deriving DecidableEq, Fintype

/-- The finite register state of the multiplication program, recording the current bit, its
presence, optional stack bits, and the addition carry. -/
structure MulVar where

  bit : Bool

  hasBit : Bool

  mbit : Option Bool

  abit : Option Bool

  xbit : Option Bool

  carry : Bool
  deriving DecidableEq

/-- The initial multiplication register state, with Boolean registers false and optional bit
registers empty. -/
def MulVar.init : MulVar := ⟨false, false, none, none, none, false⟩

/-- Store an optional bit and its presence flag, using false as the bit value when the input is
absent. -/
def MulVar.readBit (v : MulVar) (o : Option Bool) : MulVar :=
  { v with bit := o.getD false, hasBit := o.isSome }

/-- Replace the optional master-bit register with the supplied value. -/
def MulVar.readMbit (v : MulVar) (o : Option Bool) : MulVar := { v with mbit := o }

/-- Replace the two optional addition-bit registers and the carry with the supplied values. -/
def MulVar.addPosition (v : MulVar) (abit xbit : Option Bool) (carry : Bool) : MulVar :=
  { v with abit := abit, xbit := xbit, carry := carry }

/-- Clear the two optional addition-bit registers. -/
def MulVar.addEnd (v : MulVar) : MulVar := { v with abit := none, xbit := none }

/-- Replace the optional addition-output bit register with the supplied value. -/
def MulVar.readAbit (v : MulVar) (o : Option Bool) : MulVar := { v with abit := o }

/-- Arrange the six Boolean stacks as accumulator `u`, operand copy `b`, addition output `a`,
master `m`, remaining multiplier `y`, and temporary copy `t`, indexed from zero to five. -/
def mulStacks (u b a m y t : Bits) : Fin 6 → List Bool :=
  fun i => if i = 0 then u else if i = 1 then b else if i = 2 then a
           else if i = 3 then m else if i = 4 then y else t

/-- Stack 0 of `mulStacks u b a m y t` is `u`. -/
@[simp] theorem mulStacks_zero (u b a m y t : Bits) : mulStacks u b a m y t 0 = u := by
  simp [mulStacks]

/-- Stack 1 of `mulStacks u b a m y t` is `b`. -/
@[simp] theorem mulStacks_one (u b a m y t : Bits) : mulStacks u b a m y t 1 = b := by
  simp [mulStacks]

/-- Stack 2 of `mulStacks u b a m y t` is `a`. -/
@[simp] theorem mulStacks_two (u b a m y t : Bits) : mulStacks u b a m y t 2 = a := by
  simp [mulStacks]

/-- Stack 3 of `mulStacks u b a m y t` is `m`. -/
@[simp] theorem mulStacks_three (u b a m y t : Bits) : mulStacks u b a m y t 3 = m := by
  simp [mulStacks]

/-- Stack 4 of `mulStacks u b a m y t` is `y`. -/
@[simp] theorem mulStacks_four (u b a m y t : Bits) : mulStacks u b a m y t 4 = y := by
  simp [mulStacks]

/-- Stack 5 of `mulStacks u b a m y t` is `t`. -/
@[simp] theorem mulStacks_five (u b a m y t : Bits) : mulStacks u b a m y t 5 = t := by
  simp [mulStacks]

/-- Updating stack 0 to `w` replaces the accumulator argument of `mulStacks` by `w`. -/
theorem mulStacks_update_zero (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 0 w = mulStacks w b a m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stack 1 to `w` replaces the operand-copy argument of `mulStacks` by `w`. -/
theorem mulStacks_update_one (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 1 w = mulStacks u w a m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stack 2 to `w` replaces the addition-output argument of `mulStacks` by `w`. -/
theorem mulStacks_update_two (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 2 w = mulStacks u b w m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stack 3 to `w` replaces the master-stack argument of `mulStacks` by `w`. -/
theorem mulStacks_update_three (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 3 w = mulStacks u b a w y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stack 4 to `w` replaces the remaining-multiplier argument of `mulStacks` by `w`. -/
theorem mulStacks_update_four (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 4 w = mulStacks u b a m w t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stack 5 to `w` replaces the temporary-stack argument of `mulStacks` by `w`. -/
theorem mulStacks_update_five (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 5 w = mulStacks u b a m y w := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stacks 4 and 0 replaces the corresponding arguments of `mulStacks` by `w4` and
`w0`. -/
theorem mulStacks_update_four_zero (u b a m y t w0 w4 : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 4 w4) 0 w0
      = mulStacks w0 b a m w4 t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stacks 3, 1, and 5 replaces the corresponding arguments of `mulStacks` by `w3`,
`w1`, and `w5`. -/
theorem mulStacks_update_three_one_five (u b a m y t w1 w3 w5 : Bits) :
    Function.update (Function.update (Function.update (mulStacks u b a m y t) 3 w3) 1 w1) 5 w5
      = mulStacks u w1 a w3 y w5 := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stacks 5 and 3 replaces the corresponding arguments of `mulStacks` by `w5` and
`w3`. -/
theorem mulStacks_update_five_three (u b a m y t w3 w5 : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 5 w5) 3 w3
      = mulStacks u b a w3 y w5 := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stacks 0, 1, and 2 replaces the corresponding arguments of `mulStacks` by `w0`,
`w1`, and `w2`. -/
theorem mulStacks_update_zero_one_two (u b a m y t w0 w1 w2 : Bits) :
    Function.update (Function.update (Function.update (mulStacks u b a m y t) 0 w0) 1 w1) 2 w2
      = mulStacks w0 w1 w2 m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- Updating stacks 2 and 0 replaces the corresponding arguments of `mulStacks` by `w2` and
`w0`. -/
theorem mulStacks_update_two_zero (u b a m y t w0 w2 : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 2 w2) 0 w0
      = mulStacks w0 b w2 m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

/-- The sum bit obtained from the stored carry and the two optional addition bits, treating
absent bits as false. -/
def mulAddBit (v : MulVar) : Bool :=
  (carryStep v.carry (v.abit.getD false) (v.xbit.getD false)).1

/-- The outgoing carry obtained from the stored carry and the two optional addition bits,
treating absent bits as false. -/
def mulAddCarry (v : MulVar) : Bool :=
  (carryStep v.carry (v.abit.getD false) (v.xbit.getD false)).2

/-- The six-stack binary multiplication program, branching on multiplier bits and implementing
shift, duplication, restoration, addition, and reversal phases before halting. -/
def mulProgram (l : MulLabel) : TM2.Stmt (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  match l with
  | .outer =>
      .pop 4 (fun v o => MulVar.readBit v o) (
        .branch (fun v => v.hasBit)
          (.push 0 (fun _ => false) (
            .branch (fun v => v.bit)
              (.load (fun _ => MulVar.init) (.goto (fun _ => .dup)))
              (.load (fun _ => MulVar.init) (.goto (fun _ => .outer)))))
          (.load (fun _ => MulVar.init) (.goto (fun _ => .done))))
  | .dup =>
      .peek 3 (fun v o => { v with mbit := o }) (
        .branch (fun v => v.mbit.isNone)
          (.load (fun _ => MulVar.init) (.goto (fun _ => .restore)))
          (.pop 3 (fun v o => { v with mbit := o }) (
            .push 1 (fun v => v.mbit.getD false) (
              .push 5 (fun v => v.mbit.getD false) (
                .goto (fun _ => .dup))))))
  | .restore =>
      .peek 5 (fun v o => { v with mbit := o }) (
        .branch (fun v => v.mbit.isNone)
          (.load (fun _ => MulVar.init) (.goto (fun _ => .add)))
          (.pop 5 (fun v o => { v with mbit := o }) (
            .push 3 (fun v => v.mbit.getD false) (
              .goto (fun _ => .restore)))))
  | .add =>
      .peek 0 (fun v o => { v with abit := o }) (
        .peek 1 (fun v o => { v with xbit := o }) (
          .branch (fun v => v.abit.isNone && v.xbit.isNone)
            (.push 2 (fun v => v.carry) (.goto (fun _ => .flip)))
            (.pop 0 (fun v _ => v) (
              .pop 1 (fun v _ => v) (
                .push 2 (fun v => mulAddBit v) (
                  .load (fun v => { v with carry := mulAddCarry v, abit := none, xbit := none }) (
                    (.goto (fun _ => .add)))))))))
  | .flip =>
      .peek 2 (fun v o => { v with abit := o }) (
        .branch (fun v => v.abit.isNone)
          (.load (fun _ => MulVar.init) (.goto (fun _ => .outer)))
          (.pop 2 (fun v o => { v with abit := o }) (
            .push 0 (fun v => v.abit.getD false) (
              .goto (fun _ => .flip)))))
  | .done => .halt

/-- The initial multiplication configuration, with empty work stacks, reversed input words in
the master and multiplier stacks, and reset registers. -/
def mulStart (x y : Bits) : TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .outer, MulVar.init, mulStacks [] [] [] (x.reverse) (y.reverse) []⟩

/-- The bit at index `j` of the reversed multiplier word, defaulting to false beyond its length. -/
def mulBit (y : Bits) (j : ℕ) : Bool := ((y.reverse)[j]?).getD false

/-- The natural value of the first `j` bits of the reversed multiplier word, reversed back into
binary-value order. -/
def mulPrefix (y : Bits) (j : ℕ) : ℕ :=
  binaryValue ((y.reverse.take j).reverse)

/-- Add two binary words by processing their maximum length with initial carry false and
appending the final carry bit. -/
def mulAddBits (u b : Bits) : Bits :=
  let r := carryAddAux (max u.length b.length) false u b
  r.1 ++ [r.2]

/-- The recursive multiplication accumulator, initially empty and updated by doubling at each
round and adding `x` when the next multiplier bit is true. -/
def mulAcc (x y : Bits) : ℕ → Bits
  | 0 => []
  | j + 1 =>
      let acc := mulAcc x y j
      if mulBit y j then mulAddBits (false :: acc) x else false :: acc

/-- The outer-loop configuration after `j` modeled rounds, with accumulator `mulAcc x y j`,
master `x.reverse`, and the first `j` reversed multiplier bits removed. -/
def mulCfg (x y : Bits) (j : ℕ) : TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .outer, MulVar.init,
    mulStacks (mulAcc x y j) [] [] (x.reverse) ((y.reverse).drop j) []⟩

/-- A duplication configuration with the reversed first `k` bits of `m` prepended to both copy
stacks and those bits removed from the master stack. -/
def mulDupCfg (v : MulVar) (k : ℕ) (u b a m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .dup, v,
    mulStacks u ((m.take k).reverse ++ b) a (m.drop k) y ((m.take k).reverse ++ t)⟩

/-- A restoration configuration with `(m.take k).reverse ++ m` as master stack and `t.drop k` as
temporary stack. -/
def mulRestoreCfg (v : MulVar) (k : ℕ) (u b a m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .restore, v,
    mulStacks u b a ((m.take k).reverse ++ m) y (t.drop k)⟩

/-- The addition configuration after `k` modeled bit positions, with operand prefixes removed
and the carry and reversed output supplied by `addTurns`. -/
def mulAddCfg (v : MulVar) (k : ℕ) (u b a0 m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .add, MulVar.addPosition v none none (addTurns k ⟨false, u, b, []⟩).carry,
    mulStacks (u.drop k) (b.drop k) ((addTurns k ⟨false, u, b, []⟩).os ++ a0) m y t⟩

/-- The configuration entering the flip phase after addition, with empty operand stacks and the
final carry prepended to the reversed sum output and the original output suffix. -/
def mulAddFinal (v : MulVar) (u b a0 m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .flip,
    MulVar.addPosition v none none (addTurns (max u.length b.length) ⟨false, u, b, []⟩).carry,
    mulStacks [] []
      ((addTurns (max u.length b.length) ⟨false, u, b, []⟩).carry
        :: ((addTurns (max u.length b.length) ⟨false, u, b, []⟩).os ++ a0))
      m y t⟩

/-- The addition configuration at index `k`, using `mulAddCfg` through the maximum operand
length and `mulAddFinal` at larger indices. -/
def mulAddCfgAt (v : MulVar) (k : ℕ) (u b a0 m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  if k ≤ max u.length b.length then mulAddCfg v k u b a0 m y t
  else mulAddFinal v u b a0 m y t

/-- A flip configuration with the reversed first `k` bits of the addition output prepended to
the accumulator and removed from the output stack. -/
def mulFlipCfg (v : MulVar) (k : ℕ) (u b a m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .flip, v,
    mulStacks ((a.take k).reverse ++ u) b (a.drop k) m y t⟩

/-- The stack-2 output of the auxiliary addition of the shifted accumulator and `x`, used to
measure a multiplication round with a true multiplier bit. -/
def mulRoundResult (x y : Bits) (j : ℕ) : Bits :=
  (mulAddFinal MulVar.init (false :: mulAcc x y j) x [] (x.reverse)
    ((y.reverse).drop (j + 1)) []).stk 2

/-- The modeled step count for multiplication round `j`: one step for a false bit, or the
combined shift, duplication, restoration, addition, and flip counts for a true bit. -/
def mulRoundTicks (x y : Bits) (j : ℕ) : ℕ :=
  let acc := mulAcc x y j
  let u := false :: acc
  if mulBit y j then
    let res := mulRoundResult x y j
    1 + ((x.length + 1)
      + ((x.length + 1) + ((max u.length x.length + 1) + (res.length + 1))))
  else 1

/-- The cumulative modeled step count of the first `n` multiplication rounds. -/
def mulTotalTicks (x y : Bits) : ℕ → ℕ
  | 0 => 0
  | n + 1 => mulTotalTicks x y n + mulRoundTicks x y n

/-- The rational interval from `q` to `q + 1 / 2 ^ k`. -/
def nativeCert (q : ℚ) (k : ℕ) : Interval := ⟨q, q + 1 / (2 : ℚ) ^ k⟩

/-- The rounded rational interval for the value represented by `e` at precision `k`. -/
def nativeInterval (e : RatEnc) (k : ℕ) : Interval := rounded e.toRat k

/-- Divide the rounded input intervals using `divPositive` with the supplied denominator gap,
returning an optional quotient interval. -/
def nativeDiv (a b : RatEnc) (gap : ℚ) (k : ℕ) : Option Interval :=
  divPositive (nativeInterval a k) (nativeInterval b k) gap

/-- The rational interval formed from the endpoints of the square-root bracket for `q`, scale
`S`, and refinement count `k`. -/
def sqrtBracket (q : ℚ) (S : ℚ) (k : ℕ) : Interval :=
  let b := Qatlib.Concepts.ScaledSqrt.SqrtBounds.bracket q S k
  ⟨b.1, b.2.1⟩

/-- Return the square-root bracket when `S` is positive and the encoded rational lies between
zero and `S * S`; return `none` otherwise. -/
def nativeSqrt (q : RatEnc) (S : ℚ) (k : ℕ) : Option Interval :=
  if 0 < S ∧ 0 ≤ q.toRat ∧ q.toRat ≤ S * S then some (sqrtBracket q.toRat S k)
  else none

/-- A rational name code consisting of binary numerator and denominator words and a natural
precision parameter. -/
structure NameCode where

  num : Bits

  den : Bits

  prec : ℕ
  deriving DecidableEq, Repr

/-- The size measure obtained by adding the numerator length, denominator length, and precision
parameter. -/
def NameCode.size (c : NameCode) : ℕ := c.num.length + c.den.length + c.prec

/-- Decode the numerator and denominator words as natural numbers and take their quotient in the
rationals. -/
def NameCode.decode (c : NameCode) : ℚ :=
  (binaryValue c.num : ℚ) / (binaryValue c.den : ℚ)

/-- A native parameter word with slots, amplification factors, and phase precision, carrying a
proof that the slot and amplification lists have equal length. -/
structure CompleteWord where

  slots : List (List NativeParam)

  amp : List ℕ

  phaseBits : ℕ

  matched : slots.length = amp.length

/-- The native error-unit count computed from the slots paired with their amplification factors. -/
def completeWordErrorUnits (w : CompleteWord) : ℕ :=
  nativeWordErrorUnitsAux (w.slots.zip w.amp)

/-- The recursive product of a real list, with value one on the empty list. -/
def chainProduct : List ℝ → ℝ
  | [] => 1
  | a :: rest => a * chainProduct rest

/-- The recursive sum of a real list, with value zero on the empty list. -/
def rsum : List ℝ → ℝ
  | [] => 0
  | a :: rest => a + rsum rest

/-- The rational native error account at precision `k` for the complete word's paired slots and
amplification factors. -/
def completeWordErrorActual (w : CompleteWord) (k : ℕ) : ℚ :=
  nativeWordErrorActualAux (w.slots.zip w.amp) k

/-- Flatten a list of parameter slots by concatenating their entries in order. -/
def paramsOfSlots : List (List NativeParam) → List NativeParam
  | [] => []
  | s :: rest => s ++ paramsOfSlots rest

/-- The ordered list of all native parameters obtained by flattening a complete word's slots. -/
def wordParams (w : CompleteWord) : List NativeParam := paramsOfSlots w.slots

/-- The product of the real values read from all parameters of a complete word at precision `k`. -/
def completeWordReadProduct (w : CompleteWord) (k : ℕ) : ℝ :=
  chainProduct ((wordParams w).map (fun p => (p.name.eval k).toReal))

/-- The product of the ideal real values of all parameters of a complete word. -/
def completeWordIdealProduct (w : CompleteWord) : ℝ :=
  chainProduct ((wordParams w).map (fun p => p.name.value))

/-- Build a complete word from a native word and a supplied amplification list of matching
length, preserving the slots and phase precision. -/
def completeWordOf (w : NativeWord) (amp : List ℕ) (h : w.slots.length = amp.length) :
    CompleteWord :=
  { slots := w.slots, amp := amp, phaseBits := w.phaseBits, matched := h }

/-- The complete word with the slots, amplification factors, and phase precision of
`lcuConsumerWord`. -/
def lcuCompleteWord : CompleteWord :=
  { slots := lcuConsumerWord.slots
    amp := lcuConsumerWord.amp
    phaseBits := lcuConsumerWord.phaseBits
    matched := by decide }

end Qatlib.Concepts.QueryComplexity.DegreeMethod
