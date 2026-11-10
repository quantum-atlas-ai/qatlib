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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

inductive MulLabel where

  | outer

  | dup

  | restore

  | add

  | flip

  | done
  deriving DecidableEq, Fintype

structure MulVar where

  bit : Bool

  hasBit : Bool

  mbit : Option Bool

  abit : Option Bool

  xbit : Option Bool

  carry : Bool
  deriving DecidableEq

def MulVar.init : MulVar := ⟨false, false, none, none, none, false⟩

def MulVar.readBit (v : MulVar) (o : Option Bool) : MulVar :=
  { v with bit := o.getD false, hasBit := o.isSome }

def MulVar.readMbit (v : MulVar) (o : Option Bool) : MulVar := { v with mbit := o }

def MulVar.addPosition (v : MulVar) (abit xbit : Option Bool) (carry : Bool) : MulVar :=
  { v with abit := abit, xbit := xbit, carry := carry }

def MulVar.addEnd (v : MulVar) : MulVar := { v with abit := none, xbit := none }

def MulVar.readAbit (v : MulVar) (o : Option Bool) : MulVar := { v with abit := o }

def mulStacks (u b a m y t : Bits) : Fin 6 → List Bool :=
  fun i => if i = 0 then u else if i = 1 then b else if i = 2 then a
           else if i = 3 then m else if i = 4 then y else t

@[simp] theorem mulStacks_zero (u b a m y t : Bits) : mulStacks u b a m y t 0 = u := by
  simp [mulStacks]

@[simp] theorem mulStacks_one (u b a m y t : Bits) : mulStacks u b a m y t 1 = b := by
  simp [mulStacks]

@[simp] theorem mulStacks_two (u b a m y t : Bits) : mulStacks u b a m y t 2 = a := by
  simp [mulStacks]

@[simp] theorem mulStacks_three (u b a m y t : Bits) : mulStacks u b a m y t 3 = m := by
  simp [mulStacks]

@[simp] theorem mulStacks_four (u b a m y t : Bits) : mulStacks u b a m y t 4 = y := by
  simp [mulStacks]

@[simp] theorem mulStacks_five (u b a m y t : Bits) : mulStacks u b a m y t 5 = t := by
  simp [mulStacks]

theorem mulStacks_update_zero (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 0 w = mulStacks w b a m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_one (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 1 w = mulStacks u w a m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_two (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 2 w = mulStacks u b w m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_three (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 3 w = mulStacks u b a w y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_four (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 4 w = mulStacks u b a m w t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_five (u b a m y t w : Bits) :
    Function.update (mulStacks u b a m y t) 5 w = mulStacks u b a m y w := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_four_zero (u b a m y t w0 w4 : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 4 w4) 0 w0
      = mulStacks w0 b a m w4 t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_three_one_five (u b a m y t w1 w3 w5 : Bits) :
    Function.update (Function.update (Function.update (mulStacks u b a m y t) 3 w3) 1 w1) 5 w5
      = mulStacks u w1 a w3 y w5 := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_five_three (u b a m y t w3 w5 : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 5 w5) 3 w3
      = mulStacks u b a w3 y w5 := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_zero_one_two (u b a m y t w0 w1 w2 : Bits) :
    Function.update (Function.update (Function.update (mulStacks u b a m y t) 0 w0) 1 w1) 2 w2
      = mulStacks w0 w1 w2 m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem mulStacks_update_two_zero (u b a m y t w0 w2 : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 2 w2) 0 w0
      = mulStacks w0 b w2 m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

def mulAddBit (v : MulVar) : Bool :=
  (carryStep v.carry (v.abit.getD false) (v.xbit.getD false)).1

def mulAddCarry (v : MulVar) : Bool :=
  (carryStep v.carry (v.abit.getD false) (v.xbit.getD false)).2

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

def mulStart (x y : Bits) : TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .outer, MulVar.init, mulStacks [] [] [] (x.reverse) (y.reverse) []⟩

def mulBit (y : Bits) (j : ℕ) : Bool := ((y.reverse)[j]?).getD false

def mulPrefix (y : Bits) (j : ℕ) : ℕ :=
  binaryValue ((y.reverse.take j).reverse)

def mulAddBits (u b : Bits) : Bits :=
  let r := carryAddAux (max u.length b.length) false u b
  r.1 ++ [r.2]

def mulAcc (x y : Bits) : ℕ → Bits
  | 0 => []
  | j + 1 =>
      let acc := mulAcc x y j
      if mulBit y j then mulAddBits (false :: acc) x else false :: acc

def mulCfg (x y : Bits) (j : ℕ) : TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .outer, MulVar.init,
    mulStacks (mulAcc x y j) [] [] (x.reverse) ((y.reverse).drop j) []⟩

def mulDupCfg (v : MulVar) (k : ℕ) (u b a m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .dup, v,
    mulStacks u ((m.take k).reverse ++ b) a (m.drop k) y ((m.take k).reverse ++ t)⟩

def mulRestoreCfg (v : MulVar) (k : ℕ) (u b a m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .restore, v,
    mulStacks u b a ((m.take k).reverse ++ m) y (t.drop k)⟩

def mulAddCfg (v : MulVar) (k : ℕ) (u b a0 m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .add, MulVar.addPosition v none none (addTurns k ⟨false, u, b, []⟩).carry,
    mulStacks (u.drop k) (b.drop k) ((addTurns k ⟨false, u, b, []⟩).os ++ a0) m y t⟩

def mulAddFinal (v : MulVar) (u b a0 m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .flip,
    MulVar.addPosition v none none (addTurns (max u.length b.length) ⟨false, u, b, []⟩).carry,
    mulStacks [] []
      ((addTurns (max u.length b.length) ⟨false, u, b, []⟩).carry
        :: ((addTurns (max u.length b.length) ⟨false, u, b, []⟩).os ++ a0))
      m y t⟩

def mulAddCfgAt (v : MulVar) (k : ℕ) (u b a0 m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  if k ≤ max u.length b.length then mulAddCfg v k u b a0 m y t
  else mulAddFinal v u b a0 m y t

def mulFlipCfg (v : MulVar) (k : ℕ) (u b a m y t : Bits) :
    TM2.Cfg (fun _ : Fin 6 => Bool) MulLabel MulVar :=
  ⟨some .flip, v,
    mulStacks ((a.take k).reverse ++ u) b (a.drop k) m y t⟩

def mulRoundResult (x y : Bits) (j : ℕ) : Bits :=
  (mulAddFinal MulVar.init (false :: mulAcc x y j) x [] (x.reverse)
    ((y.reverse).drop (j + 1)) []).stk 2

def mulRoundTicks (x y : Bits) (j : ℕ) : ℕ :=
  let acc := mulAcc x y j
  let u := false :: acc
  if mulBit y j then
    let res := mulRoundResult x y j
    1 + ((x.length + 1)
      + ((x.length + 1) + ((max u.length x.length + 1) + (res.length + 1))))
  else 1

def mulTotalTicks (x y : Bits) : ℕ → ℕ
  | 0 => 0
  | n + 1 => mulTotalTicks x y n + mulRoundTicks x y n

def nativeCert (q : ℚ) (k : ℕ) : Interval := ⟨q, q + 1 / (2 : ℚ) ^ k⟩

def nativeInterval (e : RatEnc) (k : ℕ) : Interval := rounded e.toRat k

def nativeDiv (a b : RatEnc) (gap : ℚ) (k : ℕ) : Option Interval :=
  divPositive (nativeInterval a k) (nativeInterval b k) gap

def sqrtBracket (q : ℚ) (S : ℚ) (k : ℕ) : Interval :=
  let b := Qatlib.Concepts.ScaledSqrt.SqrtBounds.bracket q S k
  ⟨b.1, b.2.1⟩

def nativeSqrt (q : RatEnc) (S : ℚ) (k : ℕ) : Option Interval :=
  if 0 < S ∧ 0 ≤ q.toRat ∧ q.toRat ≤ S * S then some (sqrtBracket q.toRat S k)
  else none

structure NameCode where

  num : Bits

  den : Bits

  prec : ℕ
  deriving DecidableEq, Repr

def NameCode.size (c : NameCode) : ℕ := c.num.length + c.den.length + c.prec

def NameCode.decode (c : NameCode) : ℚ :=
  (binaryValue c.num : ℚ) / (binaryValue c.den : ℚ)

structure CompleteWord where

  slots : List (List NativeParam)

  amp : List ℕ

  phaseBits : ℕ

  matched : slots.length = amp.length

def completeWordErrorUnits (w : CompleteWord) : ℕ :=
  nativeWordErrorUnitsAux (w.slots.zip w.amp)

def chainProduct : List ℝ → ℝ
  | [] => 1
  | a :: rest => a * chainProduct rest

def rsum : List ℝ → ℝ
  | [] => 0
  | a :: rest => a + rsum rest

def completeWordErrorActual (w : CompleteWord) (k : ℕ) : ℚ :=
  nativeWordErrorActualAux (w.slots.zip w.amp) k

def paramsOfSlots : List (List NativeParam) → List NativeParam
  | [] => []
  | s :: rest => s ++ paramsOfSlots rest

def wordParams (w : CompleteWord) : List NativeParam := paramsOfSlots w.slots

def completeWordReadProduct (w : CompleteWord) (k : ℕ) : ℝ :=
  chainProduct ((wordParams w).map (fun p => (p.name.eval k).toReal))

def completeWordIdealProduct (w : CompleteWord) : ℝ :=
  chainProduct ((wordParams w).map (fun p => p.name.value))

def completeWordOf (w : NativeWord) (amp : List ℕ) (h : w.slots.length = amp.length) :
    CompleteWord :=
  { slots := w.slots, amp := amp, phaseBits := w.phaseBits, matched := h }

def lcuCompleteWord : CompleteWord :=
  { slots := lcuConsumerWord.slots
    amp := lcuConsumerWord.amp
    phaseBits := lcuConsumerWord.phaseBits
    matched := by decide }

end Qatlib.Concepts.QueryComplexity.DegreeMethod
