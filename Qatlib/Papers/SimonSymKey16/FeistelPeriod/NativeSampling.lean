/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.WeakPeriod
import Qatlib.Papers.SimonSymKey16.FeistelPeriod.Algebra
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SimonSymKey16.FeistelPeriod
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PeriodSampling.WeakPeriod
variable {n : ℕ}

def bitScalar (b : Bool) : ZMod 2 := if b then 1 else 0

def scalarBit (x : ZMod 2) : Bool := decide (x = 1)

theorem scalarBit_bitScalar (b : Bool) : scalarBit (bitScalar b) = b := by
  cases b <;> decide

theorem bitScalar_scalarBit (x : ZMod 2) : bitScalar (scalarBit x) = x := by
  fin_cases x <;> decide

theorem bitScalar_xor (b c : Bool) : bitScalar (b ^^ c) = bitScalar b + bitScalar c := by
  cases b <;> cases c <;> decide

def encodeBlock (a : Block n) : Reg n := fun i => scalarBit (a i)

def decodeInput (x : Reg (n+1)) : Bool × Block n :=
  (x 0, fun i => bitScalar (x i.succ))

def encodeInput (u : Bool × Block n) : Reg (n+1) := Fin.cons u.1 (encodeBlock u.2)

theorem decode_encode (u : Bool × Block n) : decodeInput (encodeInput u) = u := by
  apply Prod.ext
  · simp [decodeInput, encodeInput]
  · funext i
    simp [decodeInput, encodeInput, encodeBlock, bitScalar_scalarBit]

theorem decode_shift (x : Reg (n+1)) (s : Bool × Block n) :
    decodeInput (shift x (encodeInput s)) = bxorShift (decodeInput x) s := by
  apply Prod.ext
  · cases h : s.1 <;> simp [decodeInput, shift, encodeInput, bxorShift, h]
  · funext i
    simp [decodeInput, shift, encodeInput, encodeBlock, bxorShift,
      bitScalar_xor, bitScalar_scalarBit]

def roundPerm (P : Block n → Block n) : Equiv.Perm (Block n × Block n) where
  toFun := fun u => (u.2, u.1 + P u.2)
  invFun := fun v => (v.2 + P v.1, v.1)
  left_inv := by rintro ⟨a,b⟩; simp [block_add_self_add]
  right_inv := by rintro ⟨a,b⟩; simp [block_add_self_add]

theorem three_round_composition (P1 P2 P3 : Block n → Block n) (a c : Block n) :
    ((roundPerm P1).trans ((roundPerm P2).trans (roundPerm P3))) (a,c) =
      feistel3 P1 P2 P3 a c := rfl

def nativeFunction (P1 P2 : Block n → Block n) (α β : Block n) : Reg (n+1) → Reg n :=
  fun x => encodeBlock (feistelSimonFun P1 P2 α β (decodeInput x))

def nativePeriod (P1 : Block n → Block n) (α β : Block n) : Reg (n+1) :=
  encodeInput (feistelPeriod P1 α β)

theorem nativePeriod_nonzero (P1 : Block n → Block n) (α β : Block n) :
    nativePeriod P1 α β ≠ ZeroStr (n+1) := by
  intro h
  have hh := congrFun h 0
  simp [nativePeriod, encodeInput, feistelPeriod, ZeroStr] at hh

theorem native_period (P1 P2 : Block n → Block n) (α β : Block n) (x : Reg (n+1)) :
    nativeFunction P1 P2 α β (shift x (nativePeriod P1 α β)) =
      nativeFunction P1 P2 α β x := by
  unfold nativeFunction nativePeriod
  rw [decode_shift, feistel3_simon_period]

theorem feistel_output_normalized (P1 P2 : Block n → Block n) (α β : Block n) :
    Normalized (output (nativeFunction P1 P2 α β)) := output_normalized _

theorem feistel_nonorthogonal_probability (P1 P2 : Block n → Block n) (α β : Block n) :
    MeasureProb (output (nativeFunction P1 P2 α β))
      (Finset.univ.filter (fun q : Space (n+1) n => character q.1 (nativePeriod P1 α β) = -1)) = 0 :=
  nonorthogonal_event_zero _ _ (native_period P1 P2 α β)
end
end Qatlib.Papers.SimonSymKey16.FeistelPeriod
