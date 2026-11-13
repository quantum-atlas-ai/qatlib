/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.WeakPeriod
import Qatlib.Papers.SimonSymKey16.FeistelPeriod.Algebra

/-!
# Feistel periods in the native Simon sampling model

The encodings `encodeInput` and `decodeInput` connect binary blocks and selector bits to the
register representation used by the Simon circuit. The explicit Feistel period becomes
`nativePeriod`, giving a normalized circuit output with zero probability on characters that take
value negative one on that period. See [SantoliSchaffner2017] for the source development.

## Main statements

* `three_round_composition`: identifies the composition of three Feistel round permutations with
  `feistel3`.
* `native_period`: transports Feistel periodicity to register shifts.
* `feistel_nonorthogonal_probability`: excludes outcomes whose input-register character is
  negative on the period.

## References

* [Santoli and Schaffner, 2017][SantoliSchaffner2017]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SimonSymKey16.FeistelPeriod
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PeriodSampling.WeakPeriod
variable {n : ℕ}

/-- The binary scalar corresponding to a Boolean, sending false to zero and true to one. -/
def bitScalar (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The Boolean recording whether a binary scalar equals one. -/
def scalarBit (x : ZMod 2) : Bool := decide (x = 1)

/-- Converting a Boolean to a binary scalar and back recovers the Boolean. -/
theorem scalarBit_bitScalar (b : Bool) : scalarBit (bitScalar b) = b := by
  cases b <;> decide

/-- Converting a binary scalar to a Boolean and back recovers the scalar. -/
theorem bitScalar_scalarBit (x : ZMod 2) : bitScalar (scalarBit x) = x := by
  fin_cases x <;> decide

/-- Boolean exclusive-or becomes addition under `bitScalar`. -/
theorem bitScalar_xor (b c : Bool) : bitScalar (b ^^ c) = bitScalar b + bitScalar c := by
  cases b <;> cases c <;> decide

/-- The Boolean register encoding of a binary block, obtained by applying `scalarBit`
coordinatewise. -/
def encodeBlock (a : Block n) : Reg n := fun i => scalarBit (a i)

/-- The decoding of an `(n + 1)`-bit register into its first Boolean bit and the binary block
formed by its remaining bits. -/
def decodeInput (x : Reg (n+1)) : Bool × Block n :=
  (x 0, fun i => bitScalar (x i.succ))

/-- The register encoding of a selector bit and a binary block, placing the selector in the
first position. -/
def encodeInput (u : Bool × Block n) : Reg (n+1) := Fin.cons u.1 (encodeBlock u.2)

/-- Decoding the encoding of a selector-block pair recovers that pair. -/
theorem decode_encode (u : Bool × Block n) : decodeInput (encodeInput u) = u := by
  apply Prod.ext
  · simp [decodeInput, encodeInput]
  · funext i
    simp [decodeInput, encodeInput, encodeBlock, bitScalar_scalarBit]

/-- Decoding a register shifted by an encoded selector-block pair gives `bxorShift` of the
decoded register by that pair. -/
theorem decode_shift (x : Reg (n+1)) (s : Bool × Block n) :
    decodeInput (shift x (encodeInput s)) = bxorShift (decodeInput x) s := by
  apply Prod.ext
  · cases h : s.1 <;> simp [decodeInput, shift, encodeInput, bxorShift, h]
  · funext i
    simp [decodeInput, shift, encodeInput, encodeBlock, bxorShift,
      bitScalar_xor, bitScalar_scalarBit]

/-- The Feistel round permutation `(a, c) ↦ (c, a + P c)`, with its explicit inverse. -/
def roundPerm (P : Block n → Block n) : Equiv.Perm (Block n × Block n) where
  toFun := fun u => (u.2, u.1 + P u.2)
  invFun := fun v => (v.2 + P v.1, v.1)
  left_inv := by rintro ⟨a,b⟩; simp [block_add_self_add]
  right_inv := by rintro ⟨a,b⟩; simp [block_add_self_add]

/-- Composing the three round permutations in order gives the pair defined by `feistel3 P1 P2
P3`. See [SantoliSchaffner2017]. -/
theorem three_round_composition (P1 P2 P3 : Block n → Block n) (a c : Block n) :
    ((roundPerm P1).trans ((roundPerm P2).trans (roundPerm P3))) (a,c) =
      feistel3 P1 P2 P3 a c := rfl

/-- The Feistel-derived Simon function expressed as a map between Boolean registers by decoding
its input and encoding its output. -/
def nativeFunction (P1 P2 : Block n → Block n) (α β : Block n) : Reg (n+1) → Reg n :=
  fun x => encodeBlock (feistelSimonFun P1 P2 α β (decodeInput x))

/-- The Boolean register encoding of the explicit Feistel period. -/
def nativePeriod (P1 : Block n → Block n) (α β : Block n) : Reg (n+1) :=
  encodeInput (feistelPeriod P1 α β)

/-- The encoded Feistel period is not the all-zero register. See [SantoliSchaffner2017]. -/
theorem nativePeriod_nonzero (P1 : Block n → Block n) (α β : Block n) :
    nativePeriod P1 α β ≠ ZeroStr (n+1) := by
  intro h
  have hh := congrFun h 0
  simp [nativePeriod, encodeInput, feistelPeriod, ZeroStr] at hh

/-- The native Feistel function is invariant under shifting its input by `nativePeriod P1 α β`.
See [SantoliSchaffner2017]. -/
theorem native_period (P1 P2 : Block n → Block n) (α β : Block n) (x : Reg (n+1)) :
    nativeFunction P1 P2 α β (shift x (nativePeriod P1 α β)) =
      nativeFunction P1 P2 α β x := by
  unfold nativeFunction nativePeriod
  rw [decode_shift, feistel3_simon_period]

/-- The Simon circuit output associated with the native Feistel function is normalized. See
[SantoliSchaffner2017]. -/
theorem feistel_output_normalized (P1 P2 : Block n → Block n) (α β : Block n) :
    Normalized (output (nativeFunction P1 P2 α β)) := output_normalized _

/-- The Simon circuit output assigns probability zero to outcomes whose input-register character
evaluates to negative one on the native Feistel period. See [SantoliSchaffner2017]. -/
theorem feistel_nonorthogonal_probability (P1 P2 : Block n → Block n) (α β : Block n) :
    MeasureProb (output (nativeFunction P1 P2 α β))
      (Finset.univ.filter (fun q : Space (n+1) n => character q.1 (nativePeriod P1 α β) = -1)) = 0 :=
  nonorthogonal_event_zero _ _ (native_period P1 P2 α β)
end
end Qatlib.Papers.SimonSymKey16.FeistelPeriod
