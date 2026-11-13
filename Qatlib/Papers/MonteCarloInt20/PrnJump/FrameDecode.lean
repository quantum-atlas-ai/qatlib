/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.CompiledJump

/-!
# Decoding native PRN frames

`dataBits` extracts the residue word from the compiled PRN register frame, and `decodeNative`
interprets it modulo `2 ^ n`. The frame identities show that this decoding recovers the original
residue, connecting the native representation to the finite term oracles used for
[KanekoEtAl2020].

## Main statements

* `dataBits_frame`: recovers the encoded residue word from a clean frame.
* `decodeNative_frame`: recovers the original residue from its frame.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Frame
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic

/-- Extract the first `n + 1` data bits from a native PRN register word. -/
def dataBits (n k : ℕ) (y : Reg (width n k)) : Reg (n+1) :=
  fun j => y ⟨j.val,by dsimp only [width]; have := j.isLt; omega⟩

/-- Interpret the extracted native data word as an unsigned integer reduced modulo `2 ^ n`. -/
def decodeNative (n k : ℕ) (y : Reg (width n k)) : ZMod (2^n) :=
  (booleanWordLSBValue (n+1) (dataBits n k y) : ZMod (2^n))

/-- Extracting the data bits of a native frame returns the encoding of its residue. -/
theorem dataBits_frame {n k : ℕ} (bits : Reg k) (x : ZMod (2^n)) :
    dataBits n k (frame bits x) = encode n x := by
  funext j
  have hj : j.val < (n+1)+k := by have := j.isLt; omega
  simp only [dataBits,frame,booleanDAGInput,dif_pos hj]
  have he : (⟨j.val,hj⟩ : Fin ((n+1)+k)) = Fin.castAdd k j := Fin.ext rfl
  rw [he,Fin.append_left]

/-- Decoding a native frame returns its original residue. -/
theorem decodeNative_frame {n k : ℕ} (bits : Reg k) (x : ZMod (2^n)) :
    decodeNative n k (frame bits x) = x := by
  simp only [decodeNative,dataBits_frame,encode_value,ZMod.natCast_zmod_val]
end Qatlib.Papers.MonteCarloInt20.PrnJump.Frame
