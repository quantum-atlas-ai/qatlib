/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.CompiledJump
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Frame
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic

def dataBits (n k : ℕ) (y : Reg (width n k)) : Reg (n+1) :=
  fun j => y ⟨j.val,by dsimp only [width]; have := j.isLt; omega⟩

def decodeNative (n k : ℕ) (y : Reg (width n k)) : ZMod (2^n) :=
  (booleanWordLSBValue (n+1) (dataBits n k y) : ZMod (2^n))

theorem dataBits_frame {n k : ℕ} (bits : Reg k) (x : ZMod (2^n)) :
    dataBits n k (frame bits x) = encode n x := by
  funext j
  have hj : j.val < (n+1)+k := by have := j.isLt; omega
  simp only [dataBits,frame,booleanDAGInput,dif_pos hj]
  have he : (⟨j.val,hj⟩ : Fin ((n+1)+k)) = Fin.castAdd k j := Fin.ext rfl
  rw [he,Fin.append_left]

theorem decodeNative_frame {n k : ℕ} (bits : Reg k) (x : ZMod (2^n)) :
    decodeNative n k (frame bits x) = x := by
  simp only [decodeNative,dataBits_frame,encode_value,ZMod.natCast_zmod_val]
end Qatlib.Papers.MonteCarloInt20.PrnJump.Frame
