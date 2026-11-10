/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.FrameDecode
import Qatlib.Papers.MonteCarloInt20.MainResults.NestedPreparation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore
open Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg Qatlib.Papers.MonteCarloInt20.PrnJump.Affine
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Stride

def sampleIndex {s : ℕ} (j : Reg s) : Fin (2^s) := ⟨booleanWordLSBValue s j,Bits.lsb_lt s j⟩

def termIndex {d : ℕ} (i : Reg d) : Fin (2^d+1) :=
  ⟨booleanWordLSBValue d i+1,by have := Bits.lsb_lt d i; omega⟩

def position {s d : ℕ} (j : Reg s) (i : Reg d) : ℕ := strided (2^d) (sampleIndex j) (termIndex i)

theorem position_source {s d : ℕ} (j : Reg s) (i : Reg d) :
    position j i=booleanWordLSBValue s j*(2^d+1)+(booleanWordLSBValue d i+1)+1 := rfl

def commonPosition {s d : ℕ} (j : Reg s) : ℕ := booleanWordLSBValue s j*(2^d+1)+1

theorem position_after_common {s d : ℕ} (j : Reg s) (i : Reg d) :
    position j i=commonPosition (d:=d) j+booleanWordLSBValue d i+1 := by
  rw [position_source,commonPosition]
  omega

theorem position_bounds {s d : ℕ} (j : Reg s) (i : Reg d) :
    0<position j i ∧ position j i≤2^s*(2^d+1) :=
  strided_bounds (2^d) (sampleIndex j) (termIndex i)

def exponentBits {s d : ℕ} (j : Reg s) (i : Reg d) : Reg (s+d+1) :=
  Bits.ofNat (s+d+1) (position j i)

theorem exponentBits_value {s d : ℕ} (hd : 0 < d) (j : Reg s) (i : Reg d) :
    booleanWordLSBValue (s+d+1) (exponentBits j i)=position j i := by
  rw [exponentBits,Bits.ofNat_value]
  exact Nat.mod_eq_of_lt (strided_bit_bound s d hd (sampleIndex j) (termIndex i))

def xorShift {w : ℕ} (mask : Reg w) (x : Reg w) : Reg w := fun q => x q ^^ mask q

theorem xorShift_involutive {w : ℕ} (mask : Reg w) : Function.Involutive (xorShift mask) := by
  intro x
  funext q
  dsimp only [xorShift]
  cases x q <;> cases mask q <;> rfl

def xorMatrix {w : ℕ} (mask : Reg w) : Matrix (Reg w) (Reg w) ℂ := permMatrix (xorShift mask)

theorem xorMatrix_unitary {w : ℕ} (mask : Reg w) : xorMatrix mask ∈ unitaryGroup (Reg w) ℂ :=
  permMatrix_unitary (xorShift_involutive mask)

theorem xorMatrix_frame {w : ℕ} (x y : Reg w) :
    ApplyGate (xorMatrix (fun q => y q ^^ x q)) (Ket x)=Ket y := by
  rw [xorMatrix,applyGate_permMatrix_ket (xorShift_involutive _)]
  congr 1
  funext q
  dsimp only [xorShift]
  cases x q <;> cases y q <;> rfl

def loaderMask {n s d : ℕ} (seed : ZMod (2^n)) (j : Reg s) (i : Reg d) : Reg (width n (s+d+1)) :=
  fun q => frame (exponentBits j i) seed q ^^ frame (ZeroStr (s+d+1)) seed q

def nativeJumpMatrix {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    Matrix (Reg (width n k)) (Reg (width n k)) ℂ :=
  runMatrix 1 (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin k => q))))

theorem nativeJumpMatrix_unitary {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    nativeJumpMatrix (k:=k) a c ∈ unitaryGroup (Reg (width n k)) ℂ :=
  runMatrix_unitary 1 _ (by simp) (native_unitary a c _)

theorem nativeJumpMatrix_stride {n s d : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ)
    (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    ApplyGate (nativeJumpMatrix (k:=s+d+1) a c) (Ket (frame (exponentBits j i) seed))=
      Ket (frame (exponentBits j i) (lcg (a:ZMod (2^n)) c seed (position j i))) := by
  rw [nativeJumpMatrix,runMatrix_apply]
  exact strided_native_basis n s d hd a c seed (sampleIndex j) (termIndex i)

def strideCompute {n s d : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    Matrix (Reg (width n (s+d+1))) (Reg (width n (s+d+1))) ℂ :=
  nativeJumpMatrix a c*xorMatrix (loaderMask seed j i)

theorem strideCompute_unitary {n s d : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    strideCompute a c seed j i ∈ unitaryGroup (Reg (width n (s+d+1))) ℂ :=
  (unitaryGroup _ ℂ).mul_mem (nativeJumpMatrix_unitary a c) (xorMatrix_unitary _)

theorem strideCompute_basis {n s d : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ)
    (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    ApplyGate (strideCompute a c seed j i) (Ket (frame (ZeroStr (s+d+1)) seed))=
      Ket (frame (exponentBits j i) (lcg (a:ZMod (2^n)) c seed (position j i))) := by
  rw [strideCompute,applyGate_mul]
  have h := xorMatrix_frame (frame (ZeroStr (s+d+1)) seed) (frame (exponentBits j i) seed)
  rw [show xorMatrix (loaderMask seed j i)=xorMatrix (fun q => frame (exponentBits j i) seed q ^^
      frame (ZeroStr (s+d+1)) seed q) from rfl,h,nativeJumpMatrix_stride hd]

end Qatlib.Papers.MonteCarloInt20.PrnJump.Stride
