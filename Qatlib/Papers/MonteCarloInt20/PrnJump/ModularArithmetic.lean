/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.Recurrence
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits
open scoped Classical
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic

theorem modulus_fits (n : ℕ) : 2^n < 2^(n+1) := by
  rw [pow_succ]
  have hp : 0<2^n := by positivity
  omega

def encode (n : ℕ) (x : ZMod (2^n)) : Reg (n+1) := ofNat (n+1) x.val

def modulusBits (n : ℕ) : Reg (n+1) := ofNat (n+1) (2^n)

theorem encode_value (n : ℕ) (x : ZMod (2^n)) : booleanWordLSBValue (n+1) (encode n x) = x.val := by
  rw [encode, ofNat_value, Nat.mod_eq_of_lt (x.val_lt.trans (modulus_fits n))]

theorem modulus_value (n : ℕ) : booleanWordLSBValue (n+1) (modulusBits n) = 2^n := by
  rw [modulusBits, ofNat_value, Nat.mod_eq_of_lt (modulus_fits n)]

theorem native_mul_value (n : ℕ) (a x : ZMod (2^n)) :
    Native.mulFunction (n+1) (encode n a) (modulusBits n) (encode n x) = encode n (a*x) := by
  apply lsb_injective (n+1)
  rw [Native.mul_function_value, encode_value, encode_value, modulus_value, encode_value]
  simp only [Arithmetic.totalMul, x.val_lt, Nat.pow_pos (by decide : 0<2), and_self, ite_true,
    ZMod.val_mul]

theorem native_add_value (n : ℕ) (c x : ZMod (2^n)) :
    Native.addFunction (n+1) (encode n c) (modulusBits n) (encode n x) = encode n (x+c) := by
  apply lsb_injective (n+1)
  rw [Native.add_function_value, encode_value, encode_value, modulus_value, encode_value]
  simp only [Arithmetic.totalAdd, x.val_lt, Nat.pow_pos (by decide : 0<2), and_self, ite_true,
    ZMod.val_add]

theorem native_mul_basis (n : ℕ) (a : (ZMod (2^n))ˣ) (x : ZMod (2^n)) :
    Run 1 (reflectionCompile (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)))
      (Ket (booleanDAGInput (n+1) (Native.mulWork (n+1)) (n+1) (encode n x) (fun _ => false))) =
      Ket (booleanDAGInput (n+1) (Native.mulWork (n+1)) (n+1) (encode n ((a:ZMod (2^n))*x)) (fun _ => false)) := by
  have hc : (booleanWordLSBValue (n+1) (encode n (a:ZMod (2^n)))).Coprime
      (booleanWordLSBValue (n+1) (modulusBits n)) := by
    rw [encode_value, modulus_value]
    exact ZMod.val_coe_unit_coprime a
  have h := Native.mul_basis (n+1) (encode n (a:ZMod (2^n))) (modulusBits n) (encode n x) hc
  rw [native_mul_value] at h
  exact h

theorem native_add_basis (n : ℕ) (c x : ZMod (2^n)) :
    Run 1 (reflectionCompile (Native.addWord (n+1) (encode n c) (modulusBits n)))
      (Ket (booleanDAGInput (n+1) (Native.addWork (n+1)) (n+1) (encode n x) (fun _ => false))) =
      Ket (booleanDAGInput (n+1) (Native.addWork (n+1)) (n+1) (encode n (x+c)) (fun _ => false)) := by
  have h := Native.add_basis (n+1) (encode n c) (modulusBits n) (encode n x)
  rw [native_add_value] at h
  exact h

theorem native_mul_count (n : ℕ) (a : (ZMod (2^n))ˣ) :
    reflectionLegal (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)) ∧
    GateCount (reflectionCompile (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n))) =
      (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)).length ∧
    (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)).length ≤
      5460*(n+1)^2+1565*(n+1)+420 := by
  have h := Native.mul_resources (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)
  exact ⟨h.1, h.2.2.2.1, h.2.1⟩

end Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic
