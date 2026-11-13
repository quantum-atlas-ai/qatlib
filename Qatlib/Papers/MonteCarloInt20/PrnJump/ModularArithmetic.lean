/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.Recurrence

/-!
# Native arithmetic for power-of-two residues

`encode` and `modulusBits` represent elements of `ZMod (2^n)` and their modulus using `n+1`
bits. The module connects guarded word arithmetic to residue addition and multiplication,
including basis-state execution of the native gate programs used for PRN updates. See
[KanekoEtAl2020].

## Main statements

* `native_mul_value` and `native_add_value`: compatibility of word functions with residue
  arithmetic.
* `native_mul_basis` and `native_add_basis`: native circuit semantics with clean auxiliary
  registers.
* `native_mul_count`: legality and a polynomial multiplication gate bound.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- The modulus `2^n` fits in `n+1` bits. -/
theorem modulus_fits (n : ℕ) : 2^n < 2^(n+1) := by
  rw [pow_succ]
  have hp : 0<2^n := by positivity
  omega

/-- Encodes a residue modulo `2^n` by its canonical representative in an `n+1`-bit word. -/
def encode (n : ℕ) (x : ZMod (2^n)) : Reg (n+1) := ofNat (n+1) x.val

/-- The `n+1`-bit word encoding the modulus `2^n`. -/
def modulusBits (n : ℕ) : Reg (n+1) := ofNat (n+1) (2^n)

/-- The encoded residue has numerical value equal to its canonical representative. -/
theorem encode_value (n : ℕ) (x : ZMod (2^n)) : booleanWordLSBValue (n+1) (encode n x) = x.val := by
  rw [encode, ofNat_value, Nat.mod_eq_of_lt (x.val_lt.trans (modulus_fits n))]

/-- The modulus word has numerical value `2^n`. -/
theorem modulus_value (n : ℕ) : booleanWordLSBValue (n+1) (modulusBits n) = 2^n := by
  rw [modulusBits, ofNat_value, Nat.mod_eq_of_lt (modulus_fits n)]

/-- Native word multiplication on encoded residues equals encoding their product modulo `2^n`. -/
theorem native_mul_value (n : ℕ) (a x : ZMod (2^n)) :
    Native.mulFunction (n+1) (encode n a) (modulusBits n) (encode n x) = encode n (a*x) := by
  apply lsb_injective (n+1)
  rw [Native.mul_function_value, encode_value, encode_value, modulus_value, encode_value]
  simp only [Arithmetic.totalMul, x.val_lt, Nat.pow_pos (by decide : 0<2), and_self, ite_true,
    ZMod.val_mul]

/-- Native word addition on encoded residues equals encoding their sum modulo `2^n`. -/
theorem native_add_value (n : ℕ) (c x : ZMod (2^n)) :
    Native.addFunction (n+1) (encode n c) (modulusBits n) (encode n x) = encode n (x+c) := by
  apply lsb_injective (n+1)
  rw [Native.add_function_value, encode_value, encode_value, modulus_value, encode_value]
  simp only [Arithmetic.totalAdd, x.val_lt, Nat.pow_pos (by decide : 0<2), and_self, ite_true,
    ZMod.val_add]

/-- Multiplication by a unit is implemented by the native word program on encoded basis states
with auxiliary registers restored. -/
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

/-- Residue addition is implemented by the native word program on encoded basis states with
auxiliary registers restored. -/
theorem native_add_basis (n : ℕ) (c x : ZMod (2^n)) :
    Run 1 (reflectionCompile (Native.addWord (n+1) (encode n c) (modulusBits n)))
      (Ket (booleanDAGInput (n+1) (Native.addWork (n+1)) (n+1) (encode n x) (fun _ => false))) =
      Ket (booleanDAGInput (n+1) (Native.addWork (n+1)) (n+1) (encode n (x+c)) (fun _ => false)) := by
  have h := Native.add_basis (n+1) (encode n c) (modulusBits n) (encode n x)
  rw [native_add_value] at h
  exact h

/-- The native multiplication program is legal, its compiled gate count equals its length, and
that length satisfies the stated quadratic bound. -/
theorem native_mul_count (n : ℕ) (a : (ZMod (2^n))ˣ) :
    reflectionLegal (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)) ∧
    GateCount (reflectionCompile (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n))) =
      (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)).length ∧
    (Native.mulWord (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)).length ≤
      5460*(n+1)^2+1565*(n+1)+420 := by
  have h := Native.mul_resources (n+1) (encode n (a:ZMod (2^n))) (modulusBits n)
  exact ⟨h.1, h.2.2.2.1, h.2.1⟩

end Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic
