/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.FramedBinaryAddition
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.BinaryProductDefs

open PaidBinaryAddition (columns digits output)

theorem columns_length_max (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (columns a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [columns]
  | cons x xs ih =>
    cases b with
    | nil => simp [columns]
    | cons y ys => simp only [columns, List.length_cons, ih]; omega

theorem add_length (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (output a b).length ≤ max a.length b.length + 1 := by
  have h := PaidBinaryAddition.digits_length (columns a b) false
  simpa only [columns_length_max] using! h

def loop (a : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | [], acc => acc
  | bit :: bs, acc => loop (false :: a) bs (if bit then output acc a else acc)

def span (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : ℕ :=
    max acc.length (a.length + b.length) + b.length + 1

theorem span_pos (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    1 ≤ span a b acc := by unfold span; omega

theorem step_span (a bs acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bit : Bool) :
    span (false :: a) bs (if bit then output acc a else acc) ≤ span a (bit :: bs) acc := by
  have h := add_length acc a
  cases bit <;> simp only [Bool.false_eq_true, if_false, if_true, span, List.length_cons] <;> omega

theorem current_lengths (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    a.length + 1 ≤ span a b acc ∧ acc.length + 1 ≤ span a b acc := by
  unfold span
  omega

theorem value (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (loop a b acc) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue acc + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b := by
  induction b generalizing a acc with
  | nil => simp [loop, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue]
  | cons bit bs ih =>
    rw [loop, ih]
    cases bit <;> simp only [Bool.false_eq_true, if_false, if_true,
      PaidBinaryAddition.output_value, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat.binary_cons, Nat.bit, Bool.cond_false, Bool.cond_true]
    all_goals ring

theorem length (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (loop a b acc).length + 1 ≤ span a b acc := by
  induction b generalizing a acc with
  | nil => unfold loop span; simp only [List.length_nil, Nat.add_zero]; omega
  | cons bit bs ih =>
    exact (ih (false :: a) (if bit then output acc a else acc)).trans (step_span a bs acc bit)

theorem initial_span (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : span a b [] = a.length + 2 * b.length + 1 := by
  simp [span]
  omega

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.BinaryProductDefs
