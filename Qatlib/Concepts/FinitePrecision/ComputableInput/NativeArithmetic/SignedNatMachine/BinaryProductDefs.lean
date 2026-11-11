/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.FramedBinaryAddition

/-!
# Binary product loops and span bounds

`BinaryProductDefs.loop` multiplies little-endian Boolean words by repeated shifting and
conditional addition to an accumulator. The potential `span` controls current and final word
lengths and does not increase during a loop step; the value theorem identifies the output as the
initial accumulator plus the input product.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `value`: the shift-and-add loop computes the accumulator plus the product.
* `step_span`: the span does not increase in a loop step.
* `length` and `initial_span`: output and initial span bounds.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.BinaryProductDefs

open PaidBinaryAddition (columns digits output)

/-- The paired addition-column list has length equal to the maximum of the two input word
lengths. -/
theorem columns_length_max (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (columns a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [columns]
  | cons x xs ih =>
    cases b with
    | nil => simp [columns]
    | cons y ys => simp only [columns, List.length_cons, ih]; omega

/-- The output word of binary addition has length at most the maximum input length plus one. -/
theorem add_length (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (output a b).length ≤ max a.length b.length + 1 := by
  have h := PaidBinaryAddition.digits_length (columns a b) false
  simpa only [columns_length_max] using! h

/-- Processes multiplier bits by conditionally adding the current multiplicand to the
accumulator and shifting the multiplicand left at each step. -/
def loop (a : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | [], acc => acc
  | bit :: bs, acc => loop (false :: a) bs (if bit then output acc a else acc)

/-- The word-length potential `max acc.length (a.length + b.length) + b.length + 1` for the
multiplication loop. -/
def span (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : ℕ :=
    max acc.length (a.length + b.length) + b.length + 1

/-- The multiplication-loop span is at least one. -/
theorem span_pos (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    1 ≤ span a b acc := by unfold span; omega

/-- Shifting the multiplicand and conditionally updating the accumulator for one multiplier bit
does not increase the span. -/
theorem step_span (a bs acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bit : Bool) :
    span (false :: a) bs (if bit then output acc a else acc) ≤ span a (bit :: bs) acc := by
  have h := add_length acc a
  cases bit <;> simp only [Bool.false_eq_true, if_false, if_true, span, List.length_cons] <;> omega

/-- The span bounds both the current multiplicand length plus one and the accumulator length
plus one. -/
theorem current_lengths (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    a.length + 1 ≤ span a b acc ∧ acc.length + 1 ≤ span a b acc := by
  unfold span
  omega

/-- The loop output represents the initial accumulator value plus the product of the
multiplicand and multiplier values. -/
theorem value (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (loop a b acc) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue acc + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b := by
  induction b generalizing a acc with
  | nil => simp [loop, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue]
  | cons bit bs ih =>
    rw [loop, ih]
    cases bit <;> simp only [Bool.false_eq_true, if_false, if_true,
      PaidBinaryAddition.output_value, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat.binary_cons, Nat.bit, Bool.cond_false, Bool.cond_true]
    all_goals ring

/-- The output word length plus one is at most the initial span. -/
theorem length (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (loop a b acc).length + 1 ≤ span a b acc := by
  induction b generalizing a acc with
  | nil => unfold loop span; simp only [List.length_nil, Nat.add_zero]; omega
  | cons bit bs ih =>
    exact (ih (false :: a) (if bit then output acc a else acc)).trans (step_span a bs acc bit)

/-- With an empty accumulator, the span is the multiplicand length plus twice the multiplier
length plus one. -/
theorem initial_span (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : span a b [] = a.length + 2 * b.length + 1 := by
  simp [span]
  omega

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.BinaryProductDefs
