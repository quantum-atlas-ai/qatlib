/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.SmithFramingDefs
import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecovery

/-!
# Round-trip laws for integer word framing

This module proves that the self-delimiting integer encoding can be decoded in front of any
suffix. `decodeWords_append` gives the word-list round trip, and `encodeWords_length` computes
its exact bit length. These framing utilities support the integer presentation data used in
finite Abelian group computations [CheungMosca2001].

## Main statements

* `decodeWords_append`: decode a prescribed number of words while preserving the suffix.
* `g1`: collect the round trip, length formula, and truncated-header rejection.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.IntWordFraming.WordFraming
set_option warningAsError false

/-- Evaluate the Boolean span loop on `n` true bits followed by a false delimiter, retaining the
accumulated prefix. -/
lemma span_loop_trues (n : ℕ) (rest acc : List Bool) :
    List.span.loop id (List.replicate n true ++ false :: rest) acc =
      (((List.replicate n true).reverse ++ acc).reverse, false :: rest) := by
  induction n generalizing acc with
  | zero =>
    simp [List.span.loop]
  | succ n ih =>
    simp [List.replicate_succ, List.span.loop, ih, List.reverse_append, List.reverse_cons,
      List.append_assoc]

/-- Splitting at the first false bit extracts exactly the replicated true prefix and leaves the
delimiter with the remaining bits. -/
lemma span_true_prefix (n : ℕ) (rest : List Bool) :
    List.span id (List.replicate n true ++ false :: rest) =
      (List.replicate n true, false :: rest) := by
  simp [List.span, span_loop_trues]

/-- Decoding an encoded integer followed by an arbitrary suffix returns that integer and the
untouched suffix. -/
lemma decodeInt_append (z : ℤ) (extra : List Bool) :
    decodeInt (encodeInt z ++ extra) = some (z, extra) := by
  have hlist : encodeInt z ++ extra =
      List.replicate z.natAbs.bits.length true ++
        false :: decide (z < 0) :: (z.natAbs.bits ++ extra) := by
    simp [encodeInt, List.append_assoc]
  rw [hlist, decodeInt, span_true_prefix]
  simp [List.length_replicate, List.length_append]
  exact smithDecodeInteger_encode z

/-- Decoding `zs.length` words from their encoding followed by `tail` returns `zs` and the
untouched tail. -/
lemma decodeWords_append (zs : List ℤ) (tail : List Bool) :
    decodeWords zs.length (encodeWords zs ++ tail) = some (zs, tail) := by
  induction zs generalizing tail with
  | nil =>
    simp [decodeWords, encodeWords]
  | cons z zs ih =>
    simp only [List.length_cons, encodeWords, List.flatMap_cons, List.append_assoc, decodeWords]
    rw [decodeInt_append, ← encodeWords]
    simp [ih]

/-- An encoded integer uses two framing bits plus twice the bit length of its absolute value. -/
lemma encodeInt_length (z : ℤ) :
    (encodeInt z).length = 2 + 2 * z.natAbs.bits.length := by
  simp [encodeInt, List.length_append, List.length_replicate]
  omega

/-- An encoded word list uses twice the number of words plus twice the sum of their magnitude
bit lengths. -/
lemma encodeWords_length (zs : List ℤ) :
    (encodeWords zs).length =
      2 * zs.length + 2 * (zs.map (fun z => z.natAbs.bits.length)).sum := by
  induction zs with
  | nil =>
    simp [encodeWords]
  | cons z zs ih =>
    simp only [encodeWords, List.flatMap_cons, List.length_append, encodeInt_length]
    rw [show (List.flatMap encodeInt zs).length = (encodeWords zs).length by rfl, ih]
    simp [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- The one-bit input consisting of a true header bit fails integer decoding. -/
lemma decodeInt_truncated_header : decodeInt [true] = none := by
  simp [decodeInt, List.span, List.span.loop]

/-- Integer word framing preserves arbitrary suffixes on decoding, has the stated exact length
formula, and rejects the truncated header `[true]`. -/
theorem g1 :
    (∀ (zs : List ℤ) (tail : List Bool),
      decodeWords zs.length (encodeWords zs ++ tail) = some (zs, tail)) ∧
    (∀ zs : List ℤ, (encodeWords zs).length =
      2 * zs.length + 2 * (zs.map (fun z => z.natAbs.bits.length)).sum) ∧
    decodeInt [true] = none :=
  ⟨decodeWords_append, encodeWords_length, decodeInt_truncated_header⟩

end Qatlib.Concepts.IntWordFraming.WordFraming
