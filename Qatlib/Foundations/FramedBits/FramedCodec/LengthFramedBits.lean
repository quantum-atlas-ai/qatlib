/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.NormNum
import Qatlib.Foundations.FramedBits.FramedCodec.LengthFramedBitsDefs

/-!
# Correctness and lengths of framed bit encodings

This module proves that framed bit strings, lists of bit strings, and signed integers can be
parsed from arbitrary appended suffixes. It establishes prefix freedom for `frame`, injectivity
for `encodeList` and `encodeInt`, and exact encoded lengths for frames and lists.

The bundled statements `g1`, `g2`, and `g3` also record selected malformed inputs and
distinctions between encodings. These finite encodings belong to the classical computational
background of [KitaevShenVyalyi2002].

## Main statements

* `frame_prefix_free`: If one complete frame equals another frame followed by a suffix, the
  payloads are equal and the suffix is empty.
* `encodeList_length`: The list encoding has length one plus twice the item count plus twice the
  total payload length.
* `parseInt_append`: Parsing an encoded signed integer recovers the integer and preserves any
  appended suffix.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.FramedBits.FramedCodec

/-- Parsing a unary length prefix followed by any suffix returns the encoded length and that
suffix. -/
theorem parseLength_prefix (n : ℕ) (tail : List Bool) :
    parseLength (framePrefix n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [framePrefix, List.replicate_succ, parseLength] using
      congrArg (Option.map (fun p : ℕ × List Bool => (p.1 + 1, p.2))) ih

/-- Parsing a framed payload followed by any suffix returns the payload and preserves the
suffix. -/
theorem parseFrame_append (xs tail : List Bool) :
    parseFrame (frame xs ++ tail) = some (xs, tail) := by
  simp [frame, List.append_assoc, parseFrame, parseLength_prefix]

/-- If one complete frame equals another frame followed by a suffix, the payloads are equal and
the suffix is empty. -/
theorem frame_prefix_free (xs ys tail : List Bool)
    (h : frame xs ++ tail = frame ys) : xs = ys ∧ tail = [] := by
  have hp := congrArg parseFrame h
  rw [parseFrame_append, ← List.append_nil (frame ys), parseFrame_append] at hp
  simpa only [Option.some.injEq, Prod.mk.injEq] using hp

/-- The framed encoding of `xs` has length `2 * xs.length + 1`. -/
theorem frame_length (xs : List Bool) : (frame xs).length = 2 * xs.length + 1 := by
  simp [frame, framePrefix]
  omega

/-- Frames parse correctly with arbitrary suffixes, are prefix free, and have length twice the
payload length plus one; the two specified malformed inputs fail to parse. -/
theorem g1 :
    (∀ (xs tail : List Bool), parseFrame (frame xs ++ tail) = some (xs, tail)) ∧
    (∀ (xs ys tail : List Bool), frame xs ++ tail = frame ys → xs = ys ∧ tail = []) ∧
    (∀ xs : List Bool, (frame xs).length = 2 * xs.length + 1) ∧
    parseFrame [true, true, false, true] = none ∧ parseLength [true, true] = none :=
  ⟨parseFrame_append, frame_prefix_free, frame_length, by decide, by decide⟩

/-- Parsing the concatenated frames of a list, with the correct item count, recovers the list
and preserves any appended suffix. -/
theorem parseMany_append (xss : List (List Bool)) (tail : List Bool) :
    parseMany xss.length (xss.flatMap frame ++ tail) = some (xss, tail) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp [parseMany, List.append_assoc, parseFrame_append, ih]

/-- Parsing an encoded list recovers the list and preserves any appended suffix. -/
theorem parseList_append (xss : List (List Bool)) (tail : List Bool) :
    parseList (encodeList xss ++ tail) = some (xss, tail) := by
  simp [encodeList, List.append_assoc, parseList, parseLength_prefix, parseMany_append]

/-- The bit-string list encoding is injective. -/
theorem encodeList_injective : Function.Injective encodeList := by
  intro xs ys h
  have hp := congrArg parseList h
  have hx := parseList_append xs []
  have hy := parseList_append ys []
  simp only [List.append_nil] at hx hy
  rw [hx, hy] at hp
  exact (Option.some.inj hp |> congrArg Prod.fst)

/-- The concatenation of frames has length equal to the item count plus twice the total payload
length. -/
theorem flatMap_frame_length (xss : List (List Bool)) :
    (xss.flatMap frame).length = xss.length + 2 * (xss.map List.length).sum := by
  induction xss with
  | nil => simp
  | cons xs xss ih => simp only [List.flatMap_cons, List.length_append, frame_length,
      List.length_cons, List.map_cons, List.sum_cons, ih]; omega

/-- The list encoding has length one plus twice the item count plus twice the total payload
length. -/
theorem encodeList_length (xss : List (List Bool)) :
    (encodeList xss).length = 1 + 2 * xss.length + 2 * (xss.map List.length).sum := by
  simp only [encodeList, List.length_append, framePrefix, List.length_replicate,
    List.length_singleton, flatMap_frame_length]
  omega

/-- List encodings parse with arbitrary suffixes, are injective, and satisfy the exact length
formula; the specified empty-item and ordering examples have different encodings. -/
theorem g2 :
    (∀ (xss : List (List Bool)) (tail : List Bool),
      parseList (encodeList xss ++ tail) = some (xss, tail)) ∧
    Function.Injective encodeList ∧
    (∀ xss : List (List Bool),
      (encodeList xss).length = 1 + 2 * xss.length + 2 * (xss.map List.length).sum) ∧
    encodeList [[]] ≠ encodeList [] ∧ encodeList [[false], []] ≠ encodeList [[], [false]] :=
  ⟨parseList_append, encodeList_injective, encodeList_length, by decide, by decide⟩

/-- Decoding the canonical binary digits of a natural number recovers that number. -/
theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]

/-- Parsing an encoded signed integer recovers the integer and preserves any appended suffix. -/
theorem parseInt_append (z : ℤ) (tail : List Bool) :
    parseInt (encodeInt z ++ tail) = some (z, tail) := by
  cases z with
  | ofNat n =>
    simp [encodeInt, magnitude, parseInt, parseFrame_append, ofBits_bits]
  | negSucc n =>
    simp [encodeInt, magnitude, parseInt, parseFrame_append, ofBits_bits]
    omega

/-- The signed-integer encoding is injective. -/
theorem encodeInt_injective : Function.Injective encodeInt := by
  intro z w h
  have hp := congrArg parseInt h
  have hz := parseInt_append z []
  have hw := parseInt_append w []
  simp only [List.append_nil] at hz hw
  rw [hz, hw] at hp
  exact (Option.some.inj hp |> congrArg Prod.fst)

/-- Signed-integer encodings parse with arbitrary suffixes and are injective; the specified
larger natural numbers have different encodings, and the negative-zero input fails to parse. -/
theorem g3 :
    (∀ (z : ℤ) (tail : List Bool), parseInt (encodeInt z ++ tail) = some (z, tail)) ∧
    Function.Injective encodeInt ∧
    (∀ n : ℕ, encodeInt (n : ℤ) ≠ encodeInt ((n + 2 ^ (n + 1) : ℕ) : ℤ)) ∧
    parseInt [true, false] = none := by
  refine ⟨parseInt_append, encodeInt_injective, ?_, by decide⟩
  intro n h
  have he := encodeInt_injective h
  have hn : n = n + 2 ^ (n + 1) := by exact_mod_cast he
  have hp : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide)
  omega

end Qatlib.Foundations.FramedBits.FramedCodec
