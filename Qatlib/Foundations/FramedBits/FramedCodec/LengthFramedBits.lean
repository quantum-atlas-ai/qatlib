/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.NormNum
import Qatlib.Foundations.FramedBits.FramedCodec.LengthFramedBitsDefs

set_option autoImplicit false
namespace Qatlib.Foundations.FramedBits.FramedCodec

theorem parseLength_prefix (n : ℕ) (tail : List Bool) :
    parseLength (framePrefix n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [framePrefix, List.replicate_succ, parseLength] using
      congrArg (Option.map (fun p : ℕ × List Bool => (p.1 + 1, p.2))) ih

theorem parseFrame_append (xs tail : List Bool) :
    parseFrame (frame xs ++ tail) = some (xs, tail) := by
  simp [frame, List.append_assoc, parseFrame, parseLength_prefix]

theorem frame_prefix_free (xs ys tail : List Bool)
    (h : frame xs ++ tail = frame ys) : xs = ys ∧ tail = [] := by
  have hp := congrArg parseFrame h
  rw [parseFrame_append, ← List.append_nil (frame ys), parseFrame_append] at hp
  simpa only [Option.some.injEq, Prod.mk.injEq] using hp

theorem frame_length (xs : List Bool) : (frame xs).length = 2 * xs.length + 1 := by
  simp [frame, framePrefix]
  omega

theorem g1 :
    (∀ (xs tail : List Bool), parseFrame (frame xs ++ tail) = some (xs, tail)) ∧
    (∀ (xs ys tail : List Bool), frame xs ++ tail = frame ys → xs = ys ∧ tail = []) ∧
    (∀ xs : List Bool, (frame xs).length = 2 * xs.length + 1) ∧
    parseFrame [true, true, false, true] = none ∧ parseLength [true, true] = none :=
  ⟨parseFrame_append, frame_prefix_free, frame_length, by decide, by decide⟩

theorem parseMany_append (xss : List (List Bool)) (tail : List Bool) :
    parseMany xss.length (xss.flatMap frame ++ tail) = some (xss, tail) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp [parseMany, List.append_assoc, parseFrame_append, ih]

theorem parseList_append (xss : List (List Bool)) (tail : List Bool) :
    parseList (encodeList xss ++ tail) = some (xss, tail) := by
  simp [encodeList, List.append_assoc, parseList, parseLength_prefix, parseMany_append]

theorem encodeList_injective : Function.Injective encodeList := by
  intro xs ys h
  have hp := congrArg parseList h
  have hx := parseList_append xs []
  have hy := parseList_append ys []
  simp only [List.append_nil] at hx hy
  rw [hx, hy] at hp
  exact (Option.some.inj hp |> congrArg Prod.fst)

theorem flatMap_frame_length (xss : List (List Bool)) :
    (xss.flatMap frame).length = xss.length + 2 * (xss.map List.length).sum := by
  induction xss with
  | nil => simp
  | cons xs xss ih => simp only [List.flatMap_cons, List.length_append, frame_length,
      List.length_cons, List.map_cons, List.sum_cons, ih]; omega

theorem encodeList_length (xss : List (List Bool)) :
    (encodeList xss).length = 1 + 2 * xss.length + 2 * (xss.map List.length).sum := by
  simp only [encodeList, List.length_append, framePrefix, List.length_replicate,
    List.length_singleton, flatMap_frame_length]
  omega

theorem g2 :
    (∀ (xss : List (List Bool)) (tail : List Bool),
      parseList (encodeList xss ++ tail) = some (xss, tail)) ∧
    Function.Injective encodeList ∧
    (∀ xss : List (List Bool),
      (encodeList xss).length = 1 + 2 * xss.length + 2 * (xss.map List.length).sum) ∧
    encodeList [[]] ≠ encodeList [] ∧ encodeList [[false], []] ≠ encodeList [[], [false]] :=
  ⟨parseList_append, encodeList_injective, encodeList_length, by decide, by decide⟩

theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]

theorem parseInt_append (z : ℤ) (tail : List Bool) :
    parseInt (encodeInt z ++ tail) = some (z, tail) := by
  cases z with
  | ofNat n =>
    simp [encodeInt, magnitude, parseInt, parseFrame_append, ofBits_bits]
  | negSucc n =>
    simp [encodeInt, magnitude, parseInt, parseFrame_append, ofBits_bits]
    omega

theorem encodeInt_injective : Function.Injective encodeInt := by
  intro z w h
  have hp := congrArg parseInt h
  have hz := parseInt_append z []
  have hw := parseInt_append w []
  simp only [List.append_nil] at hz hw
  rw [hz, hw] at hp
  exact (Option.some.inj hp |> congrArg Prod.fst)

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
