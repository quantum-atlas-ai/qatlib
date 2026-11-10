/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.SmithFramingDefs
import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecovery
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.IntWordFraming.WordFraming
set_option warningAsError false

lemma span_loop_trues (n : ℕ) (rest acc : List Bool) :
    List.span.loop id (List.replicate n true ++ false :: rest) acc =
      (((List.replicate n true).reverse ++ acc).reverse, false :: rest) := by
  induction n generalizing acc with
  | zero =>
    simp [List.span.loop]
  | succ n ih =>
    simp [List.replicate_succ, List.span.loop, ih, List.reverse_append, List.reverse_cons,
      List.append_assoc]

lemma span_true_prefix (n : ℕ) (rest : List Bool) :
    List.span id (List.replicate n true ++ false :: rest) =
      (List.replicate n true, false :: rest) := by
  simp [List.span, span_loop_trues]

lemma decodeInt_append (z : ℤ) (extra : List Bool) :
    decodeInt (encodeInt z ++ extra) = some (z, extra) := by
  have hlist : encodeInt z ++ extra =
      List.replicate z.natAbs.bits.length true ++
        false :: decide (z < 0) :: (z.natAbs.bits ++ extra) := by
    simp [encodeInt, List.append_assoc]
  rw [hlist, decodeInt, span_true_prefix]
  simp [List.length_replicate, List.length_append]
  exact smithDecodeInteger_encode z

lemma decodeWords_append (zs : List ℤ) (tail : List Bool) :
    decodeWords zs.length (encodeWords zs ++ tail) = some (zs, tail) := by
  induction zs generalizing tail with
  | nil =>
    simp [decodeWords, encodeWords]
  | cons z zs ih =>
    simp only [List.length_cons, encodeWords, List.flatMap_cons, List.append_assoc, decodeWords]
    rw [decodeInt_append, ← encodeWords]
    simp [ih]

lemma encodeInt_length (z : ℤ) :
    (encodeInt z).length = 2 + 2 * z.natAbs.bits.length := by
  simp [encodeInt, List.length_append, List.length_replicate]
  omega

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

lemma decodeInt_truncated_header : decodeInt [true] = none := by
  simp [decodeInt, List.span, List.span.loop]

theorem g1 :
    (∀ (zs : List ℤ) (tail : List Bool),
      decodeWords zs.length (encodeWords zs ++ tail) = some (zs, tail)) ∧
    (∀ zs : List ℤ, (encodeWords zs).length =
      2 * zs.length + 2 * (zs.map (fun z => z.natAbs.bits.length)).sum) ∧
    decodeInt [true] = none :=
  ⟨decodeWords_append, encodeWords_length, decodeInt_truncated_header⟩

end Qatlib.Concepts.IntWordFraming.WordFraming
