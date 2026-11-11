/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram

/-!
# Walsh labels and exact index recovery

This module represents a marked database location by `database` and forms binary query
generators from a label family. It proves exact one-query recovery of the label, inverse
decoding for injective labels, and existence of injective labels whenever `N ≤ 2^q`, supporting
Walsh search in [TerhalSmolin1998].

## Main statements

* `walsh_probability`: The Walsh word uses one oracle query and yields the marked location's
  label in the first register with probability one.
* `padded_labels_exist`: If `N ≤ 2^q`, the `N` database locations possess injective binary
  labels of length `q`, as needed for [TerhalSmolin1998].

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.WalshProgram

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open LinearCodeProgram

variable {N q : ℕ}

/-- The binary query-generator matrix obtained by transposing the label family. -/
def generators (label : Fin N → Fin q → ZMod 2) : Fin q → Fin N → ZMod 2 :=
  fun i j => label j i

/-- The binary database with a single nonzero entry at the marked location `t`. -/
def database (t : Fin N) : Fin N → ZMod 2 := Pi.single t 1

/-- The generator-response vector of a singleton database equals the label of its marked
location. -/
theorem response_database (label : Fin N → Fin q → ZMod 2) (t : Fin N) :
    response (generators label) (database t) = label t := by
  classical
  funext i
  simp [response, answer, generators, database, Pi.single_apply, mul_ite]

/-- The Walsh instance of the linear-code word returns the marked location's label and clears
the workspace. -/
theorem run_walsh (label : Fin N → Fin q → ZMod 2) (t : Fin N) :
    Run (oracle (database t)) (word (generators label))
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod 2))) =
    TensorState (TensorState (Ket (label t)) (Ket 0)) (charState (1:ZMod 2)) := by
  rw [run_word, response_database]

/-- The Walsh word uses one oracle query and yields the marked location's label in the first
register with probability one. -/
theorem walsh_probability (label : Fin N → Fin q → ZMod 2) (t : Fin N) :
    QueryCount (word (generators label)) = 1 ∧
    MeasureProb (Run (oracle (database t)) (word (generators label))
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod 2))))
      (({label t} ×ˢ Finset.univ) ×ˢ Finset.univ) = 1 := by
  refine ⟨(word_resources _).1, ?_⟩
  simpa only [response_database] using response_probability (generators label) (database t)

/-- For an injective label family, applying its inverse to the measured response recovers the
marked index, as in the Walsh search construction of [TerhalSmolin1998]. -/
theorem index_decoder [NeZero N] (label : Fin N → Fin q → ZMod 2)
    (hl : Function.Injective label) (t : Fin N) :
    Function.invFun label (response (generators label) (database t)) = t := by
  rw [response_database]
  exact Function.leftInverse_invFun hl t

/-- If `N ≤ 2^q`, the `N` database locations possess injective binary labels of length `q`, as
needed for [TerhalSmolin1998]. -/
theorem padded_labels_exist (N q : ℕ) (hN : N ≤ 2^q) :
    ∃ label : Fin N → Fin q → ZMod 2, Function.Injective label := by
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (Fin q → ZMod 2) := by simpa using hN
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨e, e.injective⟩

/-- A singleton database family possesses an injective labeling with zero binary coordinates,
covering the zero-digit boundary case of [TerhalSmolin1998]. -/
theorem singleton_zero_digits :
    Function.Injective (fun _ : Fin 1 => (0 : Fin 0 → ZMod 2)) := by
  intro a b _
  exact Subsingleton.elim a b

end Qatlib.Papers.SingleQuery97.MainResults.WalshProgram
