/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.WalshProgram

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open LinearCodeProgram

variable {N q : ℕ}

def generators (label : Fin N → Fin q → ZMod 2) : Fin q → Fin N → ZMod 2 :=
  fun i j => label j i

def database (t : Fin N) : Fin N → ZMod 2 := Pi.single t 1

theorem response_database (label : Fin N → Fin q → ZMod 2) (t : Fin N) :
    response (generators label) (database t) = label t := by
  classical
  funext i
  simp [response, answer, generators, database, Pi.single_apply, mul_ite]

theorem run_walsh (label : Fin N → Fin q → ZMod 2) (t : Fin N) :
    Run (oracle (database t)) (word (generators label))
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod 2))) =
    TensorState (TensorState (Ket (label t)) (Ket 0)) (charState (1:ZMod 2)) := by
  rw [run_word, response_database]

theorem walsh_probability (label : Fin N → Fin q → ZMod 2) (t : Fin N) :
    QueryCount (word (generators label)) = 1 ∧
    MeasureProb (Run (oracle (database t)) (word (generators label))
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod 2))))
      (({label t} ×ˢ Finset.univ) ×ˢ Finset.univ) = 1 := by
  refine ⟨(word_resources _).1, ?_⟩
  simpa only [response_database] using response_probability (generators label) (database t)

theorem index_decoder [NeZero N] (label : Fin N → Fin q → ZMod 2)
    (hl : Function.Injective label) (t : Fin N) :
    Function.invFun label (response (generators label) (database t)) = t := by
  rw [response_database]
  exact Function.leftInverse_invFun hl t

theorem padded_labels_exist (N q : ℕ) (hN : N ≤ 2^q) :
    ∃ label : Fin N → Fin q → ZMod 2, Function.Injective label := by
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (Fin q → ZMod 2) := by simpa using hN
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨e, e.injective⟩

theorem singleton_zero_digits :
    Function.Injective (fun _ : Fin 1 => (0 : Fin 0 → ZMod 2)) := by
  intro a b _
  exact Subsingleton.elim a b

end Qatlib.Papers.SingleQuery97.MainResults.WalshProgram
