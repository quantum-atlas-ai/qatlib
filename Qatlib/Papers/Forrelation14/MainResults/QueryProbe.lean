/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Forrelation14.MainResults.ForrelationModel

@[expose] public section


/-! # A zero-query inhabitant exposes the free acceptance interface
The archived quantum record does not constrain acceptance by a query word.
This is a defect of that record, not a disproof of the Forrelation separation.
-/
set_option autoImplicit false
namespace Qatlib.Papers.Forrelation14.MainResults

/-- Any Boolean functional can be stored in the archived zero-query record. -/
def freeDecider {σ : Type} (P : (σ → Bool) → Bool) : Model.QuantumQueryAlgorithm σ 0 where
  accepts x := if P x then 1 else 0
  accepts_nonneg x := by split <;> norm_num
  accepts_le_one x := by split <;> norm_num

/-- The free record satisfies its success predicate with certainty for every input. -/
theorem freeSuccess {σ : Type} (P : (σ → Bool) → Bool) :
    (freeDecider P).SolvesBoundedError P (fun _ => True) (1 / 2) := by
  intro x _
  cases h : P x <;> norm_num [freeDecider, h]

/-- In particular its acceptance may distinguish the value of an unread input bit. -/
theorem unreadBit :
    (freeDecider (fun x : Unit → Bool => x ())).accepts (fun _ => true) ≠
      (freeDecider (fun x : Unit → Bool => x ())).accepts (fun _ => false) := by
  norm_num [freeDecider]

end Qatlib.Papers.Forrelation14.MainResults
