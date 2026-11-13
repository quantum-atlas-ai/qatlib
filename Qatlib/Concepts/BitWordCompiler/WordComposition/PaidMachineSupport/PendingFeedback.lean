/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.FeedbackMachine

/-!
# Pending controller variables and feedback banks

`Variable` names controller labels, environment bits, failure flags, acceptance, and success.
The injective map `address` assigns each variable a slot in a finite optional-Boolean `Bank`.

`packed` serializes the bank and `supply` updates a pending variable. The feedback execution
theorems realize this update using the clocked writer, with all index workspace cleared.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `address_injective`: distinct controller variables occupy distinct bank slots.
* `pending_feedback_execution_bounded`: writes a pending value with a uniform bank-size clock
  bound.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.ControllerFeedback
set_option autoImplicit false
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.FeedbackWrite

/-- The feedback writer's stack-slot type. -/
abbrev Slot := FeedbackWrite.Slot
/-- The feedback writer's control-label type. -/
abbrev Label := FeedbackWrite.Label
/-- The feedback writer's local-state type. -/
abbrev Local := FeedbackWrite.Local
/-- The feedback writer's stack-machine program. -/
abbrev program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local := FeedbackWrite.program
/-- The feedback writer's store constructor for bank, saved prefix, index, and temporary data. -/
abbrev store (bank saved index temporary : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  FeedbackWrite.store bank saved index temporary
/-- The feedback writer's final local state retaining the feedback bit. -/
abbrev done (feedback : Bool) : Local := FeedbackWrite.done feedback
/-- The two-bit-per-slot encoding of an optional-Boolean bank. -/
abbrev bankBits (slots : List (Option Bool)) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := FeedbackWrite.bankBits slots

/-- The encoded bank length is twice its slot count. -/
@[simp] theorem bankBits_length (slots : List (Option Bool)) :
    (bankBits slots).length = 2 * slots.length := FeedbackWrite.bankBits_length slots

/-- Controller variables comprising label bits, three environment bits, failure bits,
acceptance, and success. -/
inductive Variable (q : ℕ) where
  | label (i : Fin q)
  | environment (i : Fin 3)
  | failed (i : Fin q)
  | accepted
  | success
  deriving DecidableEq, Fintype

/-- Assigns disjoint finite bank addresses to the controller-variable constructors. -/
def address {q : ℕ} : Variable q → Fin (2*q+5)
  | .label i => ⟨i,by omega⟩
  | .environment i => ⟨q+i,by omega⟩
  | .failed i => ⟨q+3+i,by omega⟩
  | .accepted => ⟨2*q+3,by omega⟩
  | .success => ⟨2*q+4,by omega⟩

/-- Distinct controller variables have distinct bank addresses. -/
theorem address_injective (q : ℕ) : Function.Injective (@address q) := by
  intro a b h
  have hv := congrArg Fin.val h
  cases a <;> cases b <;> simp_all [address, Fin.ext_iff] <;> omega

/-- A finite bank of `2 * q + 5` optional Boolean entries. -/
abbrev Bank (q : ℕ) := Fin (2*q+5) → Option Bool

/-- Encodes the finite bank in address order using two bits per slot. -/
def packed {q : ℕ} (bank : Bank q) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    bankBits (List.ofFn bank)
/-- Sets the pending variable's bank entry to the supplied Boolean value. -/
def supply {q : ℕ} (bank : Bank q) (pending : Variable q) (feedback : Bool) : Bank q :=
  Function.update bank (address pending) (some feedback)

/-- Supplying feedback sets the pending address to that value. -/
@[simp] theorem supplied_pending {q : ℕ} (bank : Bank q) (pending : Variable q) (b : Bool) :
    supply bank pending b (address pending) = some b := by simp [supply]

/-- Supplying feedback preserves the entry of every distinct controller variable. -/
theorem supplied_other {q : ℕ} (bank : Bank q) (pending other : Variable q) (b : Bool)
    (h : other ≠ pending) : supply bank pending b (address other) = bank (address other) := by
  apply Function.update_of_ne
  exact fun he => h (address_injective q he)

/-- A packed bank has length `2 * (2 * q + 5)`. -/
@[simp] theorem packed_length {q : ℕ} (bank : Bank q) : (packed bank).length = 2*(2*q+5) := by
  simp only [packed, bankBits_length, List.length_ofFn]

/-- Enumerating a bank after an entry update equals setting that entry in its enumerated list. -/
private theorem ofFn_update {V : ℕ} (bank : Fin V → Option Bool) (i : Fin V) (b : Bool) :
    List.ofFn (Function.update bank i (some b)) = (List.ofFn bank).set i (some b) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn, List.getElem_set]
    split_ifs with h
    · subst j
      simp
    · have hn : (⟨j,by simpa using hj⟩ : Fin V) ≠ i := by
        intro he
        exact h (congrArg Fin.val he).symm
      simp [Function.update_of_ne hn]

/-- The feedback writer changes the pending entry to the supplied value and clears workspace
within an address-dependent clock bound. -/
theorem pending_feedback_execution {q : ℕ} (bank : Bank q) (pending : Variable q) (b : Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.counter .borrow),(b,(false,none),none),
        store (packed bank) [] (address pending).val.bits []⟩
      ⟨none,done b,store (packed (supply bank pending b)) [] [] []⟩
      (100*((address pending).val+1)*
        (1+2*(2*q+5)+(address pending).val.bits.length)^2) := by
  let slots := List.ofFn bank
  let i := address pending
  have hi : i.val < slots.length := by simpa only [slots, List.length_ofFn] using i.isLt
  have ht : (slots.take i.val).length = i.val := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hs : slots.take i.val ++ slots[i.val] :: slots.drop (i.val+1) = slots := by
    rw [← List.drop_eq_getElem_cons hi]
    exact List.take_append_drop _ _
  have hu : List.ofFn (supply bank pending b) = slots.take i.val ++ some b :: slots.drop (i.val+1) := by
    rw [supply, ofFn_update, List.set_eq_take_append_cons_drop, if_pos hi]
  have he := feedback_machine_execution (slots.take i.val) slots[i.val] (slots.drop (i.val+1))
    [] i.val.bits (b,(false,none),none) (by rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits, ht])
  rw [hs, ← hu, ht] at he
  simpa only [slots, i, packed, bankBits_length, List.length_ofFn, List.length_nil,
    Nat.add_zero, List.reverse_nil, List.nil_append] using he

/-- The feedback writer changes the pending entry and clears workspace within a clock bound
using the total bank size and address-encoding length. -/
theorem pending_feedback_execution_bounded {q : ℕ} (bank : Bank q) (pending : Variable q) (b : Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.counter .borrow),(b,(false,none),none),
        store (packed bank) [] (address pending).val.bits []⟩
      ⟨none,done b,store (packed (supply bank pending b)) [] [] []⟩
      (100*(2*q+5)*(1+2*(2*q+5)+(address pending).val.bits.length)^2) := by
  apply (pending_feedback_execution bank pending b).mono
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  exact (address pending).isLt

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.ControllerFeedback
