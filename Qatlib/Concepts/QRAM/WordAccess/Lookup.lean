/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.TableAccess.ReversibleTable
public import Init.Data.BitVec.Lemmas
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Coherent lookup in classically writable memory

A classical write replaces a fixed-width word at a chosen address. For a fixed memory
snapshot, a read XORs the word at the address into a target register. With a zero target this
is the read in [ChenXueChenEtAl2022], Appendix D. The read applies to arbitrary amplitudes
and admits exact uncomputation. Its matrix semantics are independent of the access time
and of any physical arrangement of the memory.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QRAM.WordAccess

open Matrix
open Qatlib.Foundations.TableAccess.ReversibleTable

/-- A fixed-width word can be enumerated by its unsigned finite index. -/
instance instFintypeBitVec (width : ℕ) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩

variable {Address : Type*} {width : ℕ}

/-- Replace one word in a classical memory snapshot. -/
def write {Word : Type*} [DecidableEq Address] (memory : Address → Word)
    (address : Address) (word : Word) : Address → Word :=
  Function.update memory address word

/-- A read leaves the address intact and XORs the addressed memory word into the target. -/
def queryAction (memory : Address → BitVec width) (input : Address × BitVec width) :
    Address × BitVec width :=
  (input.1, input.2 ^^^ memory input.1)

/-- A second read with the same snapshot undoes the first read on registers. -/
theorem query_action_involutive (memory : Address → BitVec width) :
    Function.Involutive (queryAction memory) := by
  intro input
  simp [queryAction, BitVec.xor_assoc]

variable [Fintype Address] [DecidableEq Address]

/-- The linear extension of the reversible addressed read. -/
noncomputable def query (memory : Address → BitVec width) :
    Matrix (Address × BitVec width) (Address × BitVec width) ℂ :=
  permMatrix (queryAction memory)

/-- Coherent read is unitary for every memory snapshot. -/
theorem query_unitary (memory : Address → BitVec width) :
    query memory ∈ Matrix.unitaryGroup (Address × BitVec width) ℂ :=
  permMatrix_unitary (query_action_involutive memory)

/-- A second coherent read with the same snapshot uncomputes the target. -/
theorem query_mul_self (memory : Address → BitVec width) :
    query memory * query memory = 1 :=
  permMatrix_mul_self (query_action_involutive memory)

/-- Coherent lookup acts on all address and target amplitudes by the XOR permutation. -/
theorem query_mulVec (memory : Address → BitVec width) (ψ : Address × BitVec width → ℂ)
    (address : Address) (target : BitVec width) :
    (query memory *ᵥ ψ) (address, target) = ψ (address, target ^^^ memory address) :=
  applyGate_permMatrix (query_action_involutive memory) ψ (address, target)

/-- Reading a clean target after a classical write produces the overwritten word at
the selected address and the original word at every other address. -/
theorem query_after_write (memory : Address → BitVec width) (selected address : Address)
    (word : BitVec width) :
    query (write memory selected word) *ᵥ Ket (address, 0) =
      Ket (address, if address = selected then word else memory address) := by
  rw [query, applyGate_permMatrix_ket (query_action_involutive _)]
  simp [queryAction, write, Function.update_apply]

end Qatlib.Concepts.QRAM.WordAccess
