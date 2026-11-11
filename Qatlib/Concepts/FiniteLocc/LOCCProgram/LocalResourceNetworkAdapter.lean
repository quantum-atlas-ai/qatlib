/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetwork

/-!
# Dev-side typed adapter for the finite LOCC resource witness

This adapter gives the Frozen tensor-local resource construction a stable Dev
boundary. It exposes the inventory's exact gate price and normalized state
without claiming a general LOCC channel realization or communication capacity.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Qatlib
open Matrix
open scoped ComplexOrder
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs.EPRInventory

/-- A typed Dev handle for a finite inventory of shared EPR resources. -/
structure EPRResourceHandle where
  inventory : EPRInventory

/-- The exact factory gate price carried by a Dev handle. -/
theorem EPRResourceHandle.gate_price (h : EPRResourceHandle) :
    h.inventory.gateCost = 2 * h.inventory.slots := by
  exact EPRInventory.gateCost_eq h.inventory

/-- Every shared-EPR inventory has an even gate count. -/
theorem EPRResourceHandle.gate_price_even (h : EPRResourceHandle) :
    Even h.inventory.gateCost := by
  rw [h.gate_price]
  exact ⟨h.inventory.slots, by simp [two_mul]⟩

/-- The gate ledger is at least the number of allocated EPR slots. -/
theorem EPRResourceHandle.slots_le_gate_price (h : EPRResourceHandle) :
    h.inventory.slots ≤ h.inventory.gateCost := by
  rw [h.gate_price]
  omega

/-- The local action selected by a Dev handle acts on one concrete EPR slot. -/
noncomputable def EPRResourceHandle.slot_action (h : EPRResourceHandle)
    (j : Fin h.inventory.slots)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin h.inventory.slots → (Fin 2 × Fin 2))
      (Fin h.inventory.slots → (Fin 2 × Fin 2)) ℂ :=
  slotAction h.inventory.slots j A

/-- Consuming a handle slot transforms that slot and leaves every other factor
unchanged, with the inventory state carried by the handle itself. -/
theorem EPRResourceHandle.slot_consumption (h : EPRResourceHandle)
    (j : Fin h.inventory.slots)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    h.slot_action j A * h.inventory.state * (h.slot_action j A)ᴴ =
      productMatrix (fun j' =>
        if j' = j then A * eprFactor * Aᴴ else eprFactor) := by
  simpa [EPRResourceHandle.slot_action, EPRInventory.state] using
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs.slot_consumption
      h.inventory.slots j A)

/-- The inventory state attached to a Dev handle is positive and normalized. -/
theorem EPRResourceHandle.state_is_density (h : EPRResourceHandle) :
    h.inventory.state.PosSemidef ∧ Matrix.trace h.inventory.state = 1 :=
  And.intro h.inventory.state_psd h.inventory.state_trace

end Qatlib.Concepts.FiniteLocc.LOCCProgram
