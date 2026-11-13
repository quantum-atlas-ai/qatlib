/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Simulation.CircuitCalculus

/-!
# Finite chains of state transfers

This module proves reflexivity of `TransfersState` using the identity circuit and combines
successive transfers over a finite sequence. The theorem `transfersState_chain` supplies the
transfer from the first state to the last. The mathematical context is [AharonovTaShma2007].

## Main statements

* `TransfersState.refl`: Every state transfers to itself using the identity circuit.
* `transfersState_chain`: Transfers between consecutive states of a finite sequence compose to a
  transfer from its initial state to its final state.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Simulation

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- The identity circuit satisfies the polynomial-size predicate `PolySize`. -/
theorem polySize_circId (n : ℕ) : PolySize (circId n) := by
  refine ⟨0, 0, ?_⟩
  simp [circId]

/-- Every state transfers to itself using the identity circuit. -/
theorem TransfersState.refl (ψ : State n) : TransfersState ψ ψ := by
  intro ε hε
  exact ⟨circId n, polySize_circId n, by simp [circId, hε.le]⟩

/-- Transfers between consecutive states of a finite sequence compose to a transfer from its
initial state to its final state. -/
theorem transfersState_chain : ∀ {T : ℕ} (α : Fin (T + 1) → State n),
    (∀ t : Fin T, TransfersState (α (Fin.castSucc t)) (α (Fin.succ t))) →
    TransfersState (α 0) (α (Fin.last T))
  | 0, α, _ => by
      convert! TransfersState.refl (α 0) using 2
  | T + 1, α, h => by

      set β : Fin (T + 1) → State n := fun i => α (Fin.succ i) with hβ
      have hβstep : ∀ t : Fin T,
          TransfersState (β (Fin.castSucc t)) (β (Fin.succ t)) := by
        intro t
        have hthis := h (Fin.succ t)
        have h1 : Fin.castSucc (Fin.succ t) = Fin.succ (Fin.castSucc t) := by
          ext; simp
        simp only [hβ]
        rw [← h1]
        exact hthis
      have ih := transfersState_chain β hβstep
      have hfirst : TransfersState (α 0) (β 0) := by
        have := h 0
        simpa [hβ] using this
      have hs : Fin.succ (Fin.last T) = Fin.last (T + 1) := by ext; simp
      have hlast : β (Fin.last T) = α (Fin.last (T + 1)) := by
        simp only [hβ, hs]
      rw [hlast] at ih
      exact TransfersState.trans hfirst ih

end Qatlib.Papers.AdiabStateGen03.MainResults.Simulation
