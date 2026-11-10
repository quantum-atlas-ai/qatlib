/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
import Mathlib.Data.Fintype.Perm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra

theorem antisym_state_count (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

theorem perm_ext_injective (n : ℕ) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) := by
  intro σ τ h
  exact Equiv.ext (fun x => congrFun h x)

theorem perm_range_bijective (n : ℕ) :
    Set.range (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n))
      = {f : Fin n → Fin n | Function.Bijective f} := by
  ext f
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, rfl⟩
    exact σ.bijective
  · intro hf
    exact ⟨Equiv.ofBijective f hf, rfl⟩

theorem antisym_step_costs (n q : ℕ) :
    antisymTotalCost n q = n * q ^ 2 + n ^ 2 * q + 2 * n * Nat.clog 2 n := rfl

theorem reverse_twice_identity {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : ReverseCircuit (ReverseCircuit C) = C :=
  reverse_involution C

theorem append_reverse_gate_cost {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : GateCount (C ++ ReverseCircuit C) = 2 * GateCount C := by
  rw [gateCount_append, gateCount_reverseCircuit]
  ring

theorem permutation_count_and_budget {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial ∧
      antisymTotalCost n q ≤ 4 * n ^ 2 * q ^ 2 :=
  ⟨antisym_state_count n, antisymTotalCost_bound hn hq⟩

end Qatlib.Papers.ManyBodyFermi97.MainResults
