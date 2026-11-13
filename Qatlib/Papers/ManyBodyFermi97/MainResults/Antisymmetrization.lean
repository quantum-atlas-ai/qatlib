/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
import Mathlib.Data.Fintype.Perm

/-!
# Permutation counts and antisymmetrization budgets

This module proves counting and cost identities for the antisymmetrization resource model in
[AbramsLloyd1997]. The n-particle permutation index has n! elements, and its image as functions
consists exactly of bijections.

The results unfold `antisymTotalCost`, bound it by 4n²q² for positive parameters, and show that
appending a reversed circuit doubles its gate count.

## Main statements

* `antisym_state_count`: The permutation index has n! elements.
* `append_reverse_gate_cost`: A circuit followed by its reverse has twice the gate count.
* `permutation_count_and_budget`: Permutation counting and the quadratic budget bound.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra

/-- There are n! permutations of `Fin n`. -/
theorem antisym_state_count (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- Viewing permutations of `Fin n` as functions is injective. -/
theorem perm_ext_injective (n : ℕ) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) := by
  intro σ τ h
  exact Equiv.ext (fun x => congrFun h x)

/-- The range of permutations viewed as functions is exactly the set of bijective functions on
`Fin n`. -/
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

/-- The antisymmetrization cost model is nq² + n²q + 2n ceil(log₂ n). -/
theorem antisym_step_costs (n q : ℕ) :
    antisymTotalCost n q = n * q ^ 2 + n ^ 2 * q + 2 * n * Nat.clog 2 n := rfl

/-- Reversing a circuit twice returns the original circuit. -/
theorem reverse_twice_identity {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : ReverseCircuit (ReverseCircuit C) = C :=
  reverse_involution C

/-- Appending the reverse of a circuit doubles its gate count. -/
theorem append_reverse_gate_cost {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : GateCount (C ++ ReverseCircuit C) = 2 * GateCount C := by
  rw [gateCount_append, gateCount_reverseCircuit]
  ring

/-- For n, q ≥ 1, the permutation index has n! elements and the antisymmetrization cost model is
at most 4n²q². -/
theorem permutation_count_and_budget {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial ∧
      antisymTotalCost n q ≤ 4 * n ^ 2 * q ^ 2 :=
  ⟨antisym_state_count n, antisymTotalCost_bound hn hq⟩

end Qatlib.Papers.ManyBodyFermi97.MainResults
