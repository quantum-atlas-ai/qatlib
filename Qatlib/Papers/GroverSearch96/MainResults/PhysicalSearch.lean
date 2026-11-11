/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.ObservedSearchLowerBoundAfas
import Qatlib.Concepts.SearchStopping.KnownCount.ObservedDecisionLowerBoundAfas
import Mathlib.Tactic
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchConsumers

/-!
# Physical query bounds for singleton search

This module gives lower bounds for well formed observed circuits with workspace bit oracles,
covering both decoded singleton search and the decision problem of distinguishing a singleton
oracle from the null oracle.

`physical_matching_search` compares a successful unitary search circuit with the workspace
Grover circuit on the same oracle model. `physical_search_constant_factor` turns the bounds into
an explicit query count comparison. See [Grover1996].

## Main statements

* `physical_search_sqrt_lower`: For `n ≥ 2`, a well formed observed circuit with normalized
  input that finds every singleton target with probability at least `2/3` has query depth at
  least `sqrt n / 8`.
* `physical_decision_sqrt_lower`: A well formed observed circuit with normalized input, null
  acceptance at most `1/3`, and singleton acceptance at least `2/3` has query depth at least
  `sqrt n / 12`.
* `physical_search_constant_factor`: For `n ≥ 3`, the workspace Grover circuit uses at most
  `2*π` times the queries of any normalized unitary singleton search circuit succeeding with
  probability at least `2/3` for every target.

## References

* [Grover, 1996][Grover1996]
-/

set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
namespace Qatlib.Papers.GroverSearch96.MainResults

/-- For `n ≥ 2`, a well formed observed circuit with normalized input that finds every singleton
target with probability at least `2/3` has query depth at least `sqrt n / 8`. See
[Grover1996]. -/
theorem physical_search_sqrt_lower (n : ℕ) (W : Type)
    [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W))
    (decode : ℕ → ((Fin n × Bool) × W) → Option (Fin n))
    (hn : 2 ≤ n) (hP : observedWellFormed P) (hψ : Normalized ψ)
    (hs : ∀ w : Fin n, (2/3:ℝ) ≤ observedDecodedMass
      (workspaceBitOracle (W := W) (fun z => decide (z=w))) P ψ decode (some w)) :
    Real.sqrt (n:ℝ)/8 ≤ (observedQueryDepth P:ℝ) := by
  have hb := (observedSearchLowerBound n W P ψ decode hP hψ hs).2 hn
  have hsq : (Real.sqrt (n:ℝ))^2 ≤ (8*(observedQueryDepth P:ℝ))^2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith
  have hl := (sq_le_sq₀ (Real.sqrt_nonneg (n:ℝ)) (by positivity)).mp hsq
  linarith

/-- A well formed observed circuit with normalized input, null acceptance at most `1/3`, and
singleton acceptance at least `2/3` has query depth at least `sqrt n / 12`. See
[Grover1996]. -/
theorem physical_decision_sqrt_lower (n : ℕ) (W : Type)
    [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W))
    (hP : observedWellFormed P) (hψ : Normalized ψ)
    (hnull : observedAcceptance (workspaceBitOracle (W := W) (fun _ => false)) P ψ ≤ 1/3)
    (hs : ∀ w : Fin n, (2/3:ℝ) ≤ observedAcceptance
      (workspaceBitOracle (W := W) (fun z => decide (z=w))) P ψ) :
    Real.sqrt (n:ℝ)/12 ≤ (observedQueryDepth P:ℝ) := by
  have hb := observedDecisionLowerBound n W P ψ hP hψ hnull hs
  have hsq : (Real.sqrt (n:ℝ))^2 ≤ (12*(observedQueryDepth P:ℝ))^2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith
  have hl := (sq_le_sq₀ (Real.sqrt_nonneg (n:ℝ)) (by positivity)).mp hsq
  linarith

/-- For `n ≥ 3`, any normalized unitary singleton search circuit succeeding with probability at
least `2/3` uses at least `sqrt (card (Reg n)) / 8` queries, while the workspace Grover
circuit succeeds with that probability using at most `(π/4) * sqrt (card (Reg n))` queries.
See [Grover1996]. -/
theorem physical_matching_search {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (C : Circuit ((Reg n × Bool) × W))
    (ψ : QState ((Reg n × Bool) × W))
    (decode : ((Reg n × Bool) × W) → Option (Reg n))
    (hn : 3 ≤ n) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hmark : ∀ x : Reg n, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x))) C ψ)
      (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    Real.sqrt (Fintype.card (Reg n) : ℝ) / 8 ≤ (QueryCount C : ℝ) ∧
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) ≤
      Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 ∧
    (∀ x : Reg n, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
        (Ket ((ZeroStr n, false), w)))
      (Finset.univ.filter (fun p => (some p.1.1 : Option (Reg n)) = some x)) ≥ 2 / 3) := by
  obtain ⟨hlo, hup, hs⟩ := workspace_search_matching_actual_consumer n w C ψ decode hn hC hψ hmark
  refine ⟨?_, hup, hs⟩
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Reg n)) : (0 : ℝ) ≤ _)
  have hq : (0 : ℝ) ≤ QueryCount C := Nat.cast_nonneg _
  have hroot := Real.sqrt_nonneg (Fintype.card (Reg n) : ℝ)
  nlinarith

/-- For `n ≥ 3`, the workspace Grover circuit uses at most `2*π` times the queries of any
normalized unitary singleton search circuit succeeding with probability at least `2/3` for
every target. See [Grover1996]. -/
theorem physical_search_constant_factor {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (C : Circuit ((Reg n × Bool) × W))
    (ψ : QState ((Reg n × Bool) × W))
    (decode : ((Reg n × Bool) × W) → Option (Reg n))
    (hn : 3 ≤ n) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hmark : ∀ x : Reg n, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x))) C ψ)
      (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) ≤
      (2 * Real.pi) * (QueryCount C : ℝ) := by
  obtain ⟨hlower,hupper,_⟩ := physical_matching_search n w C ψ decode hn hC hψ hmark
  have hroot : Real.sqrt (Fintype.card (Reg n) : ℝ) ≤ 8 * (QueryCount C : ℝ) := by
    linarith
  nlinarith [Real.pi_pos]

end Qatlib.Papers.GroverSearch96.MainResults
