/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxDegree20.MainResults.Definitions.QueryCost
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem3DegreeLeQueryCountSqDegr

@[expose] public section

/-!
# From per-circuit bounds to the optimal quantum query cost

Source: arXiv:2010.12629v1, Theorem 3 (page 3), `deg(f) = O(Q(f)²)` with the explicit
constant `(6 (3 + 2√2))²` of the per-circuit statement
`Qatlib.Concepts.QueryComplexity.DegreeBounds.theorem3DegreeLeQueryCountSq`.

`quantumQueryCost f` is the infimum of the query counts of bounded-error unitary circuits with
an arbitrary finite workspace that decide `f`
(`Qatlib.Papers.ApproxDegree20.MainResults.Definitions.quantumQueryCost`). The paper-level
statement then follows: a feasible query count `m` satisfies the per-circuit bound, and the
infimum itself is feasible by `Nat.sInf_mem` once the feasible set is nonempty.

Boundary: the unconditional form of the paper's Theorem 3 additionally needs a concrete
bounded-error circuit for an arbitrary Boolean function in the frozen fixed-word oracle model
(read every input coordinate into the workspace, then evaluate `f` classically). The frozen
library does not provide such a circuit, so `degree_le_sq_quantumQueryCost` below carries the
nonemptiness of the feasible set as an explicit hypothesis, and only
`degree_le_sq_of_mem_feasibleQueryCounts` is unconditional.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.ApproxDegree20.MainResults.Definitions
open Qatlib.Concepts.QueryComplexity.DegreeBounds
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Papers.ApproxDegree20.MainResults.OptimalQuery

/-- The set of query counts of bounded-error unitary circuits over a finite workspace that decide
`f` on every input; this is the index set of the infimum defining `quantumQueryCost`. -/
def feasibleQueryCounts {I : Type} [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool) :
    Set ℕ :=
  {m : ℕ | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W))
    (E : Finset ((I × Bool) × W)),
    IsUnitaryCircuit C ∧ Normalized ψ ∧
    (∀ g : I → Bool,
      2 / 3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) ∧
    QueryCount C = m}

/-- The optimal quantum query cost is the infimum of the feasible query counts. -/
theorem quantumQueryCost_eq_sInf {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) :
    quantumQueryCost f = sInf (feasibleQueryCounts f) := rfl

/-- A feasible query count obeys the per-circuit quadratic degree bound of Theorem 3. -/
theorem degree_le_sq_of_mem_feasibleQueryCounts {N : ℕ} (f : (Fin N → Bool) → Bool) {m : ℕ}
    (hm : m ∈ feasibleQueryCounts f) :
    (exactDegree f : ℝ)
      ≤ (6 * (3 + 2 * Real.sqrt 2)) ^ 2 * (m : ℝ) ^ 2 := by
  obtain ⟨W, hW, hWd, C, ψ, E, hC, hψ, hsucc, hq⟩ := hm
  have h := theorem3DegreeLeQueryCountSq N W C ψ E f hC hψ hsucc
  rw [hq] at h
  rwa [mul_pow] at h

/-- Theorem 3 in optimal form, given that some bounded-error circuit decides `f`: the exact
degree is at most `(6 (3 + 2√2))² Q(f)²`. -/
theorem degree_le_sq_quantumQueryCost {N : ℕ} (f : (Fin N → Bool) → Bool)
    (hne : (feasibleQueryCounts f).Nonempty) :
    (exactDegree f : ℝ)
      ≤ (6 * (3 + 2 * Real.sqrt 2)) ^ 2 * (quantumQueryCost f : ℝ) ^ 2 := by
  have hmem : quantumQueryCost f ∈ feasibleQueryCounts f := by
    rw [quantumQueryCost_eq_sInf]
    exact Nat.sInf_mem hne
  exact degree_le_sq_of_mem_feasibleQueryCounts f hmem

end Qatlib.Papers.ApproxDegree20.MainResults.OptimalQuery
