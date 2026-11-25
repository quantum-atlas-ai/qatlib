/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HybridQuery26.QueryModel.ClassificationLowerBound
public import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds

@[expose] public section

/-!
# Combined hybrid-query lower bounds

Combine the transcript and uninterrupted-query estimates used in the proofs
of Theorems 1 and 2 of arXiv:2610.06803v1, keeping a single query budget.
-/

set_option autoImplicit false

open Matrix
open Qatlib.Papers.HybridQuery26.QueryModel
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.HybridQuery26.QueryModel

/-- Theorem 1 combines the weighted transcript and whole-run distance estimates with
the same worst-case budget `L`. -/
theorem hybrid_classification_two_term_lower_bound {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) {q ε L : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ r i) (hrq : ∀ i, r i ≤ q)
    (hcost : ∑ i, w i * r i ≤ L) (hprogress : 1 / 9 ≤ ∑ i, w i * (r i * ε) ^ 2)
    (hdistance : 1 / 3 ≤ L * ε) :
    (1 / 12 : ℝ) * (1 / ε + 1 / (q * ε ^ 2)) ≤ L := by
  have h1 := unrestricted_query_lower_bound hε hdistance
  have h2 := classification_query_lower_bound w r hq hε hw hr hrq hcost hprogress
  have h1' : 1 / ε = 3 * (1 / (3 * ε)) := by field_simp [hε.ne']
  have h2' : 1 / (q * ε ^ 2) = 9 * (1 / (9 * q * ε ^ 2)) := by
    field_simp [hq.ne', hε.ne']
  rw [h1', h2']
  linarith

/-- Theorem 2 combines an uninterrupted search bound with the hybrid transcript drop.
The nonnegativity of the uninterrupted query count is needed to take a square root. -/
theorem search_two_term_lower_bound {N q L Q : ℝ} (hq : 0 < q) (hN : 0 ≤ N)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ L) (hNQ : N ≤ 144 * Q ^ 2)
    (hdrop : N / 9 ≤ 8 * q * L) :
    (1 / 84 : ℝ) * (Real.sqrt N + N / q) ≤ L := by
  have hsqrt : Real.sqrt N ≤ 12 * Q := (Real.sqrt_le_iff).mpr
    ⟨by positivity, by nlinarith only [hNQ]⟩
  have hhybrid := search_query_lower_bound hq hN hdrop
  have heq : N / q = 72 * (N / (72 * q)) := by field_simp [hq.ne']
  rw [heq]
  linarith

/-- On an actual normalized workspace circuit with query count bounded by the same
transcript budget, the unrestricted part follows from its null/singleton decision gap. -/
theorem workspace_search_two_term_lower_bound {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (E : Finset ((I × Bool) × W)) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hnull : MeasureProb (Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) E ≤ 1 / 3)
    (hmark : ∀ x : I, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ) E ≥ 2 / 3)
    {q L : ℝ} (hq : 0 < q) (hcost : (QueryCount C : ℝ) ≤ L)
    (hdrop : (Fintype.card I : ℝ) / 9 ≤ 8 * q * L) :
    (1 / 84 : ℝ) * (Real.sqrt (Fintype.card I : ℝ) + (Fintype.card I : ℝ) / q) ≤ L :=
  search_two_term_lower_bound hq (by positivity) (by positivity) hcost
    (workspace_decision_query_lower_bound C ψ E hC hψ hnull hmark) hdrop

end Qatlib.Papers.HybridQuery26.QueryModel
