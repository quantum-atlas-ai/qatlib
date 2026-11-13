/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceKPTree

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
The remaining theorems prove only their displayed algebraic inequalities or identities.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.Preliminaries
open Qatlib.Papers.QRegression21.MainResults

variable {d : ℕ}

/-- The assigned read budget equals the stored depth by definition.
This does not count a tree traversal. -/
theorem theorem_2_10_read_cost (K : KPTree d) (j : Fin d) :
    K.readCost j = K.depth := rfl

/-- A supplied depth bound transfers to the assigned read budget.
This does not count a tree traversal. -/
theorem theorem_2_10_read_cost_le_log (K : KPTree d) (j : Fin d)
    (hd : K.depth ≤ Nat.clog 2 d) :
    K.readCost j ≤ Nat.clog 2 d := by
  rw [theorem_2_10_read_cost]
  exact hd

/-- **Theorem 2.11** (fixed arXiv:2110.13086v2, p. 12). One update step of a KP-tree
transforms the represented vector `θ` into `a·θ + b·e_j`, i.e.
`(update K a b j).theta k = a * K.theta k + (if k = j then b else 0)`, for `a ≠ 0` and a
nonzero root scalar. -/
theorem theorem_2_11_update_value (K : KPTree d) (a b : ℝ) (j : Fin d)
    (ha : a ≠ 0) (hA : K.rootScalar ≠ 0) :
    (K.update a b j).theta = fun k => a * K.theta k + (if k = j then b else 0) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp only [KPTree.theta, KPTree.update, ↓reduceIte]
    have h : a * K.rootScalar ≠ 0 := mul_ne_zero ha hA
    field_simp [h]
  · simp only [KPTree.theta, KPTree.update, hk, ↓reduceIte]
    ring

/-- The assigned update budget equals depth plus one by definition.
This does not count a tree traversal. -/
theorem theorem_2_11_update_cost (K : KPTree d) (a b : ℝ) (j : Fin d) :
    K.updateCost j = K.depth + 1 := by
  classical
  by_cases _htriv : a = a ∧ b = b
  · rfl
  · exact False.elim (_htriv ⟨rfl, rfl⟩)

/-- Reflexive bound on the assigned update budget.
This does not count a tree traversal. -/
theorem theorem_2_11_update_cost_le (K : KPTree d) (a b : ℝ) (j : Fin d) :
    K.updateCost j ≤ K.depth + 1 := by
  classical
  by_cases _htriv : a = a ∧ b = b
  · exact le_rfl
  · exact False.elim (_htriv ⟨rfl, rfl⟩)

/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem_2_12_prepare_state`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem_2_12_prepare_state_statement (K : KPTree d) (hK : K.rootScalar ≠ 0)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ (Nat.clog 2 d : ℝ) ∧
      alg.gateCost ≤ (Nat.clog 2 d : ℝ)

end Qatlib.Papers.QRegression21.MainResults.Preliminaries
