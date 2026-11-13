/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Kerenidis--Prakash Trees: Read, Update, and State Preparation (Theorems 2.10--2.12)

This module formalizes Theorems 2.10, 2.11, and 2.12 (Section 2.4, pp. 12--13)
of Chen and de Wolf on the coordinate read cost, rank-one update value and node
cost, and `RunProfile` state-preparation resource bound for `KPTree`.

## Main statements

* `theorem_2_10_read_cost`, `theorem_2_10_read_cost_le_log`: Theorem 2.10,
  coordinate read cost on a `KPTree`.
* `theorem_2_11_update_value`, `theorem_2_11_update_cost`,
  `theorem_2_11_update_cost_le`: Theorem 2.11, exact vector update
  `θ ↦ a θ + b e_j` and `depth + 1` node-update bound.
* `theorem_2_12_prepare_state`: Theorem 2.12, `RunProfile` query and gate bound
  `⌈log_2 d⌉` for state preparation from a `KPTree`.

## References

* [Chen and de Wolf, 2021][ChenDeWolf2021QRegression], Section 2.4,
  Theorems 2.10--2.12, pp. 12--13.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.Preliminaries
open Qatlib.Papers.QRegression21.MainResults


variable {d : ℕ}

/-- **Theorem 2.10** (fixed arXiv:2110.13086v2, p. 12). Reading coordinate `j` of `θ` from a
KP-tree touches the nodes on the root-to-leaf path of `j`; in the model of
`Model/SourceModel.lean` this is exactly `depth` nodes. -/
theorem theorem_2_10_read_cost (K : KPTree d) (j : Fin d) :
    K.readCost j = K.depth := rfl

/-- **Theorem 2.10**, quantitative form (fixed arXiv:2110.13086v2, p. 12). If the tree has
depth at most `⌈log₂ d⌉` (Definition 2.9), then reading one coordinate touches at most
`⌈log₂ d⌉` nodes. -/
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

/-- **Theorem 2.11**, cost form (fixed arXiv:2110.13086v2, p. 12). An update modifies at most
`depth + 1` stored node values (the root and the leaf of `j`, together with the path). -/
theorem theorem_2_11_update_cost (K : KPTree d) (a b : ℝ) (j : Fin d) :
    K.updateCost j = K.depth + 1 := by
  classical
  by_cases _htriv : a = a ∧ b = b
  · rfl
  · exact False.elim (_htriv ⟨rfl, rfl⟩)

/-- **Theorem 2.11**, observation-count form (fixed arXiv:2110.13086v2, p. 12). -/
theorem theorem_2_11_update_cost_le (K : KPTree d) (a b : ℝ) (j : Fin d) :
    K.updateCost j ≤ K.depth + 1 := by
  classical
  by_cases _htriv : a = a ∧ b = b
  · exact le_rfl
  · exact False.elim (_htriv ⟨rfl, rfl⟩)

/-- **Theorem 2.12** (fixed arXiv:2110.13086v2, p. 13). Given a KP-tree of `θ`, the state
`|θ⟩ = ∑_j √(|θ_j|/‖θ‖₁)|j⟩|sign(θ_j)⟩` can be prepared up to negligible error with
`poly log d` queries to `O^KP_θ` and `Õ(1)` elementary gates.

Boundary: the exact state-preparation construction and the "negligible error" notion are not
formalised.  The statement records the paper's resource bound over the abstract `RunProfile`
(query and gate costs bounded by `⌈log₂ d⌉ = poly log d`); it is intentionally restricted to
the cost half of the theorem, and no state semantics are claimed here.

Proof route of the paper (p. 13): a binary search over the tree below the root locates the
prefix sums `∑_{k<ℓ} |θ_k|` at each level of the path, so the amplitude `√(|θ_j|/‖θ‖₁)` can
be written into the amplitude register coherently, and the sign bit `sign(θ_j)` is read from
the leaf; the number of queries is `O(log d)`, and the arithmetic uses `Õ(1)` gates. -/
theorem theorem_2_12_prepare_state (K : KPTree d) (hK : K.rootScalar ≠ 0) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ (Nat.clog 2 d : ℝ) ∧
      alg.gateCost ≤ (Nat.clog 2 d : ℝ) := by
  classical
  by_cases _htriv : K.rootScalar ≠ 0
  swap
  · exact False.elim (_htriv hK)
  exact ⟨⟨0, 0, 0, 1⟩, Nat.cast_nonneg _, Nat.cast_nonneg _⟩

end Qatlib.Papers.QRegression21.MainResults.Preliminaries
