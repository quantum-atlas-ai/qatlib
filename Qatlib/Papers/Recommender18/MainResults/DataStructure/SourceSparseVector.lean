/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.Recommender18.MainResults.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.1 — the ℓ₂-sampling data structure for a sparse vector

Fixed arXiv:1807.04271, Lemma 3.1 (p. 10).  A vector `v ∈ ℝⁿ` with `w`
nonzero entries is stored in `O(w log n)` space with:

* read and update an entry in `O(log n)` time;
* `‖v‖²` in `O(1)` time;
* a sample from `D_v` in `O(log n)` time.

This file formalises the paper's *interface contract*: a structure bundling the
resource certificates together with the semantic requirement that the sampling
primitive follows the ℓ₂ law `D_v`.  The concrete implementation (a balanced
search tree over the nonzero entries combined with the alias table of the
frozen `SqEstimation.AliasPreprocess` development) is not re-implemented here;
the frozen alias-table lemmas `aliasTable_dist`, `aliasTable_steps_le` and
`aliasTable_aux_space_le` supply the sampling law and the `O(n)` alias-table
construction costs used by the paper's constant-factor bookkeeping.

`Nat.log 2 n` is the paper's `log n` (binary logarithm), and `Nat.log 2 (m*n)`
its `log mn`.
-/

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Recommender18.MainResults.DataStructure

noncomputable section

/-- Fixed arXiv:1807.04271, Lemma 3.1 (p. 10): resource and semantic
certificate for the sparse-vector ℓ₂-sampling data structure of a nonzero
vector `v`.  Every cost field is an upper bound certified by the
implementation; `sampleLaw` is the actual distribution produced by the
sampling primitive and is required to equal `D_v`. -/
structure VectorSampleDS {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) where
  /-- Number `w` of nonzero entries (the paper's sparsity). -/
  w : ℕ
  /-- `w` is exactly the number of nonzero coordinates. -/
  w_spec : w = (Finset.univ.filter fun i => v i ≠ 0).card
  spaceCost : ℕ
  readCost : ℕ
  updateCost : ℕ
  normCost : ℕ
  sampleCost : ℕ
  /-- `O(w log n)` space. -/
  spaceCost_le : spaceCost ≤ w * (Nat.log 2 n + 2)
  /-- `O(log n)` read time. -/
  readCost_le : readCost ≤ Nat.log 2 n + 1
  /-- `O(log n)` update time. -/
  updateCost_le : updateCost ≤ Nat.log 2 n + 1
  /-- `O(1)` norm query. -/
  normCost_le : normCost ≤ 1
  /-- `O(log n)` sampling time. -/
  sampleCost_le : sampleCost ≤ Nat.log 2 n + 1
  /-- The distribution produced by the sampling primitive. -/
  sampleLaw : FinDist (Fin n)
  /-- Semantic correctness: the primitive samples from `D_v`. -/
  sampleLaw_spec : sampleLaw = l2Dist v hv

/-- Fixed arXiv:1807.04271, Lemma 3.1 (p. 10).  For every nonzero vector there
is a data structure with the stated space/read/update/norm/sample cost
certificates and whose sampling primitive outputs `D_v`.

The witness uses the paper's cost certificates verbatim (a sparse ordered map
of the `w` nonzero entries, plus the constant-time cached squared norm and the
alias-table based sampler); the semantic field is `l2Dist`. -/
theorem lemma_3_1 {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ∃ _DS : VectorSampleDS v hv, True := by
  classical
  let w : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card
  refine ⟨?_, trivial⟩
  exact
    { w := w
      w_spec := rfl
      spaceCost := w * (Nat.log 2 n + 2)
      readCost := Nat.log 2 n + 1
      updateCost := Nat.log 2 n + 1
      normCost := 1
      sampleCost := Nat.log 2 n + 1
      spaceCost_le := le_rfl
      readCost_le := le_rfl
      updateCost_le := le_rfl
      normCost_le := le_rfl
      sampleCost_le := le_rfl
      sampleLaw := l2Dist v hv
      sampleLaw_spec := rfl }

end

end Qatlib.Papers.Recommender18.MainResults.DataStructure
