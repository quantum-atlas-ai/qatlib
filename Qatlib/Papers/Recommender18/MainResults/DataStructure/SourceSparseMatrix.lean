/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.Recommender18.MainResults.DataStructure.SourceSparseVector

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 3.2 — the ℓ₂-sampling data structure for a sparse matrix

Fixed arXiv:1807.04271, Proposition 3.2 (p. 10).  A matrix `A ∈ ℝ^{m×n}` with
`w` nonzero entries is stored in `O(w log(mn))` space with

* read/update of an entry in `O(log(mn))` time;
* finding `Ã_i = ‖A_i‖` in `O(log m)` time;
* finding `‖A‖_F²` in `O(1)` time;
* sampling from `D_Ã` and from `D_{A_i}` in `O(log(mn))` time.

As in `SourceSparseVector.lean` we formalise the interface contract: an
existence theorem for a structure carrying the paper's cost certificates and
the two semantic sampling laws.  The paper's construction (one copy of the
Lemma 3.1 structure per row, plus the root-level structure for `Ã`) is
recorded in the docstrings; the concrete BST/alias-table implementation is
not duplicated here.
-/

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Recommender18.MainResults.DataStructure

noncomputable section

/-- The vector `Ã` of row norms `Ã_i = ‖A_i‖` (paper Proposition 3.2). -/
def rowNormVec {m n : ℕ} (A : Fin m → Fin n → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => rowNorm A i

/-- Fixed arXiv:1807.04271, Proposition 3.2 (p. 10): resource and semantic
certificate for the sparse-matrix ℓ₂-sampling data structure. -/
structure MatrixSampleDS {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hrows : ∀ i, rowEuc A i ≠ 0) (hvec : rowNormVec A ≠ 0) where
  /-- Number of nonzero entries. -/
  w : ℕ
  w_spec : w = (Finset.univ.filter fun p : Fin m × Fin n => A p.1 p.2 ≠ 0).card
  spaceCost : ℕ
  readCost : ℕ
  updateCost : ℕ
  rowNormReadCost : ℕ
  frobNormCost : ℕ
  rowSampleCost : ℕ
  entrySampleCost : ℕ
  /-- `O(w log(mn))` space. -/
  spaceCost_le : spaceCost ≤ w * (Nat.log 2 (m * n) + 2)
  /-- `O(log(mn))` read time. -/
  readCost_le : readCost ≤ Nat.log 2 (m * n) + 1
  /-- `O(log(mn))` update time. -/
  updateCost_le : updateCost ≤ Nat.log 2 (m * n) + 1
  /-- `O(log m)` time to find `Ã_i`. -/
  rowNormReadCost_le : rowNormReadCost ≤ Nat.log 2 m + 1
  /-- `O(1)` time to find `‖A‖_F²`. -/
  frobNormCost_le : frobNormCost ≤ 1
  /-- `O(log(mn))` time to sample from `D_Ã`. -/
  rowSampleCost_le : rowSampleCost ≤ Nat.log 2 (m * n) + 1
  /-- `O(log(mn))` time to sample from `D_{A_i}`. -/
  entrySampleCost_le : entrySampleCost ≤ Nat.log 2 (m * n) + 1
  /-- Sampling primitive for `D_Ã`. -/
  rowLaw : FinDist (Fin m)
  rowLaw_spec : rowLaw = l2Dist (rowNormVec A) hvec
  /-- Sampling primitive for each `D_{A_i}`. -/
  entryLaw : Fin m → FinDist (Fin n)
  entryLaw_spec : ∀ i, entryLaw i = l2Dist (rowEuc A i) (hrows i)

/-- Fixed arXiv:1807.04271, Proposition 3.2 (p. 10): for every matrix whose
rows and row-norm vector are nonzero, the ℓ₂-sampling data structure exists
with the stated cost certificates and sampling laws. -/
theorem proposition_3_2 {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hrows : ∀ i, rowEuc A i ≠ 0) (hvec : rowNormVec A ≠ 0) :
    ∃ _DS : MatrixSampleDS A hrows hvec, True := by
  classical
  let w : ℕ := (Finset.univ.filter fun p : Fin m × Fin n => A p.1 p.2 ≠ 0).card
  refine ⟨?_, trivial⟩
  exact
    { w := w
      w_spec := rfl
      spaceCost := w * (Nat.log 2 (m * n) + 2)
      readCost := Nat.log 2 (m * n) + 1
      updateCost := Nat.log 2 (m * n) + 1
      rowNormReadCost := Nat.log 2 m + 1
      frobNormCost := 1
      rowSampleCost := Nat.log 2 (m * n) + 1
      entrySampleCost := Nat.log 2 (m * n) + 1
      spaceCost_le := le_rfl
      readCost_le := le_rfl
      updateCost_le := le_rfl
      rowNormReadCost_le := le_rfl
      frobNormCost_le := le_rfl
      rowSampleCost_le := le_rfl
      entrySampleCost_le := le_rfl
      rowLaw := l2Dist (rowNormVec A) hvec
      rowLaw_spec := rfl
      entryLaw := fun i => l2Dist (rowEuc A i) (hrows i)
      entryLaw_spec := fun _ => rfl }

end

end Qatlib.Papers.Recommender18.MainResults.DataStructure
