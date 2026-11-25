/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseHam05.MainResults.EntryPartition

/-!
# Sparse Hamiltonian decomposition consumer regression

This ordinary module exercises the paper-layer entry-partition theorem through its public
namespace and checks the row-wise Euclidean estimate on the same witness.
-/

@[expose] public section

open Matrix
open Qatlib.Papers.SparseHam05.MainResults
open Qatlib.Papers.SparseHam05.MainResults
open scoped BigOperators Classical

namespace QatlibTests.SparseHam05DeepRegression

set_option autoImplicit false

/-- The public paper theorem exposes a complete decomposition and its row-energy bound. -/
example (N d : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hsp : ColSparse d H)
    (hherm : Hᴴ = H) :
    ∃ Hs : Fin (d ^ 2) → Matrix (Fin N) (Fin N) ℂ,
      IsSparseDecomposition H (d ^ 2) Hs ∧
        ∀ k i, (∑ j, ‖Hs k i j‖ ^ 2) ≤ ∑ j, ‖H i j‖ ^ 2 := by
  exact one_sparse_decomposition_row_energy_le N d H hsp hherm

end QatlibTests.SparseHam05DeepRegression
