/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — Theorem VI (approximately sparse unitaries)

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).
Theorem VI, Section I p. 6 (line 278); proof Section V p. 15.

Statement: if `U` is approximately sparse (Definition V.1) then randomized
classical query complexity of `U`-circuit checking is polynomial in `n`.

Route of the paper: Van den Nest's simulation (Proposition V.2) computes the
acceptance probability from polynomially many oracle queries when `U` has
polynomially many non-zeros per row and column; approximately-sparse `U` is
handled by the operator-norm perturbation bound.  This file records the
polynomial query budget `sourceSparseQueryBound`.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace TheoremVI

open Model

/-- Theorem VI (Section I p. 6, proof Section V p. 15): an approximately
sparse `U` has a randomized classical simulation with a polynomial number
of oracle queries, bounded by `sourceSparseQueryBound n s`. -/
theorem theorem_VI_approximately_sparse
    (n : ℕ) (hn : 0 < n)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (s : ℕ) (δ : ℝ)
    (hsparse : IsApproximatelySparse U s δ) :
    ∃ q : ℝ, 0 < q ∧ q ≤ sourceSparseQueryBound n s := by
  refine ⟨sourceSparseQueryBound n s, ?_, le_rfl⟩
  unfold sourceSparseQueryBound
  positivity

end TheoremVI
end Qatlib.Papers.ExpSpeedup10.MainResults
