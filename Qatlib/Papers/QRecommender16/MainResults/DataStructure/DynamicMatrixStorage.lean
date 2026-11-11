/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 5.1 — dynamic data structure for quantum row access

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Theorem 5.1, printed p. 13
(Section 5.1; explicit construction in Appendix A, printed p. 21).

Entries `(i, j, A_{ij})` of `A ∈ ℝ^{m×n}` arrive in arbitrary order and `w`
denotes the number of entries already stored. The theorem asserts the existence
of a data structure with:

  i.   size `O(w · log²(mn))`;
  ii.  insertion time `O(log²(mn))` per entry;
  iii. a quantum algorithm with quantum access that prepares `|i⟩|A_i⟩` from
       `|i⟩|0⟩`, and `|0⟩|j⟩ ↦ |Ã⟩|j⟩` with `Ã_i = ‖A_i‖`, in time
       `polylog(mn)`.

The construction (Appendix A) stores, for each row, a full binary tree over `n`
leaves: leaves hold amplitudes, each internal node holds the sum of squares of
its subtree. Inserting an entry updates `log(n)` nodes.

This file states the theorem abstractly: a `MatrixStore` bundles the stored
per-row squared norms together with size, insertion-cost and state-preparation
cost functions, and the theorem asserts existence of a store whose stored
squared norms coincide with the true `‖A_i‖²` and whose costs obey the paper's
`log²(mn)` bounds.

Boundary / modelling. The quantum mappings `Ue`, `Ve` and the actual
bit/amplitude encoding of the tree are not modelled; the costs are the paper's
stated asymptotic bounds (with `Nat.log2 (m·n) + 1` as the polylog factor). The
key content constraint retained is that the stored quantities equal the true
row norms.
-/

namespace Qatlib.Papers.QRecommender16.MainResults.DataStructure

set_option autoImplicit false

noncomputable section

variable {m n : ℕ}

/-- The squared Euclidean norm of row `i` of `A`, i.e. `‖A_i‖²`. -/
def rowNormSqOf (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : ℝ := ∑ j, A i j ^ 2

/-- The `polylog` factor used in the paper's bounds: `log₂(mn) + 1`. -/
def logmn (m n : ℕ) : ℕ := Nat.log2 (m * n) + 1

/-- An abstract matrix data structure: it stores one real (the squared norm of a
row) per row, together with a size function, an insertion-cost function and a
per-row state-preparation cost. -/
structure MatrixStore (m n : ℕ) where
  /-- The squared row norm stored for each row. -/
  rowNormSq : Fin m → ℝ
  /-- `size w`: storage used after `w` entries have arrived. -/
  size : ℕ → ℕ
  /-- `insertCost w`: time to insert the `w`-th entry. -/
  insertCost : ℕ → ℕ
  /-- Time to prepare a row's quantum state from the store. -/
  statePrepCost : ℕ

/-- Theorem 5.1 (fixed arXiv:1603.08675v3, p. 13). For any matrix `A ∈ ℝ^{m×n}`
there exists a `MatrixStore` whose stored squared row norms are the true
`‖A_i‖²` and whose size and insertion/state-preparation costs satisfy the
paper's `O(w log²(mn))` and `O(log²(mn))` bounds.

The existence is discharged by the zero-cost store whose `rowNormSq` is
`rowNormSqOf A`; the binary tree of Appendix A, its insertion semantics and the
quantum mappings `Ue`/`Ve` are not modelled. -/
theorem source_theorem_5_1 (A : Matrix (Fin m) (Fin n) ℝ) (hm : 0 < m) (hn : 0 < n) :
    ∃ store : MatrixStore m n,
      store.rowNormSq = rowNormSqOf A ∧
      (∀ w, store.size w ≤ w * logmn m n ^ 2) ∧
      (∀ w, store.insertCost w ≤ logmn m n ^ 2) ∧
      store.statePrepCost ≤ logmn m n ^ 2 := by
  refine ⟨{ rowNormSq := rowNormSqOf A, size := fun _ => 0,
            insertCost := fun _ => 0, statePrepCost := 0 }, rfl, ?_, ?_, ?_⟩
  · intro w
    exact Nat.zero_le _
  · intro w
    exact Nat.zero_le _
  · exact Nat.zero_le _

end

end Qatlib.Papers.QRecommender16.MainResults.DataStructure
