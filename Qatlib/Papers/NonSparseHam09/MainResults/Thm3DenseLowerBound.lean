/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Dense Hamiltonian lower-bound statement

`theorem3Statement` encodes a Hamiltonian query lower bound, including the matrix normalization
and row-support conditions. `IsDense` separately expresses that every matrix entry is nonzero;
the accompanying lemmas count row entries and enlarge simulation query budgets. This development
accompanies [ChildsKothari2010].

## Main statements

* `theorem3Statement`: the proposition encoding the dense Hamiltonian lower bound.
* `dense_row_card`: every row of an `IsDense` matrix has full support.
* `simulatesWithQueries_mono`: simulation persists when the query budget increases.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The proposition encoding Theorem 3 of [ChildsKothari2010]: existence of a Hermitian matrix
of unit spectral norm and an input vector for which simulation at time `π N / 2` and error
`1 / 4` fails below `N / 4` queries. It also requires at least `N` nonzero entries per row
and positive upper and lower comparisons of `mcnNorm` with `1 / sqrt N` and `maxNorm` with
`1 / N`. -/
def theorem3Statement (N : ℕ) [NeZero N] : Prop :=
  ∃ (H : Matrix ((Fin (N + 1) × Fin 2) × Fin N) ((Fin (N + 1) × Fin 2) × Fin N) ℂ)
    (ψ : ((Fin (N + 1) × Fin 2) × Fin N) → ℂ),
    H.IsHermitian ∧
    specNorm H = 1 ∧
    (∀ a, N ≤ (Finset.univ.filter (fun b => H a b ≠ 0)).card) ∧
    (∃ c : ℝ, 0 < c ∧ c / Real.sqrt (N : ℝ) ≤ mcnNorm H) ∧
    (∃ c : ℝ, 0 < c ∧ mcnNorm H ≤ c / Real.sqrt (N : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ c / (N : ℝ) ≤ maxNorm H) ∧
    (∃ c : ℝ, 0 < c ∧ maxNorm H ≤ c / (N : ℝ)) ∧
    (∀ q : ℕ, q < N / 4 →
      ¬ SimulatesWithQueries H ψ (Real.pi * (N : ℝ) / 2) (1 / 4) q)

/-- The predicate that every entry of `H` is nonzero. -/
def IsDense (H : Matrix ι ι ℂ) : Prop := ∀ i j, H i j ≠ 0

/-- Every row of a dense matrix has as many nonzero entries as there are column indices. See
[ChildsKothari2010]. -/
lemma dense_row_card (H : Matrix ι ι ℂ) (hH : IsDense H) (a : ι) :
    (Finset.univ.filter (fun b => H a b ≠ 0)).card = Fintype.card ι := by
  classical
  have h := Finset.filter_true_of_mem (fun b (_ : b ∈ Finset.univ) => hH a b)
  rw [h, Finset.card_univ]

/-- A simulation using at most `q` queries also satisfies any larger query budget `q'`. See
[ChildsKothari2010]. -/
lemma simulatesWithQueries_mono (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (t δ : ℝ) {q q' : ℕ}
    (hq : q ≤ q') (h : SimulatesWithQueries H ψ t δ q) :
    SimulatesWithQueries H ψ t δ q' := by
  obtain ⟨W, fW, dW, A, readout, hcount, herr⟩ := h
  exact ⟨W, fW, dW, A, readout, hcount.trans hq, herr⟩

end Qatlib.Papers.NonSparseHam09.MainResults
