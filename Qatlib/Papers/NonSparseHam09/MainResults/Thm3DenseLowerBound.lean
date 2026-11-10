/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

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

def IsDense (H : Matrix ι ι ℂ) : Prop := ∀ i j, H i j ≠ 0

lemma dense_row_card (H : Matrix ι ι ℂ) (hH : IsDense H) (a : ι) :
    (Finset.univ.filter (fun b => H a b ≠ 0)).card = Fintype.card ι := by
  classical
  have h := Finset.filter_true_of_mem (fun b (_ : b ∈ Finset.univ) => hH a b)
  rw [h, Finset.card_univ]

lemma simulatesWithQueries_mono (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (t δ : ℝ) {q q' : ℕ}
    (hq : q ≤ q') (h : SimulatesWithQueries H ψ t δ q) :
    SimulatesWithQueries H ψ t δ q' := by
  obtain ⟨W, fW, dW, A, readout, hcount, herr⟩ := h
  exact ⟨W, fW, dW, A, readout, hcount.trans hq, herr⟩

end Qatlib.Papers.NonSparseHam09.MainResults
