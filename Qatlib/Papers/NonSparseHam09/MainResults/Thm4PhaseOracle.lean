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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def theorem4Statement : Prop :=
  ¬ ∃ (p : ℝ → ℝ → ℕ) (C : ℝ) (k : ℕ),
      0 < C ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (p x y : ℝ) ≤ C * (1 + x + y) ^ k) ∧
      (∀ (N : ℕ) [NeZero N] (H : Matrix (Fin N) (Fin N) ℂ) (ψ : Fin N → ℂ) (t : ℝ),
        H.IsHermitian → 0 ≤ t →
        ∃ q : ℕ, q ≤ p (specNorm H * t) (Real.log N) ∧
          SimulatesPhaseWithQueries H ψ t (1 / 4) q)

lemma phaseEntry_of_zero (H : Matrix ι ι ℂ) (i j : ι) (h : H i j = 0) :
    phaseEntry H i j = 1 := by
  unfold phaseEntry
  rw [if_pos h]

lemma phaseEntry_norm_eq_one (H : Matrix ι ι ℂ) (i j : ι) (h : H i j ≠ 0) :
    ‖phaseEntry H i j‖ = 1 := by
  unfold phaseEntry
  rw [if_neg h, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr h))

end Qatlib.Papers.NonSparseHam09.MainResults
