/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Qatlib.Papers.NonSparseHam09.MainResults.NormChain
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def prop2Statement (H : Matrix ι ι ℂ) (hH : H.IsHermitian) {k : ℕ}
    (hk : GraphArboricityLE (matrixGraph H) k) : Prop :=
  specNorm ((absMatrix H).map Complex.ofReal) ≤ 2 * (k : ℝ) * mcnNorm H ∧
  specNorm ((absMatrix H).map Complex.ofReal) ≤ 2 * (k : ℝ) * specNorm H ∧
  specNorm H ≤ 2 * (k : ℝ) * mcnNorm H

theorem specNorm_add_le (A B : Matrix ι ι ℂ) :
    specNorm (A + B) ≤ specNorm A + specNorm B := by
  rw [specNorm_eq_l2, specNorm_eq_l2, specNorm_eq_l2]
  exact norm_add_le A B

lemma specNorm_smul_nonneg {c : ℝ} (hc : 0 ≤ c) (A : Matrix ι ι ℂ) :
    specNorm (c • A) = c * specNorm A := by
  rw [specNorm_eq_l2, specNorm_eq_l2, norm_smul, Real.norm_of_nonneg hc]

lemma absMatrix_nonneg (H : Matrix ι ι ℂ) (i j : ι) : 0 ≤ absMatrix H i j :=
  norm_nonneg _

end Qatlib.Papers.NonSparseHam09.MainResults
