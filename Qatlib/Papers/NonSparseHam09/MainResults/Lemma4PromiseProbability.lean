/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Qatlib.Papers.NonSparseHam09.MainResults.Lemma3CirculantTail
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

def lemma4Statement : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ M : ℕ in Filter.atTop,
    c₁ / (M : ℝ) ≤ probOf M (fun b => b ∈ promiseSet M) ∧
    probOf M (fun b => b ∈ promiseSet M) ≤ c₂ / (M : ℝ)

lemma mem_promiseSet_iff (M : ℕ) (b : Fin M → Bool) :
    b ∈ promiseSet M ↔
      (∑ i, signVec b i = (promiseB M : ℝ)) ∨
        (∑ i, signVec b i = -(promiseB M : ℝ)) := by
  classical
  simp [promiseSet, promiseStrings]

lemma probOf_promiseSet_nonneg (M : ℕ) :
    0 ≤ probOf M (fun b => b ∈ promiseSet M) :=
  probOf_nonneg M _

lemma probOf_promiseSet_le_one (M : ℕ) :
    probOf M (fun b => b ∈ promiseSet M) ≤ 1 :=
  probOf_le_one M _

end Qatlib.Papers.NonSparseHam09.MainResults
