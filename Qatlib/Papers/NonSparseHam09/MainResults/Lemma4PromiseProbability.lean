/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Qatlib.Papers.NonSparseHam09.MainResults.Lemma3CirculantTail

/-!
# Promise-set probability proposition

Defines `lemma4Statement` as the assertion that the promise-set probability is eventually
bounded above and below by positive constants times `1 / M`. The accompanying lemmas unfold
promise membership and bound its finite counting probability between zero and one. See
[ChildsKothari2010] for the surrounding analysis.

## Main statements

* `lemma4Statement`: The proposition that `probOf M (fun b => b ∈ promiseSet M)` is eventually
  bounded below by `c₁ / M` and above by `c₂ / M` for positive constants `c₁` and `c₂`.
* `mem_promiseSet_iff`: A Boolean string lies in `promiseSet M` exactly when its sign sum is
  `promiseB M` or its negative.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

/-- The proposition that `probOf M (fun b => b ∈ promiseSet M)` is eventually bounded below by
`c₁ / M` and above by `c₂ / M` for positive constants `c₁` and `c₂`. -/
def lemma4Statement : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ M : ℕ in Filter.atTop,
    c₁ / (M : ℝ) ≤ probOf M (fun b => b ∈ promiseSet M) ∧
    probOf M (fun b => b ∈ promiseSet M) ≤ c₂ / (M : ℝ)

/-- A Boolean string lies in `promiseSet M` exactly when its sign sum is `promiseB M` or its
negative [ChildsKothari2010]. -/
lemma mem_promiseSet_iff (M : ℕ) (b : Fin M → Bool) :
    b ∈ promiseSet M ↔
      (∑ i, signVec b i = (promiseB M : ℝ)) ∨
        (∑ i, signVec b i = -(promiseB M : ℝ)) := by
  classical
  simp [promiseSet, promiseStrings]

/-- The probability of the promise set is nonnegative [ChildsKothari2010]. -/
lemma probOf_promiseSet_nonneg (M : ℕ) :
    0 ≤ probOf M (fun b => b ∈ promiseSet M) :=
  probOf_nonneg M _

/-- The probability of the promise set is at most one [ChildsKothari2010]. -/
lemma probOf_promiseSet_le_one (M : ℕ) :
    probOf M (fun b => b ∈ promiseSet M) ≤ 1 :=
  probOf_le_one M _

end Qatlib.Papers.NonSparseHam09.MainResults
