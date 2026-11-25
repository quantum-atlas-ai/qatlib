/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryExecution.OracleWord

@[expose] public section

/-!
# Majority-vote confidence and resource bridges

Odd repetition gives an exact multiplicative query bill.  The public tensor-copy theorem then
turns a one-third per-copy failure bound into the geometric majority-failure estimate `(8/9)^r`.
The resource and probability statements are kept as separate theorems so a consumer can combine
them with its own success event and word implementation.
-/

set_option autoImplicit false

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryExecution

namespace Qatlib.Concepts.QueryBridges

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The total query bill for `2r+1` identical runs of an oracle word. -/
def majorityQueryBudget (w : OracleWord I) (r : ℕ) : ℕ :=
  (2 * r + 1) * w.queryCount

/-- The majority budget is the query count of the corresponding controlled batch. -/
theorem majorityQueryBudget_eq (w : OracleWord I) (r : ℕ) :
    majorityQueryBudget w r = (w.controlled (2 * r + 1)).queryCount := by
  rw [OracleWord.queryCount_controlled]
  rfl

/-! The probability-side majority theorem lives in the public Qatlib amplification module.  This
module keeps the resource side independent of that optional probability import, so it remains
usable by module consumers even when only the circuit core is cached. -/

/-- The canonical geometric confidence target after `r` majority amplification rounds. -/
noncomputable def majorityFailureTarget (r : ℕ) : ℝ := (8 / 9 : ℝ) ^ r

/-- The geometric confidence target is nonnegative. -/
theorem majorityFailureTarget_nonneg (r : ℕ) : 0 ≤ majorityFailureTarget r := by
  unfold majorityFailureTarget
  exact pow_nonneg (by norm_num) r

/-- Each additional amplification round multiplies the target by `8 / 9`. -/
theorem majorityFailureTarget_succ (r : ℕ) :
    majorityFailureTarget (r + 1) = (8 / 9 : ℝ) * majorityFailureTarget r := by
  simp [majorityFailureTarget, pow_succ, mul_comm]

end Qatlib.Concepts.QueryBridges
