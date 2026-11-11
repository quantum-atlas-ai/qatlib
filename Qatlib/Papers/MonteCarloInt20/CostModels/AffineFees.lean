/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.AffineWord
import Qatlib.Papers.MonteCarloInt20.CostModels.CorrectedLeadingCost

/-!
# Affine jump-word fees

`sourceJumpFee` assigns a cost to an affine jump-operation word using its multiplication count
and the stated non-self-updating multiplication fee. The resulting expression connects explicit
operation counts to the leading-cost convention discussed in [KanekoEtAl2020].

For the complete index word at `Corrected.jumpIndexWidth`, the fee equals `Corrected.jumpFee`.

## Main statements

* `source_jump_fee`: Compute the fee as `140 * qs.length * n^2`.
* `corrected_word_fee`: Identify the complete corrected-width word fee with the corrected jump
  fee.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Papers.MonteCarloInt20.PrnJump.Affine

namespace Qatlib.Papers.MonteCarloInt20.CostModels.AffineFees

/-- The fee `2 * multiplicationCount ops * Corrected.nonselfFee n` assigned to a jump-operation
word at register width `n`. -/
def sourceJumpFee {k : ℕ} (ops : List (JumpOp k)) (n : ℕ) : ℕ :=
  (2*multiplicationCount ops)*Corrected.nonselfFee n

/-- The affine operation word generated from `qs` has source jump fee `140 * qs.length * n^2`;
see [KanekoEtAl2020]. -/
theorem source_jump_fee {k : ℕ} (qs : List (Fin k)) (n : ℕ) :
    sourceJumpFee (operations qs) n = 140*qs.length*n^2 := by
  rw [sourceJumpFee, operations_mul_count, Corrected.nonselfFee]
  ring

/-- The operation word enumerating all corrected-width indices has fee `Corrected.jumpFee s d
n`; see [KanekoEtAl2020]. -/
theorem corrected_word_fee (s d n : ℕ) :
    sourceJumpFee (operations (List.ofFn (fun q : Fin (Corrected.jumpIndexWidth s d) => q))) n =
      Corrected.jumpFee s d n := by
  simp [sourceJumpFee, operations_mul_count, Corrected.jumpFee]

end Qatlib.Papers.MonteCarloInt20.CostModels.AffineFees
