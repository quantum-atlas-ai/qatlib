/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.AffineWord
import Qatlib.Papers.MonteCarloInt20.CostModels.CorrectedLeadingCost
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Papers.MonteCarloInt20.PrnJump.Affine

namespace Qatlib.Papers.MonteCarloInt20.CostModels.AffineFees

def sourceJumpFee {k : ℕ} (ops : List (JumpOp k)) (n : ℕ) : ℕ :=
  (2*multiplicationCount ops)*Corrected.nonselfFee n

theorem source_jump_fee {k : ℕ} (qs : List (Fin k)) (n : ℕ) :
    sourceJumpFee (operations qs) n = 140*qs.length*n^2 := by
  rw [sourceJumpFee, operations_mul_count, Corrected.nonselfFee]
  ring

theorem corrected_word_fee (s d n : ℕ) :
    sourceJumpFee (operations (List.ofFn (fun q : Fin (Corrected.jumpIndexWidth s d) => q))) n =
      Corrected.jumpFee s d n := by
  simp [sourceJumpFee, operations_mul_count, Corrected.jumpFee]

end Qatlib.Papers.MonteCarloInt20.CostModels.AffineFees
