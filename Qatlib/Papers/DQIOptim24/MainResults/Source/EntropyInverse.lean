/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DQIOptim24.MainResults.Source.Definitions
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic

@[expose] public section


/-!
# Endpoint regression for the increasing binary-entropy inverse

The inverse takes the supremum of sublevel sets on `[0,1/2]`.
-/

namespace Qatlib.Papers.DQIOptim24.MainResults.Source

/-- Entropy in bits is natural-log binary entropy divided by `log 2`. -/
theorem binaryEntropy_eq_binEntropy (p : ℝ) :
    binaryEntropy p = Real.binEntropy p / Real.log 2 := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [binaryEntropy, Real.negMulLog_def]
  ring

/-- The increasing inverse branch sends zero entropy to zero. -/
theorem binaryEntropyInv_zero : binaryEntropyInv 0 = 0 := by
  have hz : (0 : ℝ) ∈ {s : ℝ | s ∈ Set.Icc 0 (1 / 2) ∧ binaryEntropy s ≤ 0} := by
    norm_num [binaryEntropy]
  apply le_antisymm
  · apply csSup_le ⟨0, hz⟩
    rintro s ⟨hs, he⟩
    by_contra hn
    have hp : 0 < s := lt_of_not_ge hn
    have hent : 0 < binaryEntropy s := by
      rw [binaryEntropy_eq_binEntropy]
      exact div_pos (Real.binEntropy_pos hp (by linarith [hs.2])) (Real.log_pos (by norm_num))
    linarith
  · exact le_csSup ⟨1 / 2, fun s hs => hs.1.2⟩ hz

end Qatlib.Papers.DQIOptim24.MainResults.Source
