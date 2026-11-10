/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.ExactCountingCost
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined

theorem observedFinalGrid_le_linear {N : ℕ} (hN : 0 < N)
    (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) : observedFinalGrid z ≤ 97*N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hv : 0 ≤ pairMin z := by
    unfold pairMin firstReadout
    exact le_min (mul_nonneg (Nat.cast_nonneg N) (aeEstimate_mem _ _).1)
      (mul_nonneg (Nat.cast_nonneg N) (aeEstimate_mem _ _).1)
  have hs : ladderCost (pairMin z) N ≤ (N : ℝ)+1 := by
    unfold ladderCost
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · have h := pairMin_le z
      nlinarith
  have hg := observedFinalGrid_le_ladder z
  have hreal : (observedFinalGrid z : ℝ) ≤ 97*(N : ℝ) := by linarith
  exact_mod_cast hreal

theorem roughGrid_le_linear {N : ℕ} (hN : 0 < N) : nextCor4RoughGrid N ≤ 321*N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≤ (N : ℝ) := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hp := Real.pi_lt_four
  have h0 := Real.sqrt_nonneg (N : ℝ)
  have hg := roughGrid_le N
  have hreal : (nextCor4RoughGrid N : ℝ) ≤ 321*(N : ℝ) := by nlinarith
  exact_mod_cast hreal

theorem exact_counter_common_capacity (n : ℕ)
    (z : Fin (nextCor4RoughGrid (2^n)) × Fin (nextCor4RoughGrid (2^n))) :
    nextCor4RoughGrid (2^n) ≤ 2^(n+9) ∧ observedFinalGrid z ≤ 2^(n+9) := by
  have hN : 0 < (2 : ℕ)^n := pow_pos (by decide) n
  have hpow : (2 : ℕ)^(n+9) = 512*2^n := by rw [pow_add]; omega
  rw [hpow]
  constructor
  · exact (roughGrid_le_linear hN).trans (Nat.mul_le_mul_right _ (by decide : 321 ≤ 512))
  · exact (observedFinalGrid_le_linear hN z).trans (Nat.mul_le_mul_right _ (by decide : 97 ≤ 512))

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
