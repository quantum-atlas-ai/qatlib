/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.AdiabaticResources

noncomputable section

def ancillaQubits (M L : ℝ) : ℝ := M ^ 2 * L

def totalQubits (M L : ℝ) : ℝ := M + ancillaQubits M L

def couplerEdges (M L : ℝ) : ℝ := M ^ 2 * (L * (L - 1) / 2)

theorem coupler_per_system_le (L : ℝ) (hL : 1 ≤ L) :
    L * (L - 1) / 2 ≤ L ^ 2 := by
  nlinarith

theorem coupler_le (M L : ℝ) (_hM : 0 ≤ M) (hL : 1 ≤ L) :
    couplerEdges M L ≤ M ^ 2 * L ^ 2 := by
  unfold couplerEdges
  have h1 : L * (L - 1) / 2 ≤ L ^ 2 := coupler_per_system_le L hL
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  nlinarith

theorem coupler_le_log (M L : ℝ) (_hM : 3 ≤ M) (_hL0 : 0 ≤ L) (hLlog : L ≤ Real.log M)
    (hL1 : 1 ≤ L) :
    couplerEdges M L ≤ M ^ 2 * (Real.log M) ^ 2 := by
  have hlog0 : 0 ≤ Real.log M := le_trans _hL0 hLlog
  have hLsq : L ^ 2 ≤ (Real.log M) ^ 2 := by
    nlinarith
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  calc
    couplerEdges M L ≤ M ^ 2 * L ^ 2 := coupler_le M L (by linarith) hL1
    _ ≤ M ^ 2 * (Real.log M) ^ 2 := mul_le_mul_of_nonneg_left hLsq hM2

theorem total_qubits_le (M L : ℝ) (_hM : 3 ≤ M) (_hL0 : 0 ≤ L) (hLlog : L ≤ Real.log M) :
    totalQubits M L ≤ 2 * M ^ 2 * Real.log M := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlog1 : (1 : ℝ) ≤ Real.log M := le_trans hlog3 (Real.log_le_log (by norm_num) _hM)
  have hlog0 : 0 ≤ Real.log M := le_trans zero_le_one hlog1
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hMsqlog : M ≤ M ^ 2 * Real.log M := by
    have : M ^ 2 * 1 ≤ M ^ 2 * Real.log M :=
      mul_le_mul_of_nonneg_left hlog1 (sq_nonneg M)
    linarith
  have han : M ^ 2 * L ≤ M ^ 2 * Real.log M :=
    mul_le_mul_of_nonneg_left hLlog (sq_nonneg M)
  unfold totalQubits ancillaQubits
  linarith

end
end Qatlib.Papers.QChemistry14.ScalarModels.AdiabaticResources
