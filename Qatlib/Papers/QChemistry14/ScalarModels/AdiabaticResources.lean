/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar resource bounds for adiabatic embedding

This module defines real-valued formulas for ancillary qubits, total qubits, and coupler edges
in the embedding resource model. It derives explicit polynomial and logarithmic upper bounds
when the locality parameter is bounded by `log M`. See [McCleanEtAl2014].

## Main statements

* `coupler_le_log`: If `M ≥ 3` and `1 ≤ L ≤ log M`, the coupler-edge formula is at most `M² *
  (log M)²`.
* `total_qubits_le`: If `M ≥ 3` and `0 ≤ L ≤ log M`, the total-qubit formula is at most `2 * M²
  * log M`.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.AdiabaticResources

noncomputable section

/-- The scalar ancilla-qubit count `M² * L`. -/
def ancillaQubits (M L : ℝ) : ℝ := M ^ 2 * L

/-- The scalar total-qubit count `M + M² * L`. -/
def totalQubits (M L : ℝ) : ℝ := M + ancillaQubits M L

/-- The scalar coupler-edge count `M² * L * (L - 1) / 2`. -/
def couplerEdges (M L : ℝ) : ℝ := M ^ 2 * (L * (L - 1) / 2)

/-- For `L ≥ 1`, the pair-count expression `L * (L - 1) / 2` is at most `L²`. -/
theorem coupler_per_system_le (L : ℝ) (hL : 1 ≤ L) :
    L * (L - 1) / 2 ≤ L ^ 2 := by
  nlinarith

/-- For nonnegative `M` and `L ≥ 1`, the coupler-edge formula is at most `M² * L²`. -/
theorem coupler_le (M L : ℝ) (_hM : 0 ≤ M) (hL : 1 ≤ L) :
    couplerEdges M L ≤ M ^ 2 * L ^ 2 := by
  unfold couplerEdges
  have h1 : L * (L - 1) / 2 ≤ L ^ 2 := coupler_per_system_le L hL
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  nlinarith

/-- If `M ≥ 3` and `1 ≤ L ≤ log M`, the coupler-edge formula is at most `M² * (log M)²`. -/
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

/-- If `M ≥ 3` and `0 ≤ L ≤ log M`, the total-qubit formula is at most `2 * M² * log M`. See
[McCleanEtAl2014]. -/
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
