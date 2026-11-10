/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpDualPayoffRangeStat
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
set_option warningAsError false

theorem sdpDualPayoffRange : SdpDualPayoffRange := by
  intro D m A Cv b y alpha hD ha ha1 hA hCv hb hy s
  let Z : Operator D := (∑ i, y s i • A i) - Cv
  have hsum : (∑ i, y s i • A i).IsHermitian :=
    isSelfAdjoint_sum _ (fun i _ => (hA i).1.smul (by simp [IsSelfAdjoint]))
  have hZ : Z.IsHermitian := hsum.sub hCv.1
  have hn : ‖∑ i, y s i • A i‖ ≤ ∑ i, y s i := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((hy s).1 i)]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hA i).2 ((hy s).1 i)
  have hwidth : (∑ i, y s i) ≤ alpha := by
    apply le_trans _ (hy s).2
    apply Finset.sum_le_sum
    intro i _
    nlinarith [(hy s).1 i, hb i]
  have hnZ : ‖Z‖ ≤ 2 * alpha := by
    have h := norm_sub_le (∑ i, y s i • A i) Cv
    change ‖Z‖ ≤ _ at h
    linarith [hCv.2]
  have hpad : ((2 * alpha - ‖Z‖) • (1 : Operator D)).PosSemidef :=
    (Matrix.PosSemidef.one : (1 : Operator D).PosSemidef).smul (by exact_mod_cast (sub_nonneg.mpr hnZ))
  have hupper : ((2 * alpha) • (1 : Operator D) - Z).PosSemidef := by
    convert! (mmw_shift_posSemidef D Z hZ hD).add hpad using 1
    module
  have hlower : (Z + (2 * alpha) • (1 : Operator D)).PosSemidef := by
    have h := (mmw_shift_posSemidef D (-Z) hZ.neg hD).add hpad
    rw [norm_neg] at h
    convert! h using 1
    module
  have hscale : 0 ≤ (4 * alpha)⁻¹ := by positivity
  have hunit : (4 * alpha)⁻¹ • ((4 * alpha) • (1 : Operator D)) = 1 := by
    rw [smul_smul, inv_mul_cancel₀ (by positivity : (4 * alpha : ℝ) ≠ 0), one_smul]
  have hdiff : (1 : Operator D) - sdpDualPayoff D m A Cv alpha y s =
      (4 * alpha)⁻¹ • ((2 * alpha) • (1 : Operator D) - Z) := by
    change 1 - (4 * alpha)⁻¹ • (Z + (2 * alpha) • (1 : Operator D)) = _
    calc
      _ = (4 * alpha)⁻¹ • ((4 * alpha) • (1 : Operator D)) -
          (4 * alpha)⁻¹ • (Z + (2 * alpha) • (1 : Operator D)) := by rw [hunit]
      _ = _ := by module
  refine ⟨?_, ?_, ?_⟩
  · exact (hlower.smul (by exact_mod_cast hscale)).isHermitian
  · apply Matrix.le_iff.mpr
    simpa only [sub_zero] using! hlower.smul (by exact_mod_cast hscale)
  · apply Matrix.le_iff.mpr
    rw [hdiff]
    exact hupper.smul (by exact_mod_cast hscale)

end Qatlib.Concepts.SdpMmwSolver.SdpContract
