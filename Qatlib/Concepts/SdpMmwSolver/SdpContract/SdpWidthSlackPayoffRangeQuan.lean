/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpWidthSlackPayoffRangeStat
import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.SdpMmwSolver.OracleError

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
set_option warningAsError false

theorem not_sdpWidthSlackPayoffRange : ¬ SdpWidthSlackPayoffRangeOriginalContract := by
  intro h
  have hf := h 1 1 (fun _ => 1) 0 (fun _ => 1) (fun _ _ => 4) 0
    2 1 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i; exact ⟨Matrix.isHermitian_one, by simp⟩)
    ⟨Matrix.isHermitian_zero, by simp⟩
    (by intro i; norm_num) rfl rfl
    (by intro t; constructor; intro i; norm_num; norm_num [sdpSampledWidthBudget])
  have ho := hf.2
  norm_num [sdpDualCertificate, sdpDualCertRounds] at ho

theorem sdpWidthSlackPayoffRange : SdpWidthSlackPayoffRange := by
  intro D m A Cv b y j₀ α R δ ε hD hα hα2 hR hδ hε hsmall hbudget hA hCv hb hA0 hb0 hy
  constructor
  · intro s
    let Z : Operator D := (∑ i, y s i • A i) - Cv
    have hZ : Z.IsHermitian :=
      (isSelfAdjoint_sum _ (fun i _ => (hA i).1.smul (by simp [IsSelfAdjoint]))).sub hCv.1
    have hn : ‖∑ i, y s i • A i‖ ≤ ∑ i, y s i := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((hy s).1 i)]
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hA i).2 ((hy s).1 i)
    have hw : (∑ i, y s i) ≤ α * (1 + 2 * R * ε) := by
      apply le_trans _ (hy s).2
      apply Finset.sum_le_sum
      intro i _
      nlinarith [(hy s).1 i, hb i]
    have hnZ : ‖Z‖ ≤ 2 * α := by
      have htri := norm_sub_le (∑ i, y s i • A i) Cv
      change ‖Z‖ ≤ _ at htri
      have hs := mul_le_mul_of_nonneg_left hsmall hα.le
      nlinarith [hCv.2]
    have hpad : ((2 * α - ‖Z‖) • (1 : Operator D)).PosSemidef :=
      (Matrix.PosSemidef.one : (1 : Operator D).PosSemidef).smul
        (by exact_mod_cast (sub_nonneg.mpr hnZ))
    have hupper : ((2 * α) • (1 : Operator D) - Z).PosSemidef := by
      convert! (mmw_shift_posSemidef D Z hZ hD).add hpad using 1
      module
    have hlower : (Z + (2 * α) • (1 : Operator D)).PosSemidef := by
      have h := (mmw_shift_posSemidef D (-Z) hZ.neg hD).add hpad
      rw [norm_neg] at h
      convert! h using 1
      module
    have hscale : 0 ≤ (4 * α)⁻¹ := by positivity
    have hunit : (4 * α)⁻¹ • ((4 * α) • (1 : Operator D)) = 1 := by
      rw [smul_smul, inv_mul_cancel₀ (by positivity : (4 * α : ℝ) ≠ 0), one_smul]
    have hdiff : (1 : Operator D) - sdpDualPayoff D m A Cv α y s =
        (4 * α)⁻¹ • ((2 * α) • (1 : Operator D) - Z) := by
      change 1 - (4 * α)⁻¹ • (Z + (2 * α) • (1 : Operator D)) = _
      calc
        _ = (4 * α)⁻¹ • ((4 * α) • (1 : Operator D)) -
            (4 * α)⁻¹ • (Z + (2 * α) • (1 : Operator D)) := by rw [hunit]
        _ = _ := by module
    refine ⟨?_, ?_, ?_⟩
    · exact (hlower.smul (by exact_mod_cast hscale)).isHermitian
    · apply Matrix.le_iff.mpr
      simpa only [sub_zero] using! hlower.smul (by exact_mod_cast hscale)
    · apply Matrix.le_iff.mpr
      rw [hdiff]
      exact hupper.smul (by exact_mod_cast hscale)
  · let T := sdpDualCertRounds D R δ ε
    have hT : 0 < (T : ℝ) := by exact_mod_cast Nat.succ_pos _
    have heval : (∑ i, sdpDualCertificate m δ α R j₀ y T i * b i) =
        δ * α / (2 * R) * b j₀ +
          (∑ t ∈ Finset.range T, ∑ i, y t i * b i) / T := by
      simp only [sdpDualCertificate, add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
        ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1
      simp only [Finset.sum_mul, ← Finset.sum_div]
      rw [Finset.sum_comm]
    rw [heval, hb0]
    have hw : (∑ t ∈ Finset.range T, ∑ i, y t i * b i) ≤
        (T : ℝ) * (α * (1 + 2 * R * ε)) := by
      calc
        _ ≤ ∑ _t ∈ Finset.range T, α * (1 + 2 * R * ε) := by
          apply Finset.sum_le_sum
          intro t _
          calc
            _ = ∑ i, b i * y t i := by simp only [mul_comm]
            _ ≤ _ := (hy t).2
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hav : (∑ t ∈ Finset.range T, ∑ i, y t i * b i) / (T : ℝ) ≤
        α * (1 + 2 * R * ε) := by
      apply (div_le_iff₀ hT).mpr
      simpa only [mul_comm] using! hw
    have hoff : δ * α / (2 * R) * R = δ * α / 2 := by
      field_simp
    rw [hoff]
    have hs := mul_le_mul_of_nonneg_left hbudget hα.le
    nlinarith

end Qatlib.Concepts.SdpMmwSolver.SdpContract
