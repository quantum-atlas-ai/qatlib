/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NativeNeumannLogCutoff
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapBlockEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems

/-! One original-oracle word with an explicit logarithmic precision cutoff. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The finite construction in `NativeNeumannLogPrecision` satisfies `log_reciprocal_condition_mono` under the displayed hypotheses. -/
private theorem log_reciprocal_condition_mono (κ K : ℝ) (hκ : 1 ≤ κ) (hK : κ ≤ K) (b : ℕ) :
    reciprocalError κ⁻¹ b ≤ reciprocalError K⁻¹ b := by
  have hκp : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hKp : 0 < K := hκp.trans_le hK
  have hi : K⁻¹ ≤ κ⁻¹ := (inv_le_inv₀ hKp hκp).mpr hK
  have hκi : κ⁻¹ ≤ 1 := (inv_le_one₀ hκp).mpr hκ
  have hκ0 : 0 ≤ κ⁻¹ := (inv_pos.mpr hκp).le
  have hq : 0 ≤ 1-κ⁻¹^2 := by nlinarith
  have hqle : 1-κ⁻¹^2 ≤ 1-K⁻¹^2 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hKp.le) hi 2
    linarith
  unfold reciprocalError
  simp only [div_eq_mul_inv, inv_inv]
  exact mul_le_mul (pow_le_pow_left₀ hq hqle b) hK hκp.le
    (pow_nonneg (hq.trans hqle) b)

/-- Explicit finite cutoff and precision for the same original-oracle word.
The coefficient inequality is an input certificate; this theorem does not
claim that any classical parameter generator produces such a certificate. -/
theorem native_original_neumann_log_precision
    (K k : ℕ) (hK2 : 2 ≤ K)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B r : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : α + ‖z‖ ≤ B) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖)
    (hcondition : jointResolventCondition B r ≤ (K : ℝ))
    (hsmall : nativeCoefficientError ps p slack α B z ≤ 1/(4*(K:ℝ)^2))
    (hbudget : (2*(K:ℝ)^2+4*(K:ℝ)^3)*nativeCoefficientError ps p slack α B z +
      ((2:ℝ)⁻¹)^(k+2) ≤ ((2:ℝ)⁻¹)^k) :
    let b := K*K*(k+Nat.clog 2 K+2)
    ∃ hb : 0 < b,
      WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps p slack) ∧
      BlockEncoding (matrixResolvent A z)
        (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U))
          (nativeOriginalNeumannWord b hb F ps p slack))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F))
        ((b : ℝ)/B) (((2:ℝ)⁻¹)^k/B) ∧
      adjointQueryCount (nativeOriginalNeumannWord b hb F ps p slack) = 2*b-1 ∧
      adjointGateCount (nativeOriginalNeumannWord b hb F ps p slack) =
        2*b + (2*b-1)*(436+(if slack then 1 else 0)) := by
  let b := K*K*(k+Nat.clog 2 K+2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hc1 : 1 ≤ jointResolventCondition B r := by
    have h := (le_max_left 2 (B/r) : (2:ℝ) ≤ max 2 (B/r))
    change 2 ≤ jointResolventCondition B r at h
    linarith
  have htail := (log_reciprocal_condition_mono (jointResolventCondition B r) (K:ℝ)
    hc1 hcondition b).trans (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.LogarithmicReciprocalTail.logarithmic_reciprocal_tail K k hK2)
  have herror : ((2*(K:ℝ)^2+4*(K:ℝ)^3)*nativeCoefficientError ps p slack α B z +
      reciprocalError (jointResolventCondition B r)⁻¹ b) / B ≤ ((2:ℝ)⁻¹)^k/B := by
    apply div_le_div_of_nonneg_right _ hB.le
    linarith
  have h := native_original_neumann_resolvent_gap_blockEncoding b hb ps p slack
    A U F α B r (K:ℝ) z hbe hB hbound hr hsep hcondition hsmall
  refine ⟨hb, h.1, h.2.1.mono herror, h.2.2⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
