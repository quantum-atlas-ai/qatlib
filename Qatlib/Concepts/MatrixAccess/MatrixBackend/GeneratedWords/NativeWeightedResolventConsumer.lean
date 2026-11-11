/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.CleanWordLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeWeightedGapError
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.NativeWeightedLCUSlot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanBlockLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Transfer a weighted clean-word polynomial encoding to resolvent error.
The exact clean-word encoding is an explicit input: this module does not
establish it, the oracle's physical access, or finite synthesis costs. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open scoped BigOperators Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for weighted Resolvent Branch Dec Eq in the native weighted resolvent consumer model. -/
local instance weightedResolventBranchDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- The exact weighted clean block of the actual relabeled word yields a
weighted resolvent encoding under the per-node spectral and coefficient
conditions. No aggregate error estimate is assumed. -/
theorem weighted_original_resolvent_of_clean_word
    (b : ℕ) (hb : 0 < b)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (weights : J → ℂ) (j₀ : J)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B : ℝ) (r K : J → ℝ) (z : J → ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : ∀ j, α + ‖z j‖ ≤ B) (hr : ∀ j, 0 < r j)
    (hsep : ∀ j w, w ∈ matrixNumericalRange A → r j ≤ ‖z j-w‖)
    (hK : ∀ j, jointResolventCondition B (r j) ≤ K j)
    (hsmall : ∀ j, nativeCoefficientError (ps j) (p j) (slack j) α B (z j) ≤
      1/(4*(K j)^2))
    (hmass : 0 < coefficientMass weights)
    (hword : ProjectedUnitaryEncoding
      (∑ j, (weights j / (coefficientMass weights : ℂ)) •
        (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
          (nativeShiftBlock (ps j) (p j) (slack j) A α) b))
      (evaluate (parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)))
        (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord weights j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)))
      (tagFrame j₀ (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)))
      (tagFrame j₀ (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)))) :
    BlockEncoding (∑ j, weights j • matrixResolvent A (z j))
      (evaluate (parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)))
        (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord weights j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)))
      (tagFrame j₀ (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)))
      (tagFrame j₀ (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)))
      (((b : ℝ)/B) * coefficientMass weights)
      (∑ j, ‖weights j‖ *
        (((2*(K j)^2+4*(K j)^3) *
          nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
          reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B)) := by
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hmc : (coefficientMass weights : ℂ) ≠ 0 := by exact_mod_cast hmass.ne'
  have hscale :
      (((b : ℝ)/B) * coefficientMass weights) •
        (∑ j, (weights j / (coefficientMass weights : ℂ)) •
          (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
            (nativeShiftBlock (ps j) (p j) (slack j) A α) b)) =
      ∑ j, weights j • (((B⁻¹ : ℝ) : ℂ) •
        Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (nativeShiftBlock (ps j) (p j) (slack j) A α) b) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ext x y
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_inv]
    field_simp [hbc, hBc, hmc]
  have herr := native_weighted_gap_error b hb ps p slack weights A U F α B r K z
    hbe hB hbound hr hsep hK hsmall
  have hnonneg : 0 ≤ ∑ j, ‖weights j‖ *
      (((2*(K j)^2+4*(K j)^3) *
        nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
        reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B) :=
    (norm_nonneg _).trans herr
  refine ⟨hword.unitary, hword.left_isometry, hword.right_isometry,
    mul_pos (div_pos hbp hB) hmass, hnonneg, ?_⟩
  rw [hword.encoded, hscale]
  simpa only [norm_sub_rev] using herr

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
