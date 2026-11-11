/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
/-! Direct block-encoding form of the original-input native Neumann bound.
No small-coefficient-error hypothesis is needed for this b-dependent bound.
The sharper gap-dependent bound remains available in its original module. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The same emitted word, its canonical resolvent target, and its costs.
This consumes the original exact common-frame input and the established
coefficient/truncation bound; no full-dilation approximation is supplied. -/
theorem native_original_neumann_resolvent_blockEncoding
    (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B r : ℝ) (z : ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : α+‖z‖ ≤ B) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖) :
    WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps p slack) ∧
    BlockEncoding (matrixResolvent A z)
      (evaluate (uniformNeumannOracle b (nativeDataQuery U))
        (nativeOriginalNeumannWord b hb F ps p slack))
      (uniformNeumannFrame b hb (nativeDataFrame F))
      (uniformNeumannFrame b hb (nativeDataFrame F))
      ((b : ℝ)/B)
      (((b : ℝ)^2*nativeCoefficientError ps p slack α B z+
        reciprocalError (jointResolventCondition B r)⁻¹ b)/B) ∧
    adjointQueryCount (nativeOriginalNeumannWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeOriginalNeumannWord b hb F ps p slack) =
      2*b+(2*b-1)*(436+(if slack then 1 else 0)) := by
  obtain ⟨hw, he, herr, hq, hg⟩ := native_original_neumann_resolvent
    b hb ps p slack A U F α B r z hbe hB hbound hr hsep
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hscale : ((b : ℝ)/B) • (((b : ℂ)⁻¹) •
      leftDefectNeumann (nativeShiftBlock ps p slack A α) b) =
      ((B⁻¹ : ℝ) : ℂ) • leftDefectNeumann (nativeShiftBlock ps p slack A α) b := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_inv]
    field_simp [hbc, hBc]
  refine ⟨hw, ⟨he.unitary, he.left_isometry, he.right_isometry,
    div_pos hbp hB, (norm_nonneg _).trans herr, ?_⟩, hq, hg⟩
  rw [he.encoded, hscale]
  simpa only [norm_sub_rev] using herr

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
