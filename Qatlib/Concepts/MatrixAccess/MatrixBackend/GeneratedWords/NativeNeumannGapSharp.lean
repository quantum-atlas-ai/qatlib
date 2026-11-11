/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapInverse
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapContraction
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapInvertibility
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.RandCompile.ChannelBudget

/-! Explicit gap-stable Neumann polynomial error. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Gap-stable perturbation of the actual Neumann polynomial.  The only
spectral input is a lower singular-value bound for the ideal S; actual X's
inverse and defect gap are derived. The estimate is valid in empty dimension
and for all b, including b = 0. -/
theorem leftDefectNeumann_gap_perturbation_sharp
    (X S : Matrix I I ℂ) (K δ : ℝ) (b : ℕ)
    (hK : 1 ≤ K) (hX : ‖X‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), K⁻¹ ≤ matrixSingularValues S i)
    (hδ : ‖X-S‖ ≤ δ) (hsmall : δ ≤ 1/(4*K^2)) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b-Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b‖ ≤
      (2*K^2+4*K^3)*δ := by
  have hKpos : 0 < K := by linarith
  have ha : 0 < K⁻¹ := inv_pos.mpr hKpos
  have ha1 : K⁻¹ ≤ 1 := (inv_le_one₀ hKpos).mpr hK
  have hsmall' : δ ≤ (K⁻¹)^2/4 := by
    convert hsmall using 1
    field_simp
  have hnorm : 0 ≤ δ := (norm_nonneg (X-S)).trans hδ
  have hdef := left_defects_common_gap X S K⁻¹ δ ha ha1 hX hS hgap hδ hsmall'
  have hinv := perturbed_gap_two_sided_inverses X S K⁻¹ δ ha ha1 hgap hδ hsmall'
  let ZX := matrixPseudoinverse X
  let ZS := matrixPseudoinverse S
  let r : ℝ := 1-(K⁻¹)^2/2
  have hZX : ‖ZX‖ ≤ 2*K := by simpa only [ZX, inv_inv] using hinv.2.2.2.2.2
  have hZS : ‖ZS‖ ≤ K := by simpa only [ZS, inv_inv] using hinv.2.2.1
  have hg := leftDefectNeumann_gap_perturbation X S ZX ZS r b hdef.2.2.2 hX hS
    hinv.2.2.2.1 hinv.1 hinv.2.1 hdef.1 hdef.2.1
  have hdeninv : (1-r)⁻¹ = 2*K^2 := by
    dsimp [r]
    field_simp [ne_of_gt hKpos]
    ring
  have hfactor : ‖ZX‖*‖ZS‖ + 2*‖ZS‖/(1-r) ≤ 2*K^2+4*K^3 := by
    have hm := mul_le_mul hZX hZS (norm_nonneg ZS) (by positivity : 0 ≤ 2*K)
    rw [div_eq_mul_inv, hdeninv]
    nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hZS)]
  have hf : 0 ≤ 2*K^2+4*K^3 := by positivity
  calc
    _ ≤ (‖ZX‖*‖ZS‖ + 2*‖ZS‖/(1-r))*‖X-S‖ := hg
    _ ≤ (2*K^2+4*K^3)*‖X-S‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ ≤ (2*K^2+4*K^3)*δ := mul_le_mul_of_nonneg_left hδ hf

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
