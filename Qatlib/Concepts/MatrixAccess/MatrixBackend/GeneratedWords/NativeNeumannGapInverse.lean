/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGap
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannGapOrder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA

/-! Inverse-based perturbation of the actual left-defect polynomial. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped BigOperators Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A supplied left inverse converts the actual left-defect polynomial to a
finite inverse times a geometric complement. No normality or nonempty data
space is required. -/
theorem leftDefectNeumann_eq_inverse_complement (X Z : Matrix I I ℂ)
    (hZX : Z * X = 1) (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b = Z * (1 - (1 - X * Xᴴ)^b) := by
  let D : Matrix I I ℂ := 1 - X * Xᴴ
  have hXX : X * Xᴴ = 1-D := by dsimp [D]; noncomm_ring
  calc
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b = (Z * X) * Xᴴ * ∑ k ∈ Finset.range b, D^k := by
      rw [hZX, one_mul]
      rfl
    _ = Z * ((1-D) * ∑ k ∈ Finset.range b, D^k) := by
      rw [Matrix.mul_assoc Z X Xᴴ, hXX, Matrix.mul_assoc]
    _ = _ := by rw [mul_neg_geom_sum]

/-- A two-sided inverse perturbation identity with explicit inverse witnesses. -/
theorem inverse_difference_identity (X S ZX ZS : Matrix I I ℂ)
    (hZX : ZX * X = 1) (hSZ : S * ZS = 1) :
    ZX-ZS = ZX * (S-X) * ZS := by
  calc
    ZX-ZS = ZX*(S*ZS) - (ZX*X)*ZS := by rw [hSZ, hZX, Matrix.mul_one, Matrix.one_mul]
    _ = _ := by noncomm_ring

/-- The same explicit witnesses give the usual inverse difference norm bound. -/
theorem inverse_difference_norm_le (X S ZX ZS : Matrix I I ℂ)
    (hZX : ZX * X = 1) (hSZ : S * ZS = 1) :
    ‖ZX-ZS‖ ≤ ‖ZX‖ * ‖X-S‖ * ‖ZS‖ := by
  rw [inverse_difference_identity X S ZX ZS hZX hSZ]
  have hn : ‖S-X‖ = ‖X-S‖ := norm_sub_rev _ _
  calc
    _ ≤ ‖ZX * (S-X)‖ * ‖ZS‖ := norm_mul_le _ _
    _ ≤ (‖ZX‖ * ‖S-X‖) * ‖ZS‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by rw [hn]

/-- Inverse-based gap stability of the same finite polynomial. The strict
defect radius and inverse witnesses are explicit hypotheses; the complement
contraction follows from `hX` and is not assumed. -/
theorem leftDefectNeumann_gap_perturbation (X S ZX ZS : Matrix I I ℂ)
    (r : ℝ) (b : ℕ) (hr : r < 1) (hX : ‖X‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hZX : ZX * X = 1) (hZS : ZS * S = 1) (hSZ : S * ZS = 1)
    (hDX : ‖1-X*Xᴴ‖ ≤ r) (hDS : ‖1-S*Sᴴ‖ ≤ r) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann X b-Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b‖ ≤
      (‖ZX‖ * ‖ZS‖ + 2 * ‖ZS‖ / (1-r)) * ‖X-S‖ := by
  let DX : Matrix I I ℂ := 1-X*Xᴴ
  let DS : Matrix I I ℂ := 1-S*Sᴴ
  have hgap : 0 < 1-r := by linarith
  have hdiff : ‖DX-DS‖ ≤ 2*‖X-S‖ := by
    have he : DX-DS = -(X*Xᴴ-S*Sᴴ) := by dsimp [DX, DS]; noncomm_ring
    rw [he, norm_neg]
    have h := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_mul_sub_mul_le X Xᴴ S Sᴴ
    have hx : ‖Xᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hX
    have hd : ‖Xᴴ-Sᴴ‖ = ‖X-S‖ := by
      rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    rw [hd] at h
    have hm := mul_le_mul_of_nonneg_left hx (norm_nonneg (X-S))
    have hn := mul_le_mul_of_nonneg_right hS (norm_nonneg (X-S))
    nlinarith
  have hp : ‖DX^b-DS^b‖ ≤ 2*‖X-S‖/(1-r) := by
    have h := l2_norm_pow_sub_pow_le_of_lt_one DX DS r hr hDX hDS b
    exact h.trans (div_le_div_of_nonneg_right hdiff hgap.le)
  have hc : ‖1-DX^b‖ ≤ 1 := leftDefect_power_complement_norm_le_one X hX b
  have hi := inverse_difference_norm_le X S ZX ZS hZX hSZ
  rw [leftDefectNeumann_eq_inverse_complement X ZX hZX b,
      leftDefectNeumann_eq_inverse_complement S ZS hZS b]
  have he : ZX*(1-DX^b)-ZS*(1-DS^b) =
      (ZX-ZS)*(1-DX^b) + ZS*(DS^b-DX^b) := by noncomm_ring
  change ‖ZX*(1-DX^b)-ZS*(1-DS^b)‖ ≤ _
  rw [he]
  have h1 : ‖(ZX-ZS)*(1-DX^b)‖ ≤ ‖ZX-ZS‖ :=
    (norm_mul_le (ZX-ZS) (1-DX^b)).trans
      (by simpa using mul_le_mul_of_nonneg_left hc (norm_nonneg (ZX-ZS)))
  have h2 := norm_mul_le ZS (DS^b-DX^b)
  rw [norm_sub_rev] at h2
  have hp' := mul_le_mul_of_nonneg_left hp (norm_nonneg ZS)
  have hi' : ‖ZX-ZS‖ ≤ ‖ZX‖*‖ZS‖*‖X-S‖ := by
    exact hi.trans_eq (by ring)
  have hall := (norm_add_le ((ZX-ZS)*(1-DX^b)) (ZS*(DS^b-DX^b))).trans
    (add_le_add h1 h2)
  have hdiv : ‖ZS‖ * (2*‖X-S‖/(1-r)) =
      (2*‖ZS‖/(1-r))*‖X-S‖ := by ring
  rw [hdiv] at hp'
  nlinarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
