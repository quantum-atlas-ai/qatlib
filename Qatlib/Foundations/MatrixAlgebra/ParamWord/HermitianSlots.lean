/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.WordBounds
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Evolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Comp
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix.Norms.L2Operator RightActions
namespace Qatlib.Foundations.MatrixAlgebra.ParamWord
open Matrix
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
local instance : CStarAlgebra (Matrix I I ℂ) where
local instance : NormedAlgebra ℝ (Matrix I I ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Matrix I I ℂ)

def hamGenerator (G : Matrix I I ℂ) : Matrix I I ℂ := (-Complex.I) • G

def expSlot {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (θ : EuclideanSpace ℝ (Fin K)) : Matrix I I ℂ :=
  NormedSpace.exp ((θ j) • hamGenerator G)*W

def expSlotD {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K)→L[ℝ]Matrix I I ℂ :=
  (EuclideanSpace.proj j).smulRight (hamGenerator G*expSlot G W j θ)

omit [Nonempty I] in

theorem expSlot_eq_evolve {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (θ : EuclideanSpace ℝ (Fin K)) : expSlot G W j θ=evolve G (θ j)*W := by
  unfold expSlot evolve
  apply congrArg (fun A : Matrix I I ℂ => NormedSpace.exp A*W)
  ext a b
  simp [hamGenerator,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  ring

theorem euclidean_proj_norm {K : ℕ} (j : Fin K) :
    ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin K)→L[ℝ]ℝ)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using! PiLp.norm_apply_le x j

omit [Nonempty I] in

theorem hamGenerator_norm (G : Matrix I I ℂ) : ‖hamGenerator G‖=‖G‖ := by
  simp [hamGenerator,norm_smul]

omit [Nonempty I] in

theorem expSlot_hasFDerivAt {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (θ : EuclideanSpace ℝ (Fin K)) : HasFDerivAt (expSlot G W j) (expSlotD G W j θ) θ := by
  have h := ((hasDerivAt_exp_smul_const' (hamGenerator G) (θ j)).mul_const W).hasFDerivAt.comp
    θ (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin K)→L[ℝ]ℝ).hasFDerivAt
  convert! h using 1
  ext v
  simp [expSlotD,expSlot,ContinuousLinearMap.comp_apply,← Matrix.mul_assoc]

omit [Nonempty I] in

theorem expSlot_unitary {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (hG : G.IsHermitian) (hW : W∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : expSlot G W j θ∈unitary (Matrix I I ℂ) := by
  rw [expSlot_eq_evolve]
  exact Submonoid.mul_mem _ (evolve_unitary G hG _) hW

theorem expSlot_norm {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (hG : G.IsHermitian) (hW : W∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖expSlot G W j θ‖=1 :=
  CStarRing.norm_of_mem_unitary (expSlot_unitary G W j hG hW θ)

theorem expSlotD_norm {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (hG : G.IsHermitian) (hGn : ‖G‖≤1) (hW : W∈Matrix.unitaryGroup I ℂ)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖expSlotD G W j θ‖≤1 := by
  have ha : ‖hamGenerator G*expSlot G W j θ‖≤1 := by
    calc
      _ ≤ ‖hamGenerator G‖*‖expSlot G W j θ‖ := norm_mul_le _ _
      _ ≤ 1 := by rw [hamGenerator_norm,expSlot_norm G W j hG hW θ,mul_one];exact hGn
  rw [expSlotD,ContinuousLinearMap.norm_smulRight_apply]
  exact (mul_le_mul (euclidean_proj_norm j) ha (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem expSlot_lipschitz {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (hG : G.IsHermitian) (hGn : ‖G‖≤1) (hW : W∈Matrix.unitaryGroup I ℂ) :
    LipschitzWith 1 (expSlot G W j) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun θ => (expSlot_hasFDerivAt G W j θ).differentiableAt)
  intro θ
  change ‖fderiv ℝ (expSlot G W j) θ‖≤(1:ℝ)
  rw [(expSlot_hasFDerivAt G W j θ).fderiv]
  exact expSlotD_norm G W j hG hGn hW θ

theorem expSlotD_lipschitz {K : ℕ} (G W : Matrix I I ℂ) (j : Fin K)
    (hG : G.IsHermitian) (hGn : ‖G‖≤1) (hW : W∈Matrix.unitaryGroup I ℂ)
    (θ η : EuclideanSpace ℝ (Fin K)) : ‖expSlotD G W j θ-expSlotD G W j η‖≤‖θ-η‖ := by
  have he : expSlotD G W j θ-expSlotD G W j η=
      (EuclideanSpace.proj j).smulRight (hamGenerator G*(expSlot G W j θ-expSlot G W j η)) := by
    ext v
    simp [expSlotD,Matrix.mul_sub,smul_sub]
  rw [he,ContinuousLinearMap.norm_smulRight_apply]
  have hp := euclidean_proj_norm j
  have hl := (expSlot_lipschitz G W j hG hGn hW).norm_sub_le θ η
  have hg : ‖hamGenerator G‖≤1 := (hamGenerator_norm G).trans_le hGn
  calc
    _ ≤ 1*(‖hamGenerator G‖*‖expSlot G W j θ-expSlot G W j η‖) :=
      mul_le_mul hp (norm_mul_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ 1*(1*‖θ-η‖) := by
      gcongr
      simpa only [NNReal.coe_one,one_mul] using hl
    _ = _ := by ring
end Qatlib.Foundations.MatrixAlgebra.ParamWord
