/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FrameEncoding.SharedAncilla.SharedAncillaWordConsumers
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Qatlib.Concepts.FrameEncoding.SharedAncilla

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
variable {F : Matrix H I ℂ}

noncomputable def sharedComplement (F : Matrix H I ℂ) : Matrix H H ℂ :=
  1 - F * Fᴴ

theorem sharedFrame_projector (F : Matrix H I ℂ) : F * Fᴴ = rangeProjector F := rfl

theorem sharedProjector_mul_F (F : Matrix H I ℂ) (hF : IsIsometry F) :
    F * Fᴴ * F = F := rangeProjector_mul hF

theorem sharedProjector_adjoint (F : Matrix H I ℂ) (hF : IsIsometry F) :
    (F * Fᴴ)ᴴ = F * Fᴴ := by
  have hp := rangeProjector_isOrthogonalProjector hF
  exact hp.2

theorem sharedComplement_mul_F (F : Matrix H I ℂ) (hF : IsIsometry F) :
    sharedComplement F * F = 0 := by
  have h : Fᴴ * F = 1 := hF
  rw [sharedComplement, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h,
    Matrix.mul_one, sub_self]

theorem sharedComplement_mul_F_conj (F : Matrix H I ℂ) (hF : IsIsometry F) :
    Fᴴ * sharedComplement F = 0 := by
  have h : Fᴴ * F = 1 := hF
  rw [sharedComplement, Matrix.mul_sub, ← Matrix.mul_assoc Fᴴ F Fᴴ, h, Matrix.one_mul,
    Matrix.mul_one, sub_self]

theorem sharedComplement_adjoint (F : Matrix H I ℂ) (hF : IsIsometry F) :
    (sharedComplement F)ᴴ = sharedComplement F := by
  have hp : (F * Fᴴ)ᴴ = F * Fᴴ := sharedProjector_adjoint F hF
  simp only [sharedComplement, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [hp]

theorem sharedComplement_expand (F : Matrix H I ℂ) (X : Matrix H H ℂ) :
    sharedComplement F * X = X - F * Fᴴ * X := by
  rw [sharedComplement, Matrix.sub_mul, Matrix.one_mul]

theorem sharedComplement_idempotent (F : Matrix H I ℂ) (hF : IsIsometry F) :
    sharedComplement F * sharedComplement F = sharedComplement F := by
  have hp := rangeProjector_isOrthogonalProjector hF
  have hq := isOrthogonalProjector_compl hp
  have hq' : (1 - F * Fᴴ) * (1 - F * Fᴴ) = 1 - F * Fᴴ := hq.1
  unfold sharedComplement
  exact hq'

theorem sharedComplement_mul_projector (F : Matrix H I ℂ) (hF : IsIsometry F) :
    sharedComplement F * (F * Fᴴ) = 0 := by
  have hp := rangeProjector_isOrthogonalProjector hF
  have hid : (F * Fᴴ) * (F * Fᴴ) = F * Fᴴ := hp.1
  rw [sharedComplement, Matrix.sub_mul, Matrix.one_mul, hid, sub_self]

theorem sharedProjector_mul_complement (F : Matrix H I ℂ) (hF : IsIsometry F) :
    (F * Fᴴ) * sharedComplement F = 0 := by
  have hp := rangeProjector_isOrthogonalProjector hF
  have hid : (F * Fᴴ) * (F * Fᴴ) = F * Fᴴ := hp.1
  rw [sharedComplement, Matrix.mul_sub, Matrix.mul_one, hid, sub_self]

theorem sharedComplement_norm_le_one (F : Matrix H I ℂ) (hF : IsIsometry F) :
    ‖sharedComplement F‖ ≤ 1 := by
  have hp := rangeProjector_isOrthogonalProjector hF
  have hq := isOrthogonalProjector_compl hp
  have hq2 : (1 - rangeProjector F)ᴴ = 1 - rangeProjector F := by
    simpa only [Matrix.star_eq_conjTranspose] using! hq.2
  have h1 : ‖sharedComplement F‖ * ‖sharedComplement F‖ = ‖sharedComplement F‖ := by
    unfold sharedComplement
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self]
    rw [sharedFrame_projector, hq2, hq.1]
  have h2 : (0:ℝ) ≤ ‖sharedComplement F‖ := norm_nonneg _
  nlinarith

theorem l2_opNorm_one {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] :
    ‖(1 : Matrix n n ℂ)‖ = 1 := by
  have h : (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ : n => (1 : ℂ)) := by
    ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [h, Matrix.l2_opNorm_diagonal]
  have h2 : ‖(fun _ : n => (1 : ℂ))‖ = 1 := by
    rw [Pi.norm_def]
    simp only [nnnorm_one]
    rw [Finset.sup_const Finset.univ_nonempty 1]
    norm_num
  exact h2

theorem isometry_mul_norm_eq {F : Matrix H I ℂ} (hF : IsIsometry F)
    (X : Matrix I I ℂ) : ‖F * X‖ = ‖X‖ := by
  have hF' : Fᴴ * F = 1 := hF
  have h : ‖F * X‖ * ‖F * X‖ = ‖X‖ * ‖X‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.l2_opNorm_conjTranspose_mul_self]
    congr 1
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᴴ F X, hF', Matrix.one_mul]
  have h1 : (0:ℝ) ≤ ‖F * X‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖X‖ := norm_nonneg _
  nlinarith

theorem l2_opNorm_sq_add_le {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {X Y : Matrix m n ℂ} (h : Xᴴ * Y = 0) :
    ‖X + Y‖ * ‖X + Y‖ ≤ ‖X‖ * ‖X‖ + ‖Y‖ * ‖Y‖ := by
  have hcross : Yᴴ * X = 0 := by
    have hx : Yᴴ * X = (Xᴴ * Y)ᴴ := by simp [Matrix.conjTranspose_mul]
    rw [hx, h]
    simp
  have h1 : ‖X + Y‖ * ‖X + Y‖ = ‖(X + Y)ᴴ * (X + Y)‖ := by
    symm
    exact Matrix.l2_opNorm_conjTranspose_mul_self (X + Y)
  rw [h1]
  have hexp : (X + Y)ᴴ * (X + Y) = Xᴴ * X + Yᴴ * Y := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, hcross]
    simp
  rw [hexp]
  calc
    ‖Xᴴ * X + Yᴴ * Y‖ ≤ ‖Xᴴ * X‖ + ‖Yᴴ * Y‖ := norm_add_le _ _
    _ = ‖X‖ * ‖X‖ + ‖Y‖ * ‖Y‖ := by
        rw [Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.l2_opNorm_conjTranspose_mul_self]

def sharedMismatchBound (α ε : ℝ) : ℝ := |1 - α| + ε

structure GuardedSharedBlock (H I : Type) [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (F : Matrix H I ℂ) where

  A : Matrix I I ℂ

  U : Matrix H H ℂ

  α : ℝ

  α_pos : 0 < α

  ε : ℝ

  ε_nonneg : 0 ≤ ε

  γ : ℝ

  γ_pos : 0 < γ

  γ_le : γ ≤ ‖A‖

  Γ : ℝ

  Γ_nonneg : 0 ≤ Γ

  Γ_ge : ‖A‖ ≤ Γ

  ζ : ℝ

  ζ_nonneg : 0 ≤ ζ

  gram_le : ‖(1 : Matrix I I ℂ) - Aᴴ * A‖ ≤ ζ

  gramT_le : ‖(1 : Matrix I I ℂ) - A * Aᴴ‖ ≤ ζ

  frame_isometry : IsIsometry F

  workspace_unitary : U ∈ Matrix.unitaryGroup H ℂ

  error_le : ‖A - α • compress F U F‖ ≤ ε

def GuardedSharedBlock.mismatch {F : Matrix H I ℂ} (b : GuardedSharedBlock H I F) : ℝ :=
  sharedMismatchBound b.α b.ε

def GuardedSharedBlock.defectBound {F : Matrix H I ℂ} (b : GuardedSharedBlock H I F) : ℝ :=
  b.ζ + 2 * b.Γ * b.mismatch

noncomputable def GuardedSharedBlock.defect {F : Matrix H I ℂ}
    (b : GuardedSharedBlock H I F) : ℝ := Real.sqrt b.defectBound

theorem GuardedSharedBlock.mismatch_le (b : GuardedSharedBlock H I F) :
    ‖compress F b.U F - b.A‖ ≤ b.mismatch := by
  have hP : ‖compress F b.U F‖ ≤ 1 :=
    l2_norm_compress_le_one b.frame_isometry b.workspace_unitary b.frame_isometry
  have hnorm : ‖b.A - b.α • compress F b.U F‖ ≤ b.ε := b.error_le
  have hkey : compress F b.U F - b.A =
      ((1 - b.α) • compress F b.U F - (b.A - b.α • compress F b.U F)) := by
    have h1 : (1 - b.α) • compress F b.U F + b.α • compress F b.U F
        = compress F b.U F := by
      rw [← add_smul]
      simp
    have h2 : (1 - b.α) • compress F b.U F - (b.A - b.α • compress F b.U F)
        = (1 - b.α) • compress F b.U F + b.α • compress F b.U F - b.A := by abel
    rw [h2, h1]
  rw [hkey]
  have h1 : ‖(1 - b.α) • compress F b.U F‖ = |1 - b.α| * ‖compress F b.U F‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  calc
    ‖(1 - b.α) • compress F b.U F - (b.A - b.α • compress F b.U F)‖
        ≤ ‖(1 - b.α) • compress F b.U F‖ + ‖b.A - b.α • compress F b.U F‖ := by
          have hk : (1 - b.α) • compress F b.U F - (b.A - b.α • compress F b.U F)
              = (1 - b.α) • compress F b.U F + (-(b.A - b.α • compress F b.U F)) := by
                abel
          rw [hk]
          calc
            ‖(1 - b.α) • compress F b.U F + (-(b.A - b.α • compress F b.U F))‖
                ≤ ‖(1 - b.α) • compress F b.U F‖ + ‖-(b.A - b.α • compress F b.U F)‖ :=
                  norm_add_le _ _
            _ = ‖(1 - b.α) • compress F b.U F‖ + ‖b.A - b.α • compress F b.U F‖ := by
                  rw [norm_neg]
    _ ≤ |1 - b.α| + b.ε := by
          have h2 : |1 - b.α| * ‖compress F b.U F‖ ≤ |1 - b.α| * 1 :=
            mul_le_mul_of_nonneg_left hP (abs_nonneg (1 - b.α))
          linarith [h1, h2, hnorm]
    _ = b.mismatch := by rfl

theorem GuardedSharedBlock.defectBound_nonneg (b : GuardedSharedBlock H I F) :
    0 ≤ b.defectBound := by
  unfold GuardedSharedBlock.defectBound
  have h1 : 0 ≤ b.ζ := b.ζ_nonneg
  have h2 : 0 ≤ b.Γ := b.Γ_nonneg
  have h3 : 0 ≤ b.mismatch := by
    unfold GuardedSharedBlock.mismatch sharedMismatchBound
    exact add_nonneg (abs_nonneg _) b.ε_nonneg
  have h4 : 0 ≤ b.Γ * b.mismatch := mul_nonneg h2 h3
  have h5 : 0 ≤ 2 * (b.Γ * b.mismatch) := mul_nonneg (by norm_num) h4
  linarith

end Qatlib.Concepts.FrameEncoding.SharedAncilla
