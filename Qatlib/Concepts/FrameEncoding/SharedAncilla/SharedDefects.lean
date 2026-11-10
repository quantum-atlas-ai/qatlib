/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FrameEncoding.SharedAncilla.SharedAncillaDefs
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.FrameEncoding.SharedAncilla

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Qatlib.Concepts.FrameEncoding.SharedAncilla

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
variable {F : Matrix H I ℂ}

theorem shared_defect_identity {A : Matrix I I ℂ} {U : Matrix H H ℂ} (F : Matrix H I ℂ)
    (hF : IsIsometry F) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    (U * F - F * A)ᴴ * (U * F - F * A)
      = (Fᴴ * F - Aᴴ * A)
        + (Aᴴ * (A - compress F U F) + (A - compress F U F)ᴴ * A) := by
  have hU' : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hU.1
  have hF' : Fᴴ * F = 1 := hF
  have hUF : (U * F)ᴴ * (U * F) = Fᴴ * F := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U F, hU',
      Matrix.one_mul]
  have hFA : (F * A)ᴴ * (F * A) = Aᴴ * A := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F A, hF',
      Matrix.one_mul]
  have hXA : (U * F)ᴴ * (F * A) = (compress F U F)ᴴ * A := by
    simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      Matrix.conjTranspose_conjTranspose]
  have hYA : (F * A)ᴴ * (U * F) = Aᴴ * compress F U F := by
    simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hsub : Aᴴ * (A - compress F U F) = Aᴴ * A - Aᴴ * compress F U F :=
    Matrix.mul_sub Aᴴ A (compress F U F)
  have hsub' : (A - compress F U F)ᴴ * A
      = (Aᴴ - (compress F U F)ᴴ) * A := by
    rw [Matrix.conjTranspose_sub]
  have hsub'' : (Aᴴ - (compress F U F)ᴴ) * A
      = Aᴴ * A - (compress F U F)ᴴ * A :=
    Matrix.sub_mul Aᴴ (compress F U F)ᴴ A
  calc
    (U * F - F * A)ᴴ * (U * F - F * A)
        = (U * F)ᴴ * (U * F) - (U * F)ᴴ * (F * A)
            - ((F * A)ᴴ * (U * F) - (F * A)ᴴ * (F * A)) := by
          rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    _ = Fᴴ * F - (compress F U F)ᴴ * A - (Aᴴ * compress F U F - Aᴴ * A) := by
          rw [hUF, hFA, hXA, hYA]
    _ = (Fᴴ * F - Aᴴ * A)
          + (Aᴴ * (A - compress F U F) + (A - compress F U F)ᴴ * A) := by
          rw [hsub, hsub', hsub'']
          abel

theorem shared_defect_bound_le {A : Matrix I I ℂ} {U : Matrix H H ℂ} (F : Matrix H I ℂ)
    (hF : IsIsometry F) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (α ε ζ Γ : ℝ) (hζ : 0 ≤ ζ) (hΓ : 0 ≤ Γ)
    (hgram : ‖(1 : Matrix I I ℂ) - Aᴴ * A‖ ≤ ζ)
    (hmismatch : ‖A - compress F U F‖ ≤ |1 - α| + ε)
    (hA : ‖A‖ ≤ Γ) :
    ‖U * F - F * A‖ * ‖U * F - F * A‖ ≤ ζ + 2 * Γ * (|1 - α| + ε) := by
  have hid := shared_defect_identity (A := A) (U := U) F hF hU
  have hF' : Fᴴ * F = 1 := hF
  have hsq : ‖U * F - F * A‖ * ‖U * F - F * A‖
      = ‖(U * F - F * A)ᴴ * (U * F - F * A)‖ := by
    symm
    exact Matrix.l2_opNorm_conjTranspose_mul_self (U * F - F * A)
  rw [hsq, hid]
  have hg : ‖Fᴴ * F - Aᴴ * A‖ ≤ ζ := by
    have hkey : Fᴴ * F - Aᴴ * A = (1 : Matrix I I ℂ) - Aᴴ * A := by rw [hF']
    rw [hkey]
    exact hgram
  have h1 : ‖Aᴴ * (A - compress F U F)‖ ≤ ‖A‖ * ‖A - compress F U F‖ := by
    have h := Matrix.l2_opNorm_mul Aᴴ (A - compress F U F)
    rwa [Matrix.l2_opNorm_conjTranspose] at h
  have h2 : ‖(A - compress F U F)ᴴ * A‖ ≤ ‖A - compress F U F‖ * ‖A‖ := by
    have h := Matrix.l2_opNorm_mul (A - compress F U F)ᴴ A
    rwa [Matrix.l2_opNorm_conjTranspose] at h
  have h3 : ‖A - compress F U F‖ ≤ |1 - α| + ε := hmismatch
  calc
    ‖(Fᴴ * F - Aᴴ * A)
          + (Aᴴ * (A - compress F U F) + (A - compress F U F)ᴴ * A)‖
        ≤ ‖Fᴴ * F - Aᴴ * A‖
          + ‖Aᴴ * (A - compress F U F) + (A - compress F U F)ᴴ * A‖ :=
          norm_add_le (Fᴴ * F - Aᴴ * A)
            (Aᴴ * (A - compress F U F) + (A - compress F U F)ᴴ * A)
    _ ≤ ‖Fᴴ * F - Aᴴ * A‖ + ‖Aᴴ * (A - compress F U F)‖
          + ‖(A - compress F U F)ᴴ * A‖ := by
            have hn := norm_add_le (Aᴴ * (A - compress F U F))
              ((A - compress F U F)ᴴ * A)
            linarith
    _ ≤ ζ + Γ * (|1 - α| + ε) + (|1 - α| + ε) * Γ := by
          have hnpe : 0 ≤ |1 - α| + ε :=
            le_trans (norm_nonneg (A - compress F U F)) h3
          have e1 : ‖Aᴴ * (A - compress F U F)‖ ≤ Γ * (|1 - α| + ε) :=
            le_trans h1 (mul_le_mul hA h3 (norm_nonneg (A - compress F U F)) hΓ)
          have e2 : ‖(A - compress F U F)ᴴ * A‖ ≤ (|1 - α| + ε) * Γ :=
            le_trans h2 (mul_le_mul h3 hA (norm_nonneg A) hnpe)
          linarith
    _ = ζ + 2 * Γ * (|1 - α| + ε) := by ring

theorem GuardedSharedBlock.defect_le (b : GuardedSharedBlock H I F) :
    ‖b.U * F - F * b.A‖ * ‖b.U * F - F * b.A‖ ≤ b.defectBound := by
  have h := shared_defect_bound_le (A := b.A) (U := b.U) F b.frame_isometry
    b.workspace_unitary b.α b.ε b.ζ b.Γ b.ζ_nonneg b.Γ_nonneg b.gram_le
    (by
      have hn : ‖b.A - compress F b.U F‖ = ‖compress F b.U F - b.A‖ := by
        rw [← neg_sub, norm_neg]
      rw [hn]
      simpa only [GuardedSharedBlock.mismatch, sharedMismatchBound] using b.mismatch_le)
    b.Γ_ge
  simpa only [GuardedSharedBlock.defectBound, GuardedSharedBlock.mismatch,
    sharedMismatchBound] using h

theorem GuardedSharedBlock.defect_norm_le (b : GuardedSharedBlock H I F) :
    ‖b.U * F - F * b.A‖ ≤ b.defect := by
  have h4 := b.defect_le
  have h6 : 0 ≤ b.defectBound := b.defectBound_nonneg
  have h6' : 0 ≤ b.defect := by
    unfold GuardedSharedBlock.defect
    exact Real.sqrt_nonneg _
  have h7 : b.defect * b.defect = b.defectBound := by
    unfold GuardedSharedBlock.defect
    calc
      Real.sqrt b.defectBound * Real.sqrt b.defectBound = (Real.sqrt b.defectBound) ^ 2 := by ring
      _ = b.defectBound := Real.sq_sqrt h6
  have hsq2 : ‖b.U * F - F * b.A‖ ^ 2 ≤ b.defect ^ 2 := by
    rw [pow_two, pow_two, h7]
    exact h4
  exact (sq_le_sq₀ (norm_nonneg (b.U * F - F * b.A)) h6').mp hsq2

theorem GuardedSharedBlock.leak_le (b : GuardedSharedBlock H I F) :
    ‖sharedComplement F * b.U * F‖ ≤ b.defect := by
  have hQ : sharedComplement F * F = 0 := sharedComplement_mul_F F b.frame_isometry
  have h1 : sharedComplement F * (b.U * F - F * b.A) = sharedComplement F * b.U * F := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc (sharedComplement F) F b.A, hQ, Matrix.zero_mul,
      sub_zero, Matrix.mul_assoc]
  have h2 : ‖sharedComplement F‖ ≤ 1 := sharedComplement_norm_le_one F b.frame_isometry
  have h3 : ‖sharedComplement F * (b.U * F - F * b.A)‖
      ≤ ‖sharedComplement F‖ * ‖b.U * F - F * b.A‖ := Matrix.l2_opNorm_mul _ _
  have h3' : ‖sharedComplement F‖ * ‖b.U * F - F * b.A‖
      ≤ ‖b.U * F - F * b.A‖ := by
    have hmul := mul_le_mul_of_nonneg_right h2 (norm_nonneg (b.U * F - F * b.A))
    simpa using hmul
  have h4 := b.defect_le
  have h6 : 0 ≤ b.defectBound := b.defectBound_nonneg
  have h6' : 0 ≤ b.defect := by
    unfold GuardedSharedBlock.defect
    exact Real.sqrt_nonneg _
  have h7 : b.defect * b.defect = b.defectBound := by
    unfold GuardedSharedBlock.defect
    calc
      Real.sqrt b.defectBound * Real.sqrt b.defectBound = (Real.sqrt b.defectBound) ^ 2 := by ring
      _ = b.defectBound := Real.sq_sqrt h6
  have h8 : ‖b.U * F - F * b.A‖ ≤ b.defect := by
    have hsq2 : ‖b.U * F - F * b.A‖ ^ 2 ≤ b.defect ^ 2 := by
      rw [pow_two, pow_two, h7]
      exact h4
    exact (sq_le_sq₀ (norm_nonneg (b.U * F - F * b.A)) h6').mp hsq2
  rw [← h1]
  linarith

theorem GuardedSharedBlock.leak_adjoint_le (b : GuardedSharedBlock H I F) :
    ‖Fᴴ * b.U * sharedComplement F‖ ≤ b.defect := by
  have h1 : ‖Fᴴ * b.U * sharedComplement F‖ = ‖sharedComplement F * b.Uᴴ * F‖ := by
    have he : Fᴴ * b.U * sharedComplement F
        = (sharedComplement F * b.Uᴴ * F)ᴴ := by
      simp [sharedComplement, Matrix.conjTranspose_mul, Matrix.mul_assoc,
        Matrix.conjTranspose_conjTranspose]
    rw [he, Matrix.l2_opNorm_conjTranspose]
  have hQ : sharedComplement F * F = 0 := sharedComplement_mul_F F b.frame_isometry
  have h2 : sharedComplement F * b.Uᴴ * F
      = sharedComplement F * (b.Uᴴ * F - F * b.Aᴴ) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc (sharedComplement F) F b.Aᴴ, hQ,
      Matrix.zero_mul, sub_zero, Matrix.mul_assoc]
  have h3 : ‖sharedComplement F‖ ≤ 1 := sharedComplement_norm_le_one F b.frame_isometry
  have h4 : ‖sharedComplement F * (b.Uᴴ * F - F * b.Aᴴ)‖
      ≤ ‖sharedComplement F‖ * ‖b.Uᴴ * F - F * b.Aᴴ‖ := Matrix.l2_opNorm_mul _ _
  have h4' : ‖sharedComplement F‖ * ‖b.Uᴴ * F - F * b.Aᴴ‖
      ≤ ‖b.Uᴴ * F - F * b.Aᴴ‖ := by
    have hmul := mul_le_mul_of_nonneg_right h3 (norm_nonneg (b.Uᴴ * F - F * b.Aᴴ))
    simpa using hmul

  have hc : compress F b.Uᴴ F = (compress F b.U F)ᴴ := by
    simp [compress, Matrix.mul_assoc]
  have hgram : ‖(1 : Matrix I I ℂ) - (b.Aᴴ)ᴴ * (b.Aᴴ)‖ ≤ b.ζ := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact b.gramT_le
  have herr : ‖b.Aᴴ - b.α • compress F b.Uᴴ F‖ ≤ b.ε := by
    have hkey : b.Aᴴ - b.α • compress F b.Uᴴ F
        = (b.A - b.α • compress F b.U F)ᴴ := by
      rw [hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial]
    rw [hkey, Matrix.l2_opNorm_conjTranspose]
    exact b.error_le
  have hA : ‖b.Aᴴ‖ ≤ b.Γ := by
    have hkey : ‖b.Aᴴ‖ = ‖b.A‖ := Matrix.l2_opNorm_conjTranspose b.A
    rw [hkey]
    exact b.Γ_ge
  have hmis : ‖b.Aᴴ - compress F b.Uᴴ F‖ ≤ |1 - b.α| + b.ε := by
    have hkey : b.Aᴴ - compress F b.Uᴴ F
        = (b.A - compress F b.U F)ᴴ := by
      rw [hc, Matrix.conjTranspose_sub]
    rw [hkey, Matrix.l2_opNorm_conjTranspose]
    have hn : ‖b.A - compress F b.U F‖ = ‖compress F b.U F - b.A‖ := by
      rw [← neg_sub, norm_neg]
    rw [hn]
    simpa only [GuardedSharedBlock.mismatch, sharedMismatchBound] using b.mismatch_le
  have h5 := shared_defect_bound_le (A := b.Aᴴ) (U := b.Uᴴ) F b.frame_isometry
    (adjoint_unitary b.workspace_unitary) b.α b.ε b.ζ b.Γ b.ζ_nonneg b.Γ_nonneg
    hgram hmis hA
  have h6 : 0 ≤ b.defectBound := b.defectBound_nonneg
  have h6' : 0 ≤ b.defect := by
    unfold GuardedSharedBlock.defect
    exact Real.sqrt_nonneg _
  have h7 : b.defect * b.defect = b.defectBound := by
    unfold GuardedSharedBlock.defect
    calc
      Real.sqrt b.defectBound * Real.sqrt b.defectBound = (Real.sqrt b.defectBound) ^ 2 := by ring
      _ = b.defectBound := Real.sq_sqrt h6
  have h8 : ‖b.Uᴴ * F - F * b.Aᴴ‖ ≤ b.defect := by
    have hsq2 : ‖b.Uᴴ * F - F * b.Aᴴ‖ ^ 2 ≤ b.defect ^ 2 := by
      rw [pow_two, pow_two, h7]
      exact h5
    exact (sq_le_sq₀ (norm_nonneg (b.Uᴴ * F - F * b.Aᴴ)) h6').mp hsq2
  rw [h1, h2]
  linarith

end Qatlib.Concepts.FrameEncoding.SharedAncilla
