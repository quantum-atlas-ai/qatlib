/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.GroundLimit.GroundSpaceDamping
import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.MatrixEvolution
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.GroundSpace
open Matrix NormedSpace Filter
open Qatlib.Concepts.ImaginaryFlow.GroundLimit
open Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
open scoped BigOperators Topology Classical

section ActualMatrixGroundspace

def eigenMask {d : ℕ} {H : Op d} (hH : H.IsHermitian) (i0 : Fin d) (i : Fin d) : ℂ :=
  if hH.eigenvalues i = hH.eigenvalues i0 then 1 else 0

def eigenspaceProjector {d : ℕ} {H : Op d} (hH : H.IsHermitian) (i0 : Fin d) : Op d :=
  eigenU hH * diagonal (eigenMask hH i0) * (eigenU hH).conjTranspose

theorem eigenspaceProjector_hermitian {d : ℕ} {H : Op d} (hH : H.IsHermitian) (i0 : Fin d) :
    (eigenspaceProjector hH i0).IsHermitian := by
  have hdiag : (diagonal (eigenMask hH i0)).conjTranspose = diagonal (eigenMask hH i0) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    by_cases hi : hH.eigenvalues i = hH.eigenvalues i0 <;> simp [eigenMask, hi]
  change (eigenspaceProjector hH i0).conjTranspose = eigenspaceProjector hH i0
  simp only [eigenspaceProjector, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hdiag,
    Matrix.mul_assoc]

theorem eigenspaceProjector_idempotent {d : ℕ} {H : Op d} (hH : H.IsHermitian) (i0 : Fin d) :
    eigenspaceProjector hH i0 * eigenspaceProjector hH i0 = eigenspaceProjector hH i0 := by
  have hU : (eigenU hH).conjTranspose * eigenU hH = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.property
  have hD : diagonal (eigenMask hH i0) * diagonal (eigenMask hH i0) =
      diagonal (eigenMask hH i0) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    simp [eigenMask]
  unfold eigenspaceProjector
  calc
    _ = eigenU hH * (diagonal (eigenMask hH i0) * diagonal (eigenMask hH i0)) *
        (eigenU hH).conjTranspose := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (eigenU hH).conjTranspose (eigenU hH)
        (diagonal (eigenMask hH i0) * (eigenU hH).conjTranspose), hU, Matrix.one_mul]
    _ = _ := by rw [hD]

theorem eigenspaceProjector_eigen {d : ℕ} (H : Op d) (hH : H.IsHermitian) (i0 : Fin d) :
    H * eigenspaceProjector hH i0 =
      (hH.eigenvalues i0 : ℂ) • eigenspaceProjector hH i0 := by
  have hU : (eigenU hH).conjTranspose * eigenU hH = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.property
  have hs : H = eigenU hH * diagonal (fun i => (hH.eigenvalues i : ℂ)) *
      (eigenU hH).conjTranspose := hH.spectral_theorem
  have hD : diagonal (fun i => (hH.eigenvalues i : ℂ)) * diagonal (eigenMask hH i0) =
      (hH.eigenvalues i0 : ℂ) • diagonal (eigenMask hH i0) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    ext i
    by_cases hi : hH.eigenvalues i = hH.eigenvalues i0 <;> simp [eigenMask, hi]
  calc
    H * eigenspaceProjector hH i0 =
        (eigenU hH * diagonal (fun i => (hH.eigenvalues i : ℂ)) *
          (eigenU hH).conjTranspose) * eigenspaceProjector hH i0 :=
      congrArg (fun A : Op d => A * eigenspaceProjector hH i0) hs
    _ = eigenU hH * (diagonal (fun i => (hH.eigenvalues i : ℂ)) *
        diagonal (eigenMask hH i0)) * (eigenU hH).conjTranspose := by
      unfold eigenspaceProjector
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (eigenU hH).conjTranspose (eigenU hH)
        (diagonal (eigenMask hH i0) * (eigenU hH).conjTranspose), hU, Matrix.one_mul]
    _ = _ := by rw [hD]; simp only [eigenspaceProjector, Matrix.mul_smul, Matrix.smul_mul]

def rightGround {d : ℕ} (g : Op d) {H : Op d} (hH : H.IsHermitian)
    (φ : State d) (i0 : Fin d) : State d :=
  Matrix.toEuclideanLin (exp (-g) * eigenspaceProjector hH i0 * exp g) φ

theorem retained_rightComponents_eq_projector {d : ℕ} (g : Op d) {H : Op d} (hH : H.IsHermitian)
    (φ : State d) (i0 : Fin d) :
    retainedGround hH.eigenvalues (fun _ => 1) (rightComponent g hH φ) i0 =
      rightGround g hH φ i0 := by
  apply WithLp.ofLp_injective
  simp only [retainedGround, WithLp.ofLp_sum, apply_ite, WithLp.ofLp_zero,
    rightComponent, one_smul]
  change (∑ i, if hH.eigenvalues i = hH.eigenvalues i0 then
      coefficients g hH φ i • (exp (-g) * eigenU hH)ᵀ i else 0) =
    (exp (-g) * eigenspaceProjector hH i0 * exp g) *ᵥ φ.ofLp
  have hM : exp (-g) * eigenspaceProjector hH i0 * exp g =
      (exp (-g) * eigenU hH) * diagonal (eigenMask hH i0) *
        ((eigenU hH).conjTranspose * exp g) := by
    simp only [eigenspaceProjector, Matrix.mul_assoc]
  rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec φ.ofLp (eigenU hH).conjTranspose (exp g)]
  change _ = (exp (-g) * eigenU hH) *ᵥ
    (diagonal (eigenMask hH i0) *ᵥ coefficients g hH φ)
  have hdv : diagonal (eigenMask hH i0) *ᵥ coefficients g hH φ =
      fun i => eigenMask hH i0 i * coefficients g hH φ i := by
    ext i
    exact Matrix.mulVec_diagonal _ _ i
  rw [hdv]
  ext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : hH.eigenvalues i = hH.eigenvalues i0
  · simp only [eigenMask, if_pos hi, one_mul]
    change coefficients g hH φ i * (exp (-g) * eigenU hH) j i =
      (exp (-g) * eigenU hH) j i * coefficients g hH φ i
    ring
  · simp only [eigenMask, if_neg hi, zero_mul, mul_zero]
    rfl

theorem rightGround_eigen {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (i0 : Fin d) :
    Matrix.toEuclideanLin (tc H g) (rightGround g hH φ i0) =
      hH.eigenvalues i0 • rightGround g hH φ i0 := by
  rw [← retained_rightComponents_eq_projector]
  unfold retainedGround
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : hH.eigenvalues i = hH.eigenvalues i0
  · simp only [if_pos hi, one_smul]
    rw [rightComponent_eigen H g hH φ i, hi]
  · simp only [if_neg hi, map_zero, smul_zero]

theorem actual_normalized_groundspace_limit {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (i0 : Fin d)
    (hmin : ∀ i, hH.eigenvalues i0 ≤ hH.eigenvalues i)
    (hoverlap : rightGround g hH φ i0 ≠ 0) :
    Tendsto (fun t : ℝ => ‖actualState H g φ t‖⁻¹ • actualState H g φ t)
      atTop (𝓝 (‖rightGround g hH φ i0‖⁻¹ • rightGround g hH φ i0)) := by
  have hr : retainedGround hH.eigenvalues (fun _ => 1) (rightComponent g hH φ) i0 ≠ 0 := by
    rw [retained_rightComponents_eq_projector]
    exact hoverlap
  have h := normalized_spectral_groundspace hH.eigenvalues (fun _ => 1)
    (rightComponent g hH φ) i0 hmin hr
  simpa only [← actualState_eq_existing_spectral H g hH φ,
    retained_rightComponents_eq_projector] using h

end ActualMatrixGroundspace

end Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.GroundSpace
