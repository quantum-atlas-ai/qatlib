/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.TruncatedSketchSecondIsometryStat
import Qatlib.Concepts.SketchSpectral.SketchPerturb.SketchSingularValueStabilitySamp

/-!
# Near-isometry of a thresholded second sketch

`truncatedSketchSecondIsometry` controls the Gram matrix obtained by inverse-singular-value
scaling on the retained singular subspace. A Frobenius Gram error bounded by `τ² * α` yields
operator-norm distance at most `α` from the threshold projector, as used in the sketch
constructions of [ChiaEtAl2022].

## Main statements

* `truncatedSketchSecondIsometry`: If the Gram approximation error is at most `τ² * α`,
  thresholded inverse-singular-value scaling makes the transformed Gram matrix differ from the
  retained-coordinate projector by operator norm at most `α`. See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.SketchSpectral.SketchPerturb
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- If the Gram approximation error is at most `τ² * α`, thresholded inverse-singular-value
scaling makes the transformed Gram matrix differ from the retained-coordinate projector by
operator norm at most `α`. See [ChiaEtAl2022]. -/
theorem truncatedSketchSecondIsometry : TruncatedSketchSecondIsometry := by
  intro C RS CT _ _ _ _ _ _ R Cc τ α η hτ _hα hη hclose hbound
  let Z := basisColumns (rightSingularBasis Ccᴴ)
  let g : Fin (Fintype.card RS) → ℂ := fun i =>
    if τ ≤ matrixSingularValues Cc i then ((matrixSingularValues Cc i)⁻¹ : ℂ) else 0
  let e : Fin (Fintype.card RS) → ℂ := fun i => if τ ≤ matrixSingularValues Cc i then 1 else 0
  let D := diagonal g
  let P := D*Zᴴ
  have hZ : ‖Z‖ ≤ 1 := basisColumns_norm_le _
  have hD : ‖D‖ ≤ 1/τ := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    dsimp only [g]
    split_ifs with h
    · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hτ.trans_le h).le]
      simpa only [one_div] using one_div_le_one_div_of_le hτ h
    · simp only [norm_zero]
      positivity
  have hP : ‖P‖ ≤ 1/τ := by
    apply (Matrix.l2_opNorm_mul D Zᴴ).trans
    rw [Matrix.l2_opNorm_conjTranspose]
    exact (mul_le_mul hD hZ (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hb : orderedHermitianBasis (Matrix.isHermitian_mul_conjTranspose_self Cc) =
      rightSingularBasis Ccᴴ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using (singular_gram_ordered Ccᴴ).1
  have he := orderedHermitian_diagonal (Matrix.isHermitian_mul_conjTranspose_self Cc)
  rw [hb] at he
  simp only [spectralDiagonal] at he
  simp_rw [sketchSingularValueStability_outer_gram RS CT Cc, Complex.ofReal_pow] at he
  have hd : Zᴴ*(Cc*Ccᴴ)*Z =
      diagonal (fun i : Fin (Fintype.card RS) => (matrixSingularValues Cc i : ℂ)^2) := by
    rw [he]
    change Zᴴ*(Z*diagonal _*Zᴴ)*Z = _
    have hunit : Zᴴ*Z = 1 := basisColumns_adjoint_mul _
    calc
      _ = (Zᴴ*Z)*diagonal (fun i : Fin (Fintype.card RS) => (matrixSingularValues Cc i : ℂ)^2)*(Zᴴ*Z) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hunit]; simp
  have hs (i : Fin (Fintype.card RS)) :
      g i*(matrixSingularValues Cc i : ℂ)^2*star (g i) = e i := by
    dsimp only [g,e]
    split_ifs with h
    · have hne : (matrixSingularValues Cc i : ℂ) ≠ 0 :=
        by exact_mod_cast (hτ.trans_le h).ne'
      simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
      field_simp
    · simp
  have hproj : D*Zᴴ*(Cc*Ccᴴ)*Z*Dᴴ = diagonal e := by
    calc
      _ = D*(Zᴴ*(Cc*Ccᴴ)*Z)*Dᴴ := by simp only [Matrix.mul_assoc]
      _ = D*diagonal (fun i : Fin (Fintype.card RS) => (matrixSingularValues Cc i : ℂ)^2)*Dᴴ := by rw [hd]
      _ = diagonal e := by
        rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
            Matrix.diagonal_mul_diagonal]
        exact congrArg diagonal (funext hs)
  change ‖D*Zᴴ*R*Rᴴ*Z*Dᴴ-diagonal e‖ ≤ α
  have hΔ : ‖R*Rᴴ-Cc*Ccᴴ‖ ≤ η := by
    rw [norm_sub_rev]
    exact (spectral_operator_norm_le_frobenius _).trans hclose
  have herr : D*Zᴴ*R*Rᴴ*Z*Dᴴ-diagonal e = P*(R*Rᴴ-Cc*Ccᴴ)*Pᴴ := by
    rw [← hproj]
    simp only [P, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [herr]
  calc
    _ ≤ (‖P‖*‖R*Rᴴ-Cc*Ccᴴ‖)*‖Pᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1/τ)*η*(1/τ) := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = η/(τ*τ) := by ring
    _ ≤ α := (div_le_iff₀ (mul_pos hτ hτ)).mpr (by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound)

end Qatlib.Concepts.SketchSpectral.EvenSVT
