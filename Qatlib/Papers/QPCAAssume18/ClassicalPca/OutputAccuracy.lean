/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.NativeSpectrum
import Qatlib.Papers.QPCAAssume18.ClassicalPca.LiftResidual
import Qatlib.Foundations.MatrixAlgebra.SpectralPerturb

/-!
# Phase accuracy of lifted PCA outputs

Defines the singular-value-scaled PCA output and its target right singular vector. Rescaling
estimates and isolation in the native Hermitian spectrum convert Gram perturbations into a
vector error bound up to complex phase, supporting [Tang2021].

## Main statements

* `pca_output_rescale`: The scaled PCA output differs from the normalized adjoint lift by at
  most `eta / pcaSmallValue W i` under the stated positivity and Gram error assumptions.
* `pca_output_phase`: Under the stated gap, eigenvalue proximity, and Gram error bounds, the PCA
  output is within the explicit rescaling-plus-residual error of the target vector up to a unit
  complex phase [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SketchSpectral.SketchPerturb
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Foundations.MatrixAlgebra.SpectralPerturb.PhaseResidual

/-- The adjoint lift of a small-sketch eigenvector divided by the square root of its squared
singular value. -/
def pcaOutput {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) : EuclideanSpace ℂ (Fin d) :=
  (Real.sqrt (pcaSmallValue W i) : ℂ)⁻¹ • Rᴴ.toEuclideanLin (pcaSmallVector W i)

/-- The ordered unit eigenvector of `Aᴴ * A` at index `i`. -/
def pcaTarget {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) (i : Fin d) :
    EuclideanSpace ℂ (Fin d) :=
  orderedHermitianBasis (Matrix.isHermitian_conjTranspose_mul_self A) (pcaNativeIndex i)

/-- If `a ≥ 0`, `mu > 0`, and `a^2` is within `eta` of `mu`, then `a / sqrt mu` is within `eta /
mu` of one. -/
theorem pca_sqrt_rescale (a mu eta : ℝ) (ha : 0 ≤ a) (hmu : 0 < mu)
    (herr : |a ^ 2 - mu| ≤ eta) : |a / Real.sqrt mu - 1| ≤ eta / mu := by
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hsq := Real.sq_sqrt hmu.le
  have hprod : |a / Real.sqrt mu - 1| * (Real.sqrt mu * (a + Real.sqrt mu)) = |a ^ 2 - mu| := by
    have hid : (a / Real.sqrt mu - 1) * (Real.sqrt mu * (a + Real.sqrt mu)) = a ^ 2 - mu := by
      field_simp
      nlinarith
    rw [← abs_of_nonneg (mul_nonneg hs.le (by positivity)), ← abs_mul, hid]
  have hden : mu ≤ Real.sqrt mu * (a + Real.sqrt mu) := by nlinarith
  apply (le_div_iff₀ hmu).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (abs_nonneg (a / Real.sqrt mu - 1))]

/-- The scaled PCA output differs from the normalized adjoint lift by at most `eta /
pcaSmallValue W i` under the stated positivity and Gram error assumptions. -/
theorem pca_output_rescale {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (eta : ℝ)
    (hmu : 0 < pcaSmallValue W i)
    (hx : 0 < ‖Rᴴ.toEuclideanLin (pcaSmallVector W i)‖)
    (hgram : spectralFrobenius (W * Wᴴ - R * Rᴴ) ≤ eta) :
    ‖pcaOutput R W i - pcaUnitLift R (pcaSmallVector W i)‖ ≤ eta / pcaSmallValue W i := by
  let x := Rᴴ.toEuclideanLin (pcaSmallVector W i)
  have hid : pcaOutput R W i =
      ((‖x‖ / Real.sqrt (pcaSmallValue W i) : ℝ) : ℂ) • pcaUnitLift R (pcaSmallVector W i) := by
    have hxC : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hscalar : (Real.sqrt (pcaSmallValue W i) : ℂ)⁻¹ =
        ((‖x‖ / Real.sqrt (pcaSmallValue W i) : ℝ) : ℂ) * (‖x‖ : ℂ)⁻¹ := by
      rw [Complex.ofReal_div]
      field_simp
    exact (congrArg (fun z : ℂ => z • x) hscalar).trans
      (smul_smul (((‖x‖ / Real.sqrt (pcaSmallValue W i) : ℝ) : ℂ)) ((‖x‖ : ℂ)⁻¹) x).symm
  have hdiff : (↑(‖x‖ / Real.sqrt (pcaSmallValue W i)) : ℂ) • pcaUnitLift R (pcaSmallVector W i) -
      pcaUnitLift R (pcaSmallVector W i) =
      ((↑(‖x‖ / Real.sqrt (pcaSmallValue W i)) : ℂ) - 1) • pcaUnitLift R (pcaSmallVector W i) := by module
  rw [hid, hdiff, norm_smul,
    pcaUnitLift_norm R (pcaSmallVector W i) hx, mul_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact pca_sqrt_rescale ‖x‖ (pcaSmallValue W i) eta (norm_nonneg _) hmu
    (pca_lift_norm_error R W (pcaSmallVector W i) (pcaSmallValue W i) eta
      (pcaSmallVector_norm W i) (pcaSmallVector_action W i) hgram)

/-- Consecutive squared-singular-value gaps on a retained prefix isolate its corresponding
native Hermitian eigenvalue from every other eigenvalue by at least `g`. -/
theorem pca_native_gap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) (k : ℕ) (g : ℝ)
    (hgap : ∀ i ∈ Finset.range k,
      g ≤ matrixSingularValues A i ^ 2 - matrixSingularValues A (i + 1) ^ 2)
    (i : Fin d) (hik : i.val < k)
    (j : Fin (Fintype.card (Fin d))) (hne : j ≠ pcaNativeIndex i) :
    g ≤ |orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) j -
      orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) (pcaNativeIndex i)| := by
  apply pca_antitone_prefix_isolation _
    (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀_antitone k g ?_ _ hik j hne
  intro l hl hnext
  change g ≤ orderedHermitianValues _ l - orderedHermitianValues _ ⟨l.val + 1, hnext⟩
  rw [(singular_gram_ordered A).2 l, (singular_gram_ordered A).2 ⟨l.val + 1, hnext⟩]
  exact hgap l.val (Finset.mem_range.mpr hl)

/-- Under the stated gap, eigenvalue proximity, and Gram error bounds, the PCA output is within
the explicit rescaling-plus-residual error of the target vector up to a unit complex phase
[Tang2021]. -/
theorem pca_output_phase {n q d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (R : Matrix (Fin q) (Fin d) ℂ) (W : Matrix (Fin q) (Fin q) ℂ)
    (k : ℕ) (i : Fin d) (iq : Fin q) (hik : i.val < k)
    (sigma g etaRow etaCol : ℝ) (hsigma : 0 < sigma) (hg : 0 < g)
    (hgap : ∀ l ∈ Finset.range k,
      g ≤ matrixSingularValues A l ^ 2 - matrixSingularValues A (l + 1) ^ 2)
    (hmu : sigma ^ 2 / 2 ≤ pcaSmallValue W iq) (heta : etaCol ≤ sigma ^ 2 / 4)
    (hclose : |pcaSmallValue W iq - matrixSingularValues A i ^ 2| ≤ g / 2)
    (hrow : spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ etaRow)
    (hcol : spectralFrobenius (W * Wᴴ - R * Rᴴ) ≤ etaCol) :
    ∃ zeta : ℂ, ‖zeta‖ = 1 ∧
      ‖pcaOutput R W iq - zeta • pcaTarget A i‖ ≤
        etaCol / pcaSmallValue W iq + (4 / g) * (etaRow + 2 * ‖R‖ * etaCol / sigma) := by
  have hx := pca_lift_norm_lower R W (pcaSmallVector W iq) (pcaSmallValue W iq)
    etaCol sigma (pcaSmallVector_norm W iq) (pcaSmallVector_action W iq) hcol hsigma hmu heta
  have hxpos : 0 < ‖Rᴴ.toEuclideanLin (pcaSmallVector W iq)‖ := by linarith
  have hmuPos : 0 < pcaSmallValue W iq := lt_of_lt_of_le (by positivity) hmu
  have hc : |pcaSmallValue W iq - orderedHermitianValues
      (Matrix.isHermitian_conjTranspose_mul_self A) (pcaNativeIndex i)| ≤ g / 2 := by
    rw [(singular_gram_ordered A).2]
    exact hclose
  obtain ⟨zeta, hzeta, hphase⟩ := residual_phase_bound
    (orderedHermitianBasis (Matrix.isHermitian_conjTranspose_mul_self A)) (Aᴴ * A).toEuclideanLin
    (orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A))
    (orderedHermitianBasis_action (Matrix.isHermitian_conjTranspose_mul_self A))
    (pcaUnitLift R (pcaSmallVector W iq)) (pcaUnitLift_norm R _ hxpos)
    (pcaNativeIndex i) g (pcaSmallValue W iq) hg (pca_native_gap A k g hgap i hik) hc
  refine ⟨zeta, hzeta, ?_⟩
  calc
    _ ≤ ‖pcaOutput R W iq - pcaUnitLift R (pcaSmallVector W iq)‖ +
        ‖pcaUnitLift R (pcaSmallVector W iq) - zeta • pcaTarget A i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (pca_output_rescale R W iq etaCol hmuPos hxpos hcol)
      (hphase.trans (mul_le_mul_of_nonneg_left
        (pcaUnitLift_residual A R W (pcaSmallVector W iq) (pcaSmallValue W iq)
          etaRow etaCol sigma (pcaSmallVector_norm W iq) (pcaSmallVector_action W iq)
          hrow hcol hsigma hmu heta) (by positivity)))

end Qatlib.Papers.QPCAAssume18.ClassicalPca
