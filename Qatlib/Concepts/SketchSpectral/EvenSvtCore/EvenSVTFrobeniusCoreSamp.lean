/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSvtCore.EvenSVTFrobeniusCoreStat
import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferSamp

/-!
# Frobenius error core for even SVT

The module proves Frobenius triangle, adjoint, and mixed operator-product estimates, including a
bound for the sandwich `Rᴴ * X * R`. These estimates establish `evenSVTFrobeniusCore_proof`,
which propagates the two Gram errors through the matrix functions appearing in even singular
value transformation [ChiaEtAl2022].

## Main statements

* `frobenius_operator_product_bounds`: Both mixed operator- and Frobenius-norm product bounds
  hold for `A * B`. See [ChiaEtAl2022].
* `gram_sandwich_frobenius_bound`: The Frobenius norm of `Rᴴ * X * R` is at most `‖Rᴴ * R‖`
  times the Frobenius norm of `X`.
* `evenSVTFrobeniusCore_proof`: Under spectral consistency, cross-spectrum Lipschitz bounds, and
  two Gram error bounds, the even-SVT sandwich has Frobenius error at most `L * η₁ + W * (Lbar *
  η₂)`. See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.EvenSvtCore

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- The spectral Frobenius norm equals the Euclidean norm of the matrix entries flattened over
the product index type. -/
private theorem frobenius_flat {O I : Type} [Fintype O] [Fintype I] (A : Matrix O I ℂ) :
    spectralFrobenius A = ‖WithLp.toLp 2 (fun p : O × I => A p.1 p.2)‖ := by
  apply (sq_eq_sq₀ (spectralFrobenius_nonneg _) (norm_nonneg _)).mp
  rw [spectralFrobenius_sq, EuclideanSpace.norm_sq_eq]
  simp only [Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]

/-- The spectral Frobenius norm satisfies the triangle inequality. -/
private theorem frobenius_add {O I : Type} [Fintype O] [Fintype I] (A B : Matrix O I ℂ) :
    spectralFrobenius (A + B) ≤ spectralFrobenius A + spectralFrobenius B := by
  rw [frobenius_flat, frobenius_flat A, frobenius_flat B]
  exact norm_add_le (WithLp.toLp 2 (fun p : O × I => A p.1 p.2))
    (WithLp.toLp 2 (fun p : O × I => B p.1 p.2))

/-- Conjugate transpose preserves the spectral Frobenius norm. -/
private theorem frobenius_adjoint {O I : Type} [Fintype O] [Fintype I] (A : Matrix O I ℂ) :
    spectralFrobenius Aᴴ = spectralFrobenius A := by
  apply (sq_eq_sq₀ (spectralFrobenius_nonneg _) (spectralFrobenius_nonneg _)).mp
  rw [spectralFrobenius_sq, spectralFrobenius_sq]
  simp only [Matrix.conjTranspose_apply, Complex.normSq_eq_norm_sq, norm_star]
  exact Finset.sum_comm

/-- The spectral Frobenius norm of a matrix sum is at most the sum of the two norms. See
[ChiaEtAl2022]. -/
theorem frobenius_add_bound {O I : Type} [Fintype O] [Fintype I]
    (A B : Matrix O I ℂ) :
    spectralFrobenius (A + B) ≤ spectralFrobenius A + spectralFrobenius B :=
  frobenius_add A B

/-- The spectral Frobenius norm is invariant under conjugate transpose. See [ChiaEtAl2022]. -/
theorem frobenius_adjoint_eq {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) : spectralFrobenius Aᴴ = spectralFrobenius A :=
  frobenius_adjoint A

/-- Negating a matrix preserves its spectral Frobenius norm. See [ChiaEtAl2022]. -/
theorem frobenius_neg_eq {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) : spectralFrobenius (-A) = spectralFrobenius A := by
  rw [frobenius_flat, frobenius_flat]
  exact norm_neg (WithLp.toLp 2 (fun p : O × I => A p.1 p.2))

/-- The Frobenius norm of `A * B` is at most the operator norm of `A` times the Frobenius norm
of `B`. -/
private theorem frobenius_mul_left {O I J : Type} [Fintype O] [Fintype I] [Fintype J]
    [DecidableEq I] (A : Matrix O I ℂ) (B : Matrix I J ℂ) :
    spectralFrobenius (A * B) ≤ ‖A‖ * spectralFrobenius B := by
  have hcol (j : J) : (∑ i : O, Complex.normSq ((A * B) i j)) ≤
      ‖A‖^2 * (∑ i : I, Complex.normSq (B i j)) := by
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun i => B i j))
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa [mul_pow, EuclideanSpace.norm_sq_eq, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Complex.normSq_eq_norm_sq] using hs
  apply (sq_le_sq₀ (spectralFrobenius_nonneg _)
    (mul_nonneg (norm_nonneg _) (spectralFrobenius_nonneg _))).mp
  rw [mul_pow, spectralFrobenius_sq, spectralFrobenius_sq, Finset.sum_comm]
  calc
    _ ≤ ∑ j : J, ‖A‖^2 * (∑ i : I, Complex.normSq (B i j)) :=
      Finset.sum_le_sum (fun j _hj => hcol j)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- The Frobenius norm of `A * B` is at most the Frobenius norm of `A` times the operator norm
of `B`. -/
private theorem frobenius_mul_right {O I J : Type} [Fintype O] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix O I ℂ) (B : Matrix I J ℂ) :
    spectralFrobenius (A * B) ≤ spectralFrobenius A * ‖B‖ := by
  rw [← frobenius_adjoint (A * B), Matrix.conjTranspose_mul]
  exact (frobenius_mul_left Bᴴ Aᴴ).trans_eq (by
    rw [Matrix.l2_opNorm_conjTranspose, frobenius_adjoint, mul_comm])

/-- Both mixed operator- and Frobenius-norm product bounds hold for `A * B`. See [ChiaEtAl2022]. -/
theorem frobenius_operator_product_bounds {O I J : Type}
    [Fintype O] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix O I ℂ) (B : Matrix I J ℂ) :
    spectralFrobenius (A * B) ≤ ‖A‖ * spectralFrobenius B ∧
      spectralFrobenius (A * B) ≤ spectralFrobenius A * ‖B‖ :=
  ⟨frobenius_mul_left A B, frobenius_mul_right A B⟩

/-- The Frobenius norm of `Rᴴ * X * R` is at most `‖Rᴴ * R‖` times the Frobenius norm of `X`. -/
theorem gram_sandwich_frobenius_bound {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (R : Matrix K C ℂ) (X : Matrix K K ℂ) :
    spectralFrobenius (Rᴴ * X * R) ≤ ‖Rᴴ * R‖ * spectralFrobenius X := by
  rw [Matrix.mul_assoc]
  calc
    _ ≤ ‖Rᴴ‖ * spectralFrobenius (X * R) := frobenius_mul_left Rᴴ (X * R)
    _ ≤ ‖Rᴴ‖ * (spectralFrobenius X * ‖R‖) :=
      mul_le_mul_of_nonneg_left (frobenius_mul_right X R) (norm_nonneg _)
    _ = _ := by rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]; ring

/-- Under spectral consistency, cross-spectrum Lipschitz bounds, and two Gram error bounds, the
even-SVT sandwich has Frobenius error at most `L * η₁ + W * (Lbar * η₂)`. See
[ChiaEtAl2022]. -/
theorem evenSVTFrobeniusCore_proof : EvenSVTFrobeniusCore := by
  intro K C RS CT _ _ _ _ _ _ _ _ A R Cc f fbar L Lbar η₁ η₂ W
    hL hLb _hη₁ _hη₂ hcons hLip hLipb hE₁ hE₂ hW
  let hR := Matrix.isHermitian_conjTranspose_mul_self R
  let hA := Matrix.isHermitian_conjTranspose_mul_self A
  let hRR := Matrix.isHermitian_mul_conjTranspose_self R
  let hCc := Matrix.isHermitian_mul_conjTranspose_self Cc
  let shift := fun x : ℝ => f x - f 0
  have hconsistent : hermitianFunction (Rᴴ * R) hR (fun x => fbar x * x) =
      hermitianFunction (Rᴴ * R) hR shift := by
    unfold hermitianFunction
    congr 1
    funext i
    exact hcons i
  have hfirst : spectralFrobenius (hermitianFunction (Rᴴ * R) hR shift -
      hermitianFunction (Aᴴ * A) hA shift) ≤ L * η₁ := by
    have h := hermitian_spectral_function_frobenius_stability C (Rᴴ * R) (Aᴴ * A) hR hA shift L hL
      (fun i j => by simpa [shift, sub_sub_sub_cancel_right] using hLip i j)
    exact h.trans (mul_le_mul_of_nonneg_left hE₁ hL)
  let X := hermitianFunction (Cc * Ccᴴ) hCc fbar - hermitianFunction (R * Rᴴ) hRR fbar
  have hsecond : spectralFrobenius X ≤ Lbar * η₂ :=
    (hermitian_spectral_function_frobenius_stability RS (Cc * Ccᴴ) (R * Rᴴ) hCc hRR fbar Lbar hLb hLipb).trans
      (mul_le_mul_of_nonneg_left hE₂ hLb)
  have hsandwich : spectralFrobenius (Rᴴ * X * R) ≤ W * (Lbar * η₂) :=
    (gram_sandwich_frobenius_bound R X).trans
      (mul_le_mul hW hsecond (spectralFrobenius_nonneg _) ((norm_nonneg (Rᴴ * R)).trans hW))
  have heq : Rᴴ * hermitianFunction (Cc * Ccᴴ) hCc fbar * R -
      hermitianFunction (Aᴴ * A) hA shift =
        (hermitianFunction (Rᴴ * R) hR shift - hermitianFunction (Aᴴ * A) hA shift) + Rᴴ * X * R := by
    dsimp only [X]
    rw [Matrix.mul_sub, Matrix.sub_mul, svtGramTransfer_proof RS C R fbar, hconsistent]
    abel
  rw [heq]
  exact (frobenius_add _ _).trans (add_le_add hfirst hsandwich)

end Qatlib.Concepts.SketchSpectral.EvenSvtCore
