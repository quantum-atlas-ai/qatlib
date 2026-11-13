/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation

/-!
# Frobenius stability of Hermitian matrix functions

This module defines `hermitianFunction` by evaluating a scalar function in an ordered
orthonormal eigenbasis. It proves a Frobenius perturbation bound from Lipschitz bounds on
cross-pairs of eigenvalues and identifies polynomial spectral evaluation with matrix polynomial
evaluation, in the setting of [Bhatia1997].

## Main statements

* `hermitian_spectral_function_frobenius_stability`: transfers cross-pair scalar bounds to a
  matrix Frobenius bound.
* `hermitian_spectral_polynomial_evaluation`: identifies spectral and algebraic polynomial
  evaluation.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The matrix obtained by applying `f` to the ordered eigenvalues of the Hermitian matrix `A`
in its ordered orthonormal eigenbasis. -/
noncomputable def hermitianFunction {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ→ℂ) : Matrix I I ℂ :=
  spectralDiagonal (orderedHermitianBasis hA) (fun i=> f (orderedHermitianValues hA i))

/-- If `f` satisfies the stated Lipschitz bound with nonnegative constant `L` on every
cross-pair of eigenvalues of Hermitian matrices `A` and `B`, then their spectral function
values differ in Frobenius norm by at most `L * spectralFrobenius (A - B)`. -/
theorem hermitian_spectral_function_frobenius_stability : ∀ (I : Type) [Fintype I]
    [DecidableEq I] (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ→ℂ) (L : ℝ),0≤L →
    (∀ i j,‖f (orderedHermitianValues hA i)-f (orderedHermitianValues hB j)‖≤
      L*|orderedHermitianValues hA i-orderedHermitianValues hB j|) →
    spectralFrobenius (hermitianFunction A hA f-hermitianFunction B hB f)≤
      L*spectralFrobenius (A-B) := by
  intro I _ _ A B hA hB f L hL hLip
  let a := orderedHermitianValues hA
  let b := orderedHermitianValues hB
  let W : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ := fun i j =>
    Complex.normSq (((basisColumns (orderedHermitianBasis hA))ᴴ*
      basisColumns (orderedHermitianBasis hB)) i j)
  have hreal := spectralFrobenius_cross_difference (orderedHermitianBasis hA)
    (orderedHermitianBasis hB) (fun i => (a i : ℂ)) (fun j => (b j : ℂ))
  rw [← orderedHermitian_diagonal hA,← orderedHermitian_diagonal hB] at hreal
  have hAB : spectralFrobenius (A-B)^2=∑ i,∑ j,W i j*(a i-b j)^2 := by
    simpa only [← Complex.ofReal_sub,Complex.normSq_ofReal,pow_two] using hreal
  have hcomplex : spectralFrobenius (hermitianFunction A hA f-hermitianFunction B hB f)^2=
      ∑ i,∑ j,W i j*Complex.normSq (f (a i)-f (b j)) :=
    spectralFrobenius_cross_difference (orderedHermitianBasis hA) (orderedHermitianBasis hB)
      (fun i => f (a i)) (fun j => f (b j))
  have hpoint (i j : Fin (Fintype.card I)) :
      Complex.normSq (f (a i)-f (b j))≤L^2*(a i-b j)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (abs_nonneg _))).mpr (hLip i j)
    simpa only [mul_pow,sq_abs] using hsq
  apply (sq_le_sq₀ (spectralFrobenius_nonneg _) (mul_nonneg hL (spectralFrobenius_nonneg _))).mp
  rw [hcomplex,mul_pow,hAB]
  calc
    (∑ i,∑ j,W i j*Complex.normSq (f (a i)-f (b j)))≤
        ∑ i,∑ j,W i j*(L^2*(a i-b j)^2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hpoint i j) (Complex.normSq_nonneg _)))
    _=L^2*(∑ i,∑ j,W i j*(a i-b j)^2) := by
      simp only [Finset.mul_sum,mul_left_comm,mul_assoc]

/-- Applying a real polynomial through the Hermitian spectral decomposition equals algebraic
evaluation of its complex coefficient embedding at the matrix. -/
theorem hermitian_spectral_polynomial_evaluation : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (p : Polynomial ℝ),
    hermitianFunction A hA (fun x=>((p.eval x:ℝ):ℂ))=aeval A (p.map Complex.ofRealHom) := by
  intro I _ _ A hA p
  rw [aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hA) A _
    (orderedHermitianBasis_action hA)]
  unfold hermitianFunction
  congr 1
  funext i
  exact (Polynomial.eval_map_apply (p := p) Complex.ofRealHom
    (orderedHermitianValues hA i)).symm

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
