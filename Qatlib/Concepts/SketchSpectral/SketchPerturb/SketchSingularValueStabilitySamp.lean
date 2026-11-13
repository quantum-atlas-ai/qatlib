/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.SketchPerturb.SketchSingularValueStabilityStat
import Qatlib.Concepts.WalkSearch.Spectral.Approximation

/-!
# Squared singular value bounds from two sketch Gram errors

This module proves `SketchSingularValueStability`, a pointwise perturbation bound for squared
singular values of two-stage sketches. Frobenius bounds `η₁` and `η₂` on the two Gram
differences yield error at most 2η₁ + 2η₂ over the specified index range, in the setting of
[ChiaEtAl2022].

The proof relates both inner and outer Gram spectra to squared singular values using ordered
Hermitian eigenvalues.

## Main statements

* `sketchSingularValueStability_inner`: a single inner Gram perturbation bound.
* `sketchSingularValueStability_outer_gram`: the outer Gram eigenvalue identity.
* `sketchSingularValueStability`: the combined two-stage bound.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SketchSpectral.SketchPerturb
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A Frobenius bound `η` on RᴴR - AᴴA bounds each squared singular value difference by `η` at
indices below the number of columns. -/
theorem sketchSingularValueStability_inner
    (K C RS : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (η : ℝ)
    (hη : spectralFrobenius (Rᴴ*R-Aᴴ*A) ≤ η) (i : ℕ) (hi : i < Fintype.card C) :
    |(matrixSingularValues R i)^2-(matrixSingularValues A i)^2| ≤ η := by
  let j : Fin (Fintype.card C) := ⟨i, hi⟩
  have hw := (ordered_hermitian_weyl_and_hoffman_wielandt C (Rᴴ*R) (Aᴴ*A)
    (Matrix.isHermitian_conjTranspose_mul_self R) (Matrix.isHermitian_conjTranspose_mul_self A)).1 j
  rw [(singular_gram_ordered R).2 j, (singular_gram_ordered A).2 j] at hw
  exact hw.trans ((spectral_operator_norm_le_frobenius _).trans hη)

/-- A decreasing eigenvalue family with a corresponding orthonormal eigenbasis equals the
canonical ordered Hermitian eigenvalue family. -/
private theorem ordered_values_of_basis (I : Type) [Fintype I] [DecidableEq I]
    (T : Matrix I I ℂ) (hT : T.IsHermitian)
    (b : OrthonormalBasis (Fin (Fintype.card I)) ℂ (EuclideanSpace ℂ I))
    (ev : Fin (Fintype.card I) → ℝ) (hev : Antitone ev)
    (hb : ∀ i, T.toEuclideanLin (b i) = (ev i:ℂ) • b i) :
    orderedHermitianValues hT = ev := by
  let ht := Matrix.isSymmetric_toEuclideanLin_iff.mpr hT
  have hm : LinearMap.toMatrix b.toBasis b.toBasis T.toEuclideanLin = diagonal (fun i => (ev i:ℂ)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
    rw [hb,inner_smul_right,b.inner_eq_ite]
    by_cases hij : i=j
    · subst j; simp
    · simp [hij]
  have hchar : T.toEuclideanLin.charpoly = ∏ i, (X-C (ev i:ℂ)) := by
    rw [← LinearMap.charpoly_toMatrix T.toEuclideanLin b.toBasis,hm,Matrix.charpoly_diagonal]
  have hr : T.toEuclideanLin.charpoly.roots = Multiset.map (fun i => (ev i:ℂ)) Finset.univ.val := by
    rw [hchar,Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero])]
    simp
  have hs := ht.sort_roots_charpoly_eq_eigenvalues finrank_euclideanSpace
  rw [hr] at hs
  simp only [Multiset.map_map] at hs
  simp only [Function.comp_def] at hs
  rw [Fin.univ_val_map,Multiset.coe_sort] at hs
  change (List.ofFn ev).mergeSort (fun a b => decide (a ≥ b)) =
    List.ofFn (ht.eigenvalues finrank_euclideanSpace) at hs
  have hsort : (List.ofFn ev).mergeSort (fun a b => decide (a ≥ b)) = List.ofFn ev := by
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq,← List.sortedGE_iff_pairwise]
    exact hev.sortedGE_ofFn
  rw [hsort] at hs
  apply List.ofFn_inj.mp
  exact hs.symm

/-- The ordered eigenvalues of AAᴴ are the squared singular values of `A`, indexed over its row
dimension. -/
theorem sketchSingularValueStability_outer_gram
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) :
    ∀ i : Fin (Fintype.card O),
      orderedHermitianValues (Matrix.isHermitian_mul_conjTranspose_self A) i = (matrixSingularValues A i)^2 := by
  intro i
  apply congrFun (a := i)
  apply ordered_values_of_basis O (A*Aᴴ) (Matrix.isHermitian_mul_conjTranspose_self A)
    (leftSingularBasis A) (fun i => (matrixSingularValues A i)^2)
  · intro i j hij
    apply pow_le_pow_left₀ (matrixSingularValues_nonneg A j)
    exact A.toEuclideanLin.singularValues_antitone (by exact_mod_cast hij)
  · intro i
    simpa only [Complex.ofReal_pow] using leftGram_apply_leftSingularBasis A i

/-- Two nonnegative Frobenius Gram error bounds `η₁` and `η₂` give squared singular value error
at most 2η₁ + 2η₂ at the indices specified by `SketchSingularValueStability`. See
[ChiaEtAl2022]. -/
theorem sketchSingularValueStability : SketchSingularValueStability := by
  intro K C RS CT _ _ _ _ _ _ _ _ A R Cc η₁ η₂ hη₁ hη₂ h₁ h₂ i hi
  have hiRS : i < Fintype.card RS := lt_of_lt_of_le hi (min_le_left _ _)
  have hiC : i < Fintype.card C := lt_of_lt_of_le hi (min_le_right _ _)
  have hw := (ordered_hermitian_weyl_and_hoffman_wielandt RS (Cc*Ccᴴ) (R*Rᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self Cc) (Matrix.isHermitian_mul_conjTranspose_self R)).1 ⟨i,hiRS⟩
  rw [sketchSingularValueStability_outer_gram RS CT Cc,
    sketchSingularValueStability_outer_gram RS C R] at hw
  have ho := hw.trans ((spectral_operator_norm_le_frobenius _).trans h₂)
  have hin := sketchSingularValueStability_inner K C RS A R η₁ h₁ i hiC
  have ht :=
      abs_sub_le ((matrixSingularValues Cc i)^2) ((matrixSingularValues R i)^2)
      ((matrixSingularValues A i)^2)
  nlinarith only [ho,hin,ht,hη₁,hη₂]

end Qatlib.Concepts.SketchSpectral.SketchPerturb
