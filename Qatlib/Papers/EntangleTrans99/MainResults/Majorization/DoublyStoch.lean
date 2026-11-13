/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EntangleTrans99.MainResults.Majorization.PermMix
import Qatlib.Papers.EntangleTrans99.MainResults.TTransform.Basic
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Doubly stochastic mixing of spectra

This module proves that a finite real vector majorizes its image under a doubly stochastic
matrix, using a convex decomposition into permutation matrices. This supplies a spectral mixing
ingredient for the entanglement criterion of [Nielsen1999].

In dimension two, `exists_tTransform_eq_mulVec_of_doublyStochastic_two` expresses the matrix
action as a single T-transform with mixing parameter in the unit interval.

## Main statements

* `majorizes_mulVec_doublyStochastic`: proves majorization under doubly stochastic mixing.
* `exists_tTransform_eq_mulVec_of_doublyStochastic_two`: represents two-dimensional mixing by a
  T-transform.

## References

* [Nielsen, 1999][Nielsen1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Majorization

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Papers.EntangleTrans99.MainResults.TTransform
open Matrix
open scoped BigOperators

/-- A finite real vector majorizes its image under a doubly stochastic matrix [Nielsen1999]. -/
theorem majorizes_mulVec_doublyStochastic {n : ℕ} (a : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D ∈ doublyStochastic ℝ (Fin n)) :
    Majorizes a (D *ᵥ a) := by
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  have hmix : D *ᵥ a = permMix w a := by
    rw [← hwD, Matrix.sum_mulVec]
    funext j
    simp only [Matrix.smul_mulVec, Matrix.permMatrix_mulVec, permMix, Finset.sum_apply,
      Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [hmix]
  exact majorizes_permMix a w hw0 hw1

/-- The action of a two-dimensional doubly stochastic matrix on any real vector equals a
T-transform with a parameter in `[0, 1]` [Nielsen1999]. -/
theorem exists_tTransform_eq_mulVec_of_doublyStochastic_two
    (a : Fin 2 → ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D ∈ doublyStochastic ℝ (Fin 2)) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, D *ᵥ a = tTransformSpectrum a θ 0 1 := by
  classical
  have hrow0 : D 0 0 + D 0 1 = 1 := by
    simpa [Fin.sum_univ_two] using sum_row_of_mem_doublyStochastic hD 0
  have hrow1 : D 1 0 + D 1 1 = 1 := by
    simpa [Fin.sum_univ_two] using sum_row_of_mem_doublyStochastic hD 1
  have hcol0 : D 0 0 + D 1 0 = 1 := by
    simpa [Fin.sum_univ_two] using sum_col_of_mem_doublyStochastic hD 0
  have h00 : 0 ≤ D 0 0 := nonneg_of_mem_doublyStochastic hD
  have h01 : 0 ≤ D 0 1 := nonneg_of_mem_doublyStochastic hD
  have hθ1 : D 0 0 ≤ 1 := by linarith
  refine ⟨D 0 0, ⟨h00, hθ1⟩, ?_⟩
  funext j
  have hD01 : D 0 1 = 1 - D 0 0 := by linarith
  have hD10 : D 1 0 = 1 - D 0 0 := by linarith
  have hD11 : D 1 1 = D 0 0 := by linarith
  fin_cases j
  · change (D *ᵥ a) 0 = tTransformSpectrum a (D 0 0) 0 1 0
    rw [tTransformSpectrum_zero]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD01]
  · change (D *ᵥ a) 1 = tTransformSpectrum a (D 0 0) 0 1 1
    rw [tTransformSpectrum_one]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD10, hD11]

end Qatlib.Papers.EntangleTrans99.MainResults.Majorization
