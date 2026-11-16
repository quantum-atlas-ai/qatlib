/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order201HiGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for the two population coordinates

The row indices follow ThreeLevelCoordinateMetric.fullCoordinates and
ThreeLevelCornerFastChart.fastCoordinates. Each row retains all twelve real
and imaginary identities against the complete original source matrices.
Each coefficient pair is checked separately, then the six pairs are assembled
using the table equalities, bounding the kernel reduction context.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables.Balanced
open Matrix
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Balanced real and imaginary base/base Gram coefficients on row 0. -/
private theorem r0BB :
    (∀ j, gramBBRealBalanced 0 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 0 j) ∧
    (∀ j, gramBBImagBalanced 0 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 0 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 0. -/
private theorem r0BU :
    (∀ j, gramBURealBalanced 0 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 0 j) ∧
    (∀ j, gramBUImagBalanced 0 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 0 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 0. -/
private theorem r0BV :
    (∀ j, gramBVRealBalanced 0 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 0 j) ∧
    (∀ j, gramBVImagBalanced 0 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 0 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 0. -/
private theorem r0UU :
    (∀ j, gramUURealBalanced 0 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 0 j) ∧
    (∀ j, gramUUImagBalanced 0 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 0 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 0. -/
private theorem r0UV :
    (∀ j, gramUVRealBalanced 0 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 0 j) ∧
    (∀ j, gramUVImagBalanced 0 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 0 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 0. -/
private theorem r0VV :
    (∀ j, gramVVRealBalanced 0 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 0 j) ∧
    (∀ j, gramVVImagBalanced 0 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 0 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 0. -/
private theorem certifiedRow0 :
    (∀ j, gramBBReal 0 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 0 j) ∧
    (∀ j, gramBBImag 0 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 0 j) ∧
    (∀ j, gramBUReal 0 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 0 j) ∧
    (∀ j, gramBUImag 0 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 0 j) ∧
    (∀ j, gramBVReal 0 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 0 j) ∧
    (∀ j, gramBVImag 0 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 0 j) ∧
    (∀ j, gramUUReal 0 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 0 j) ∧
    (∀ j, gramUUImag 0 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 0 j) ∧
    (∀ j, gramUVReal 0 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 0 j) ∧
    (∀ j, gramUVImag 0 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 0 j) ∧
    (∀ j, gramVVReal 0 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 0 j) ∧
    (∀ j, gramVVImag 0 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 0 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r0BB.1, r0BB.2, r0BU.1, r0BU.2, r0BV.1, r0BV.2, r0UU.1, r0UU.2, r0UV.1, r0UV.2, r0VV.1, r0VV.2⟩

/-- Balanced real and imaginary base/base Gram coefficients on row 1. -/
private theorem r1BB :
    (∀ j, gramBBRealBalanced 1 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 1 j) ∧
    (∀ j, gramBBImagBalanced 1 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 1 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 1. -/
private theorem r1BU :
    (∀ j, gramBURealBalanced 1 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 1 j) ∧
    (∀ j, gramBUImagBalanced 1 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 1 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 1. -/
private theorem r1BV :
    (∀ j, gramBVRealBalanced 1 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 1 j) ∧
    (∀ j, gramBVImagBalanced 1 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 1 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 1. -/
private theorem r1UU :
    (∀ j, gramUURealBalanced 1 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 1 j) ∧
    (∀ j, gramUUImagBalanced 1 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 1 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 1. -/
private theorem r1UV :
    (∀ j, gramUVRealBalanced 1 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 1 j) ∧
    (∀ j, gramUVImagBalanced 1 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 1 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 1. -/
private theorem r1VV :
    (∀ j, gramVVRealBalanced 1 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 1 j) ∧
    (∀ j, gramVVImagBalanced 1 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 1 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 1. -/
private theorem certifiedRow1 :
    (∀ j, gramBBReal 1 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 1 j) ∧
    (∀ j, gramBBImag 1 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 1 j) ∧
    (∀ j, gramBUReal 1 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 1 j) ∧
    (∀ j, gramBUImag 1 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 1 j) ∧
    (∀ j, gramBVReal 1 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 1 j) ∧
    (∀ j, gramBVImag 1 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 1 j) ∧
    (∀ j, gramUUReal 1 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 1 j) ∧
    (∀ j, gramUUImag 1 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 1 j) ∧
    (∀ j, gramUVReal 1 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 1 j) ∧
    (∀ j, gramUVImag 1 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 1 j) ∧
    (∀ j, gramVVReal 1 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 1 j) ∧
    (∀ j, gramVVImag 1 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 1 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r1BB.1, r1BB.2, r1BU.1, r1BU.2, r1BV.1, r1BV.2, r1UU.1, r1UU.2, r1UV.1, r1UV.2, r1VV.1, r1VV.2⟩

/-- All twelve complete-source Gram identities on the two population coordinates. -/
theorem populationRows (i : Fin 15) (hi : i.val < 2) :
    (∀ j, gramBBReal i j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) i j) ∧
    (∀ j, gramBBImag i j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) i j) ∧
    (∀ j, gramBUReal i j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) i j) ∧
    (∀ j, gramBUImag i j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) i j) ∧
    (∀ j, gramBVReal i j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) i j) ∧
    (∀ j, gramBVImag i j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) i j) ∧
    (∀ j, gramUUReal i j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) i j) ∧
    (∀ j, gramUUImag i j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) i j) ∧
    (∀ j, gramUVReal i j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) i j) ∧
    (∀ j, gramUVImag i j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) i j) ∧
    (∀ j, gramVVReal i j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) i j) ∧
    (∀ j, gramVVImag i j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) i j) := by
  fin_cases i
  · exact certifiedRow0
  · exact certifiedRow1
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables.Balanced
