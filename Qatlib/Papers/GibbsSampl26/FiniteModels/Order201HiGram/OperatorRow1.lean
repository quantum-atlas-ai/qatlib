/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order201HiGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for the leading coordinates of operator row 1 in the fast chart

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

/-- Balanced real and imaginary base/base Gram coefficients on row 5. -/
private theorem r5BB :
    (∀ j, gramBBRealBalanced 5 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 5 j) ∧
    (∀ j, gramBBImagBalanced 5 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 5 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 5. -/
private theorem r5BU :
    (∀ j, gramBURealBalanced 5 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 5 j) ∧
    (∀ j, gramBUImagBalanced 5 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 5 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 5. -/
private theorem r5BV :
    (∀ j, gramBVRealBalanced 5 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 5 j) ∧
    (∀ j, gramBVImagBalanced 5 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 5 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 5. -/
private theorem r5UU :
    (∀ j, gramUURealBalanced 5 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 5 j) ∧
    (∀ j, gramUUImagBalanced 5 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 5 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 5. -/
private theorem r5UV :
    (∀ j, gramUVRealBalanced 5 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 5 j) ∧
    (∀ j, gramUVImagBalanced 5 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 5 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 5. -/
private theorem r5VV :
    (∀ j, gramVVRealBalanced 5 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 5 j) ∧
    (∀ j, gramVVImagBalanced 5 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 5 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 5. -/
private theorem certifiedRow5 :
    (∀ j, gramBBReal 5 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 5 j) ∧
    (∀ j, gramBBImag 5 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 5 j) ∧
    (∀ j, gramBUReal 5 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 5 j) ∧
    (∀ j, gramBUImag 5 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 5 j) ∧
    (∀ j, gramBVReal 5 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 5 j) ∧
    (∀ j, gramBVImag 5 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 5 j) ∧
    (∀ j, gramUUReal 5 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 5 j) ∧
    (∀ j, gramUUImag 5 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 5 j) ∧
    (∀ j, gramUVReal 5 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 5 j) ∧
    (∀ j, gramUVImag 5 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 5 j) ∧
    (∀ j, gramVVReal 5 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 5 j) ∧
    (∀ j, gramVVImag 5 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 5 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r5BB.1, r5BB.2, r5BU.1, r5BU.2, r5BV.1, r5BV.2, r5UU.1, r5UU.2, r5UV.1, r5UV.2, r5VV.1, r5VV.2⟩

/-- Balanced real and imaginary base/base Gram coefficients on row 6. -/
private theorem r6BB :
    (∀ j, gramBBRealBalanced 6 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 6 j) ∧
    (∀ j, gramBBImagBalanced 6 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 6 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 6. -/
private theorem r6BU :
    (∀ j, gramBURealBalanced 6 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 6 j) ∧
    (∀ j, gramBUImagBalanced 6 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 6 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 6. -/
private theorem r6BV :
    (∀ j, gramBVRealBalanced 6 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 6 j) ∧
    (∀ j, gramBVImagBalanced 6 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 6 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 6. -/
private theorem r6UU :
    (∀ j, gramUURealBalanced 6 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 6 j) ∧
    (∀ j, gramUUImagBalanced 6 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 6 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 6. -/
private theorem r6UV :
    (∀ j, gramUVRealBalanced 6 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 6 j) ∧
    (∀ j, gramUVImagBalanced 6 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 6 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 6. -/
private theorem r6VV :
    (∀ j, gramVVRealBalanced 6 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 6 j) ∧
    (∀ j, gramVVImagBalanced 6 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 6 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 6. -/
private theorem certifiedRow6 :
    (∀ j, gramBBReal 6 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 6 j) ∧
    (∀ j, gramBBImag 6 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 6 j) ∧
    (∀ j, gramBUReal 6 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 6 j) ∧
    (∀ j, gramBUImag 6 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 6 j) ∧
    (∀ j, gramBVReal 6 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 6 j) ∧
    (∀ j, gramBVImag 6 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 6 j) ∧
    (∀ j, gramUUReal 6 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 6 j) ∧
    (∀ j, gramUUImag 6 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 6 j) ∧
    (∀ j, gramUVReal 6 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 6 j) ∧
    (∀ j, gramUVImag 6 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 6 j) ∧
    (∀ j, gramVVReal 6 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 6 j) ∧
    (∀ j, gramVVImag 6 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 6 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r6BB.1, r6BB.2, r6BU.1, r6BU.2, r6BV.1, r6BV.2, r6UU.1, r6UU.2, r6UV.1, r6UV.2, r6VV.1, r6VV.2⟩

/-- All twelve complete-source Gram identities on the leading coordinates of operator row 1 in the fast chart. -/
theorem operatorRow1 (i : Fin 15) (hi : 5 ≤ i.val ∧ i.val < 7) :
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
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · exact certifiedRow5
  · exact certifiedRow6
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables.Balanced
