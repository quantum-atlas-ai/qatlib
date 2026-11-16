/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.CollisionGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for the leading coordinates of operator row 2 in the fast chart

The row indices follow ThreeLevelCoordinateMetric.fullCoordinates and
ThreeLevelCornerFastChart.fastCoordinates. Each row retains all twelve real
and imaginary identities against the complete original source matrices.
Each coefficient pair is checked separately, then the six pairs are assembled
using the table equalities, bounding the kernel reduction context.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables.Balanced
open Matrix
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Balanced real and imaginary base/base Gram coefficients on row 9. -/
private theorem r9BB :
    (∀ j, gramBBRealBalanced 9 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 9 j) ∧
    (∀ j, gramBBImagBalanced 9 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 9 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 9. -/
private theorem r9BU :
    (∀ j, gramBURealBalanced 9 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 9 j) ∧
    (∀ j, gramBUImagBalanced 9 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 9 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 9. -/
private theorem r9BV :
    (∀ j, gramBVRealBalanced 9 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 9 j) ∧
    (∀ j, gramBVImagBalanced 9 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 9 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 9. -/
private theorem r9UU :
    (∀ j, gramUURealBalanced 9 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 9 j) ∧
    (∀ j, gramUUImagBalanced 9 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 9 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 9. -/
private theorem r9UV :
    (∀ j, gramUVRealBalanced 9 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 9 j) ∧
    (∀ j, gramUVImagBalanced 9 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 9 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 9. -/
private theorem r9VV :
    (∀ j, gramVVRealBalanced 9 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 9 j) ∧
    (∀ j, gramVVImagBalanced 9 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 9 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 9. -/
private theorem certifiedRow9 :
    (∀ j, gramBBReal 9 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 9 j) ∧
    (∀ j, gramBBImag 9 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 9 j) ∧
    (∀ j, gramBUReal 9 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 9 j) ∧
    (∀ j, gramBUImag 9 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 9 j) ∧
    (∀ j, gramBVReal 9 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 9 j) ∧
    (∀ j, gramBVImag 9 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 9 j) ∧
    (∀ j, gramUUReal 9 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 9 j) ∧
    (∀ j, gramUUImag 9 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 9 j) ∧
    (∀ j, gramUVReal 9 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 9 j) ∧
    (∀ j, gramUVImag 9 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 9 j) ∧
    (∀ j, gramVVReal 9 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 9 j) ∧
    (∀ j, gramVVImag 9 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 9 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r9BB.1, r9BB.2, r9BU.1, r9BU.2, r9BV.1, r9BV.2, r9UU.1, r9UU.2, r9UV.1, r9UV.2, r9VV.1, r9VV.2⟩

/-- Balanced real and imaginary base/base Gram coefficients on row 10. -/
private theorem r10BB :
    (∀ j, gramBBRealBalanced 10 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 10 j) ∧
    (∀ j, gramBBImagBalanced 10 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 10 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 10. -/
private theorem r10BU :
    (∀ j, gramBURealBalanced 10 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 10 j) ∧
    (∀ j, gramBUImagBalanced 10 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 10 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 10. -/
private theorem r10BV :
    (∀ j, gramBVRealBalanced 10 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 10 j) ∧
    (∀ j, gramBVImagBalanced 10 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 10 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 10. -/
private theorem r10UU :
    (∀ j, gramUURealBalanced 10 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 10 j) ∧
    (∀ j, gramUUImagBalanced 10 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 10 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 10. -/
private theorem r10UV :
    (∀ j, gramUVRealBalanced 10 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 10 j) ∧
    (∀ j, gramUVImagBalanced 10 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 10 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 10. -/
private theorem r10VV :
    (∀ j, gramVVRealBalanced 10 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 10 j) ∧
    (∀ j, gramVVImagBalanced 10 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 10 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 10. -/
private theorem certifiedRow10 :
    (∀ j, gramBBReal 10 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 10 j) ∧
    (∀ j, gramBBImag 10 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 10 j) ∧
    (∀ j, gramBUReal 10 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 10 j) ∧
    (∀ j, gramBUImag 10 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 10 j) ∧
    (∀ j, gramBVReal 10 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 10 j) ∧
    (∀ j, gramBVImag 10 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 10 j) ∧
    (∀ j, gramUUReal 10 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 10 j) ∧
    (∀ j, gramUUImag 10 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 10 j) ∧
    (∀ j, gramUVReal 10 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 10 j) ∧
    (∀ j, gramUVImag 10 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 10 j) ∧
    (∀ j, gramVVReal 10 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 10 j) ∧
    (∀ j, gramVVImag 10 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 10 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r10BB.1, r10BB.2, r10BU.1, r10BU.2, r10BV.1, r10BV.2, r10UU.1, r10UU.2, r10UV.1, r10UV.2, r10VV.1, r10VV.2⟩

/-- All twelve complete-source Gram identities on the leading coordinates of operator row 2 in the fast chart. -/
theorem operatorRow2 (i : Fin 15) (hi : 9 ≤ i.val ∧ i.val < 11) :
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
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · exact certifiedRow9
  · exact certifiedRow10
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables.Balanced
