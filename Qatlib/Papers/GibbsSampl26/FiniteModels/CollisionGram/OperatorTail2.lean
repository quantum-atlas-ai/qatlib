/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.CollisionGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for the trailing coordinates of operator row 2 in the fast chart

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

/-- Balanced real and imaginary base/base Gram coefficients on row 11. -/
private theorem r11BB :
    (∀ j, gramBBRealBalanced 11 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 11 j) ∧
    (∀ j, gramBBImagBalanced 11 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 11 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 11. -/
private theorem r11BU :
    (∀ j, gramBURealBalanced 11 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 11 j) ∧
    (∀ j, gramBUImagBalanced 11 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 11 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 11. -/
private theorem r11BV :
    (∀ j, gramBVRealBalanced 11 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 11 j) ∧
    (∀ j, gramBVImagBalanced 11 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 11 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 11. -/
private theorem r11UU :
    (∀ j, gramUURealBalanced 11 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 11 j) ∧
    (∀ j, gramUUImagBalanced 11 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 11 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 11. -/
private theorem r11UV :
    (∀ j, gramUVRealBalanced 11 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 11 j) ∧
    (∀ j, gramUVImagBalanced 11 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 11 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 11. -/
private theorem r11VV :
    (∀ j, gramVVRealBalanced 11 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 11 j) ∧
    (∀ j, gramVVImagBalanced 11 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 11 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 11. -/
private theorem certifiedRow11 :
    (∀ j, gramBBReal 11 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 11 j) ∧
    (∀ j, gramBBImag 11 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 11 j) ∧
    (∀ j, gramBUReal 11 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 11 j) ∧
    (∀ j, gramBUImag 11 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 11 j) ∧
    (∀ j, gramBVReal 11 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 11 j) ∧
    (∀ j, gramBVImag 11 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 11 j) ∧
    (∀ j, gramUUReal 11 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 11 j) ∧
    (∀ j, gramUUImag 11 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 11 j) ∧
    (∀ j, gramUVReal 11 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 11 j) ∧
    (∀ j, gramUVImag 11 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 11 j) ∧
    (∀ j, gramVVReal 11 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 11 j) ∧
    (∀ j, gramVVImag 11 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 11 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r11BB.1, r11BB.2, r11BU.1, r11BU.2, r11BV.1, r11BV.2, r11UU.1, r11UU.2, r11UV.1, r11UV.2, r11VV.1, r11VV.2⟩

/-- Balanced real and imaginary base/base Gram coefficients on row 12. -/
private theorem r12BB :
    (∀ j, gramBBRealBalanced 12 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 12 j) ∧
    (∀ j, gramBBImagBalanced 12 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 12 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 12. -/
private theorem r12BU :
    (∀ j, gramBURealBalanced 12 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 12 j) ∧
    (∀ j, gramBUImagBalanced 12 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 12 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 12. -/
private theorem r12BV :
    (∀ j, gramBVRealBalanced 12 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 12 j) ∧
    (∀ j, gramBVImagBalanced 12 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 12 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 12. -/
private theorem r12UU :
    (∀ j, gramUURealBalanced 12 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 12 j) ∧
    (∀ j, gramUUImagBalanced 12 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 12 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 12. -/
private theorem r12UV :
    (∀ j, gramUVRealBalanced 12 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 12 j) ∧
    (∀ j, gramUVImagBalanced 12 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 12 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 12. -/
private theorem r12VV :
    (∀ j, gramVVRealBalanced 12 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 12 j) ∧
    (∀ j, gramVVImagBalanced 12 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 12 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 12. -/
private theorem certifiedRow12 :
    (∀ j, gramBBReal 12 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 12 j) ∧
    (∀ j, gramBBImag 12 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 12 j) ∧
    (∀ j, gramBUReal 12 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 12 j) ∧
    (∀ j, gramBUImag 12 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 12 j) ∧
    (∀ j, gramBVReal 12 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 12 j) ∧
    (∀ j, gramBVImag 12 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 12 j) ∧
    (∀ j, gramUUReal 12 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 12 j) ∧
    (∀ j, gramUUImag 12 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 12 j) ∧
    (∀ j, gramUVReal 12 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 12 j) ∧
    (∀ j, gramUVImag 12 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 12 j) ∧
    (∀ j, gramVVReal 12 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 12 j) ∧
    (∀ j, gramVVImag 12 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 12 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r12BB.1, r12BB.2, r12BU.1, r12BU.2, r12BV.1, r12BV.2, r12UU.1, r12UU.2, r12UV.1, r12UV.2, r12VV.1, r12VV.2⟩

/-- All twelve complete-source Gram identities on the trailing coordinates of operator row 2 in the fast chart. -/
theorem operatorTail2 (i : Fin 15) (hi : 11 ≤ i.val ∧ i.val < 13) :
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
  · norm_num at hi
  · norm_num at hi
  · exact certifiedRow11
  · exact certifiedRow12
  · norm_num at hi
  · norm_num at hi

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables.Balanced
