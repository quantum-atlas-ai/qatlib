/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.HighCollGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for the corrected final coordinate of operator row 1

Coordinate 8 represents X13 + X32/2 in fastCoordinates.
All twelve real and imaginary identities use the complete original source.
The six complex coefficient pairs are checked in separate private declarations.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionCoefficientTables.Balanced
open Matrix
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Balanced real and imaginary base/base Gram coefficients on row 8. -/
private theorem r8BB :
    (∀ j, gramBBRealBalanced 8 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 8 j) ∧
    (∀ j, gramBBImagBalanced 8 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 8 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 8. -/
private theorem r8BU :
    (∀ j, gramBURealBalanced 8 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 8 j) ∧
    (∀ j, gramBUImagBalanced 8 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 8 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 8. -/
private theorem r8BV :
    (∀ j, gramBVRealBalanced 8 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 8 j) ∧
    (∀ j, gramBVImagBalanced 8 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 8 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 8. -/
private theorem r8UU :
    (∀ j, gramUURealBalanced 8 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 8 j) ∧
    (∀ j, gramUUImagBalanced 8 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 8 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 8. -/
private theorem r8UV :
    (∀ j, gramUVRealBalanced 8 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 8 j) ∧
    (∀ j, gramUVImagBalanced 8 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 8 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 8. -/
private theorem r8VV :
    (∀ j, gramVVRealBalanced 8 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 8 j) ∧
    (∀ j, gramVVImagBalanced 8 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 8 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 8. -/
private theorem certifiedRow8 :
    (∀ j, gramBBReal 8 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 8 j) ∧
    (∀ j, gramBBImag 8 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 8 j) ∧
    (∀ j, gramBUReal 8 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 8 j) ∧
    (∀ j, gramBUImag 8 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 8 j) ∧
    (∀ j, gramBVReal 8 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 8 j) ∧
    (∀ j, gramBVImag 8 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 8 j) ∧
    (∀ j, gramUUReal 8 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 8 j) ∧
    (∀ j, gramUUImag 8 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 8 j) ∧
    (∀ j, gramUVReal 8 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 8 j) ∧
    (∀ j, gramUVImag 8 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 8 j) ∧
    (∀ j, gramVVReal 8 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 8 j) ∧
    (∀ j, gramVVImag 8 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 8 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r8BB.1, r8BB.2, r8BU.1, r8BU.2, r8BV.1, r8BV.2, r8UU.1, r8UU.2, r8UV.1, r8UV.2, r8VV.1, r8VV.2⟩

/-- All twelve complete-source Gram identities for the corrected final coordinate of operator row 1. -/
theorem operatorEntry13 (i : Fin 15) (hi : i.val = 8) :
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
  · exact certifiedRow8
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionCoefficientTables.Balanced
