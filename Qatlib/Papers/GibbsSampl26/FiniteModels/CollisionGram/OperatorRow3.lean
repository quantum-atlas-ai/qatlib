/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.CollisionGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for operator row 3 in the nonorthonormal fast chart

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

/-- Balanced real and imaginary base/base Gram coefficients on row 13. -/
private theorem r13BB :
    (∀ j, gramBBRealBalanced 13 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 13 j) ∧
    (∀ j, gramBBImagBalanced 13 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 13 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 13. -/
private theorem r13BU :
    (∀ j, gramBURealBalanced 13 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 13 j) ∧
    (∀ j, gramBUImagBalanced 13 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 13 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 13. -/
private theorem r13BV :
    (∀ j, gramBVRealBalanced 13 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 13 j) ∧
    (∀ j, gramBVImagBalanced 13 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 13 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 13. -/
private theorem r13UU :
    (∀ j, gramUURealBalanced 13 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 13 j) ∧
    (∀ j, gramUUImagBalanced 13 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 13 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 13. -/
private theorem r13UV :
    (∀ j, gramUVRealBalanced 13 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 13 j) ∧
    (∀ j, gramUVImagBalanced 13 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 13 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 13. -/
private theorem r13VV :
    (∀ j, gramVVRealBalanced 13 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 13 j) ∧
    (∀ j, gramVVImagBalanced 13 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 13 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 13. -/
private theorem certifiedRow13 :
    (∀ j, gramBBReal 13 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 13 j) ∧
    (∀ j, gramBBImag 13 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 13 j) ∧
    (∀ j, gramBUReal 13 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 13 j) ∧
    (∀ j, gramBUImag 13 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 13 j) ∧
    (∀ j, gramBVReal 13 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 13 j) ∧
    (∀ j, gramBVImag 13 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 13 j) ∧
    (∀ j, gramUUReal 13 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 13 j) ∧
    (∀ j, gramUUImag 13 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 13 j) ∧
    (∀ j, gramUVReal 13 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 13 j) ∧
    (∀ j, gramUVImag 13 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 13 j) ∧
    (∀ j, gramVVReal 13 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 13 j) ∧
    (∀ j, gramVVImag 13 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 13 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r13BB.1, r13BB.2, r13BU.1, r13BU.2, r13BV.1, r13BV.2, r13UU.1, r13UU.2, r13UV.1, r13UV.2, r13VV.1, r13VV.2⟩

/-- Balanced real and imaginary base/base Gram coefficients on row 14. -/
private theorem r14BB :
    (∀ j, gramBBRealBalanced 14 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 14 j) ∧
    (∀ j, gramBBImagBalanced 14 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 14 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 14. -/
private theorem r14BU :
    (∀ j, gramBURealBalanced 14 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 14 j) ∧
    (∀ j, gramBUImagBalanced 14 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 14 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 14. -/
private theorem r14BV :
    (∀ j, gramBVRealBalanced 14 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 14 j) ∧
    (∀ j, gramBVImagBalanced 14 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 14 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 14. -/
private theorem r14UU :
    (∀ j, gramUURealBalanced 14 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 14 j) ∧
    (∀ j, gramUUImagBalanced 14 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 14 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 14. -/
private theorem r14UV :
    (∀ j, gramUVRealBalanced 14 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 14 j) ∧
    (∀ j, gramUVImagBalanced 14 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 14 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 14. -/
private theorem r14VV :
    (∀ j, gramVVRealBalanced 14 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 14 j) ∧
    (∀ j, gramVVImagBalanced 14 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 14 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 14. -/
private theorem certifiedRow14 :
    (∀ j, gramBBReal 14 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 14 j) ∧
    (∀ j, gramBBImag 14 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 14 j) ∧
    (∀ j, gramBUReal 14 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 14 j) ∧
    (∀ j, gramBUImag 14 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 14 j) ∧
    (∀ j, gramBVReal 14 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 14 j) ∧
    (∀ j, gramBVImag 14 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 14 j) ∧
    (∀ j, gramUUReal 14 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 14 j) ∧
    (∀ j, gramUUImag 14 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 14 j) ∧
    (∀ j, gramUVReal 14 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 14 j) ∧
    (∀ j, gramUVImag 14 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 14 j) ∧
    (∀ j, gramVVReal 14 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 14 j) ∧
    (∀ j, gramVVImag 14 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 14 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r14BB.1, r14BB.2, r14BU.1, r14BU.2, r14BV.1, r14BV.2, r14UU.1, r14UU.2, r14UV.1, r14UV.2, r14VV.1, r14VV.2⟩

/-- All twelve complete-source Gram identities on operator row 3 in the nonorthonormal fast chart. -/
theorem operatorRow3 (i : Fin 15) (hi : 13 ≤ i.val) :
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
  · norm_num at hi
  · norm_num at hi
  · exact certifiedRow13
  · exact certifiedRow14

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables.Balanced
