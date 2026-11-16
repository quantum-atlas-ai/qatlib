/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order201LowGram.BalancedTables

@[expose] public section


/-!
# Complete Gram incidence for the leading coordinates of operator row 0 (X₀₁ and X₀₂)

The row indices follow ThreeLevelCoordinateMetric.fullCoordinates and
ThreeLevelCornerFastChart.fastCoordinates. Each row retains all twelve real
and imaginary identities against the complete original source matrices.
Each coefficient pair is checked separately, then the six pairs are assembled
using the table equalities, bounding the kernel reduction context.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowCoefficientTables.Balanced
open Matrix
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Balanced real and imaginary base/base Gram coefficients on row 2. -/
private theorem r2BB :
    (∀ j, gramBBRealBalanced 2 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 2 j) ∧
    (∀ j, gramBBImagBalanced 2 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 2 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 2. -/
private theorem r2BU :
    (∀ j, gramBURealBalanced 2 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 2 j) ∧
    (∀ j, gramBUImagBalanced 2 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 2 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 2. -/
private theorem r2BV :
    (∀ j, gramBVRealBalanced 2 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 2 j) ∧
    (∀ j, gramBVImagBalanced 2 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 2 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 2. -/
private theorem r2UU :
    (∀ j, gramUURealBalanced 2 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 2 j) ∧
    (∀ j, gramUUImagBalanced 2 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 2 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 2. -/
private theorem r2UV :
    (∀ j, gramUVRealBalanced 2 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 2 j) ∧
    (∀ j, gramUVImagBalanced 2 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 2 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 2. -/
private theorem r2VV :
    (∀ j, gramVVRealBalanced 2 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 2 j) ∧
    (∀ j, gramVVImagBalanced 2 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 2 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 2. -/
private theorem certifiedRow2 :
    (∀ j, gramBBReal 2 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 2 j) ∧
    (∀ j, gramBBImag 2 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 2 j) ∧
    (∀ j, gramBUReal 2 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 2 j) ∧
    (∀ j, gramBUImag 2 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 2 j) ∧
    (∀ j, gramBVReal 2 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 2 j) ∧
    (∀ j, gramBVImag 2 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 2 j) ∧
    (∀ j, gramUUReal 2 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 2 j) ∧
    (∀ j, gramUUImag 2 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 2 j) ∧
    (∀ j, gramUVReal 2 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 2 j) ∧
    (∀ j, gramUVImag 2 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 2 j) ∧
    (∀ j, gramVVReal 2 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 2 j) ∧
    (∀ j, gramVVImag 2 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 2 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r2BB.1, r2BB.2, r2BU.1, r2BU.2, r2BV.1, r2BV.2, r2UU.1, r2UU.2, r2UV.1, r2UV.2, r2VV.1, r2VV.2⟩

/-- Balanced real and imaginary base/base Gram coefficients on row 3. -/
private theorem r3BB :
    (∀ j, gramBBRealBalanced 3 j = (faceBaseRealBalanced.transpose * faceBaseRealBalanced + faceBaseImagBalanced.transpose * faceBaseImagBalanced) 3 j) ∧
    (∀ j, gramBBImagBalanced 3 j = (faceBaseRealBalanced.transpose * faceBaseImagBalanced - faceBaseImagBalanced.transpose * faceBaseRealBalanced) 3 j) := by
  decide +kernel

/-- Balanced real and imaginary base/up Gram coefficients on row 3. -/
private theorem r3BU :
    (∀ j, gramBURealBalanced 3 j = (faceBaseRealBalanced.transpose * faceUpRealBalanced + faceBaseImagBalanced.transpose * faceUpImagBalanced + faceUpRealBalanced.transpose * faceBaseRealBalanced + faceUpImagBalanced.transpose * faceBaseImagBalanced) 3 j) ∧
    (∀ j, gramBUImagBalanced 3 j = (faceBaseRealBalanced.transpose * faceUpImagBalanced - faceBaseImagBalanced.transpose * faceUpRealBalanced + faceUpRealBalanced.transpose * faceBaseImagBalanced - faceUpImagBalanced.transpose * faceBaseRealBalanced) 3 j) := by
  decide +kernel

/-- Balanced real and imaginary base/down Gram coefficients on row 3. -/
private theorem r3BV :
    (∀ j, gramBVRealBalanced 3 j = (faceBaseRealBalanced.transpose * faceDownRealBalanced + faceBaseImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceBaseRealBalanced + faceDownImagBalanced.transpose * faceBaseImagBalanced) 3 j) ∧
    (∀ j, gramBVImagBalanced 3 j = (faceBaseRealBalanced.transpose * faceDownImagBalanced - faceBaseImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceBaseImagBalanced - faceDownImagBalanced.transpose * faceBaseRealBalanced) 3 j) := by
  decide +kernel

/-- Balanced real and imaginary up/up Gram coefficients on row 3. -/
private theorem r3UU :
    (∀ j, gramUURealBalanced 3 j = (faceUpRealBalanced.transpose * faceUpRealBalanced + faceUpImagBalanced.transpose * faceUpImagBalanced) 3 j) ∧
    (∀ j, gramUUImagBalanced 3 j = (faceUpRealBalanced.transpose * faceUpImagBalanced - faceUpImagBalanced.transpose * faceUpRealBalanced) 3 j) := by
  decide +kernel

/-- Balanced real and imaginary up/down Gram coefficients on row 3. -/
private theorem r3UV :
    (∀ j, gramUVRealBalanced 3 j = (faceUpRealBalanced.transpose * faceDownRealBalanced + faceUpImagBalanced.transpose * faceDownImagBalanced + faceDownRealBalanced.transpose * faceUpRealBalanced + faceDownImagBalanced.transpose * faceUpImagBalanced) 3 j) ∧
    (∀ j, gramUVImagBalanced 3 j = (faceUpRealBalanced.transpose * faceDownImagBalanced - faceUpImagBalanced.transpose * faceDownRealBalanced + faceDownRealBalanced.transpose * faceUpImagBalanced - faceDownImagBalanced.transpose * faceUpRealBalanced) 3 j) := by
  decide +kernel

/-- Balanced real and imaginary down/down Gram coefficients on row 3. -/
private theorem r3VV :
    (∀ j, gramVVRealBalanced 3 j = (faceDownRealBalanced.transpose * faceDownRealBalanced + faceDownImagBalanced.transpose * faceDownImagBalanced) 3 j) ∧
    (∀ j, gramVVImagBalanced 3 j = (faceDownRealBalanced.transpose * faceDownImagBalanced - faceDownImagBalanced.transpose * faceDownRealBalanced) 3 j) := by
  decide +kernel

/-- Exact complete Gram incidence on fixed row 3. -/
private theorem certifiedRow3 :
    (∀ j, gramBBReal 3 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 3 j) ∧
    (∀ j, gramBBImag 3 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 3 j) ∧
    (∀ j, gramBUReal 3 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 3 j) ∧
    (∀ j, gramBUImag 3 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 3 j) ∧
    (∀ j, gramBVReal 3 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 3 j) ∧
    (∀ j, gramBVImag 3 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 3 j) ∧
    (∀ j, gramUUReal 3 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 3 j) ∧
    (∀ j, gramUUImag 3 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 3 j) ∧
    (∀ j, gramUVReal 3 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 3 j) ∧
    (∀ j, gramUVImag 3 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 3 j) ∧
    (∀ j, gramVVReal 3 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 3 j) ∧
    (∀ j, gramVVImag 3 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 3 j) := by
  rw [← faceBaseRealBalanced_eq, ← faceBaseImagBalanced_eq, ← faceUpRealBalanced_eq, ← faceUpImagBalanced_eq, ← faceDownRealBalanced_eq, ← faceDownImagBalanced_eq, ← gramBBRealBalanced_eq, ← gramBBImagBalanced_eq, ← gramBURealBalanced_eq, ← gramBUImagBalanced_eq, ← gramBVRealBalanced_eq, ← gramBVImagBalanced_eq, ← gramUURealBalanced_eq, ← gramUUImagBalanced_eq, ← gramUVRealBalanced_eq, ← gramUVImagBalanced_eq, ← gramVVRealBalanced_eq, ← gramVVImagBalanced_eq]
  exact ⟨r3BB.1, r3BB.2, r3BU.1, r3BU.2, r3BV.1, r3BV.2, r3UU.1, r3UU.2, r3UV.1, r3UV.2, r3VV.1, r3VV.2⟩

/-- All twelve complete-source Gram identities on the leading coordinates of operator row 0 (X₀₁ and X₀₂). -/
theorem operatorRow0 (i : Fin 15) (hi : 2 ≤ i.val ∧ i.val < 4) :
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
  · exact certifiedRow2
  · exact certifiedRow3
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

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowCoefficientTables.Balanced
