/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighBalancedGram

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite coefficient incidence on the order201 high collision face

The six fixed Gram products of the literal stack B+eU+GeV are checked
entrywise. They are then bound to all30certified degree(4,2) coefficients.
The actual physical interpretation of B,U,V and generic Bernstein
reconstruction are supplied separately by ThreeLevelOrder201HighFace.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables
open ThreeLevelGramCertificate ThreeLevelOrder201HighCertificates Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async true


/-- Gram row 0 for the stated finite source data. -/
theorem gram_row_0 :
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
  exact certified_gram_row 0


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables
