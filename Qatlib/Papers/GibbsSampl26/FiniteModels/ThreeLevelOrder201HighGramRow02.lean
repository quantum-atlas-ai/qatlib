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


/-- Gram row 2 for the stated finite source data. -/
theorem gram_row_2 :
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
  exact certified_gram_row 2


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables
