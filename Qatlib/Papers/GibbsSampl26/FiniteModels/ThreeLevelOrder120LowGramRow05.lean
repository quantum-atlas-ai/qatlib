/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowBalancedGram

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite coefficient incidence on the order120 low collision face

The six fixed Gram products of the literal stack B+eU+GeV are checked
entrywise. They are then bound to all 43 certified degree (6,3)/(4,2) coefficient occurrences.
The actual physical interpretation of B,U,V and generic Bernstein
reconstruction are supplied separately by ThreeLevelOrder120LowFace.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowCoefficientTables
open ThreeLevelGramCertificate ThreeLevelOrder120LowCertificates Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async true


/-- Gram row 5 for the stated finite source data. -/
theorem gram_row_5 :
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
  exact certified_gram_row 5


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowCoefficientTables
