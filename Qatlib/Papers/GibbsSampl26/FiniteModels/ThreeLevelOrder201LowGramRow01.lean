/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowBalancedGram

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite coefficient incidence on the order201 low collision face

The six fixed Gram products of the literal stack B+eU+GeV are checked
entrywise. They are then bound to all30certified degree(4,2) coefficients.
The actual physical interpretation of B,U,V and generic Bernstein
reconstruction are supplied separately by ThreeLevelOrder201LowFace.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowCoefficientTables
open ThreeLevelGramCertificate ThreeLevelOrder201LowCertificates Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async true


/-- Gram row 1 for the stated finite source data. -/
theorem gram_row_1 :
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
  exact certified_gram_row 1


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowCoefficientTables
