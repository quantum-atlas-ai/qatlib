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


/-- Gram row 14 for the stated finite source data. -/
theorem gram_row_14 :
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
  exact certified_gram_row 14


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowCoefficientTables
