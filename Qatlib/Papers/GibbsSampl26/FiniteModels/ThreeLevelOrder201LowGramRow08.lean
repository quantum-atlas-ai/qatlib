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


/-- Gram row 8 for the stated finite source data. -/
theorem gram_row_8 :
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
  exact certified_gram_row 8


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowCoefficientTables
