/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionBalancedGram

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite coefficient incidence on the order012 collision face

The six fixed Gram products of the literal stack B+eU+GeV are checked
entrywise. They are then bound to all30certified degree(4,2) coefficients.
The actual physical interpretation of B,U,V and generic Bernstein
reconstruction are supplied separately by ThreeLevelCollisionFace.
-/

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables
open ThreeLevelGramCertificate ThreeLevelCollisionCertificates Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async true


/-- Gram row 10 for the stated finite source data. -/
theorem gram_row_10 :
    (∀ j, gramBBReal 10 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 10 j) ∧
    (∀ j, gramBBImag 10 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 10 j) ∧
    (∀ j, gramBUReal 10 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 10 j) ∧
    (∀ j, gramBUImag 10 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 10 j) ∧
    (∀ j, gramBVReal 10 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 10 j) ∧
    (∀ j, gramBVImag 10 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 10 j) ∧
    (∀ j, gramUUReal 10 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 10 j) ∧
    (∀ j, gramUUImag 10 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 10 j) ∧
    (∀ j, gramUVReal 10 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 10 j) ∧
    (∀ j, gramUVImag 10 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 10 j) ∧
    (∀ j, gramVVReal 10 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 10 j) ∧
    (∀ j, gramVVImag 10 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 10 j) := by
  exact certified_gram_row 10


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables
