/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionBalancedGram

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite coefficient incidence on the order012 high collision face

The six fixed Gram products of the literal stack B+eU+AeV are checked
entrywise. They are then bound to all 35 certified degree (4,3)/(4,2) coefficients.
The actual physical interpretation of B,U,V and generic Bernstein
reconstruction are supplied separately by ThreeLevelHighCollisionFace.
-/

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionCoefficientTables
open ThreeLevelGramCertificate ThreeLevelHighCollisionCertificates Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async true


/-- Gram row 4 for the stated finite source data. -/
theorem gram_row_4 :
    (∀ j, gramBBReal 4 j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) 4 j) ∧
    (∀ j, gramBBImag 4 j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) 4 j) ∧
    (∀ j, gramBUReal 4 j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) 4 j) ∧
    (∀ j, gramBUImag 4 j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) 4 j) ∧
    (∀ j, gramBVReal 4 j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) 4 j) ∧
    (∀ j, gramBVImag 4 j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) 4 j) ∧
    (∀ j, gramUUReal 4 j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) 4 j) ∧
    (∀ j, gramUUImag 4 j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) 4 j) ∧
    (∀ j, gramUVReal 4 j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) 4 j) ∧
    (∀ j, gramUVImag 4 j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) 4 j) ∧
    (∀ j, gramVVReal 4 j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) 4 j) ∧
    (∀ j, gramVVImag 4 j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) 4 j) := by
  exact certified_gram_row 4


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionCoefficientTables
