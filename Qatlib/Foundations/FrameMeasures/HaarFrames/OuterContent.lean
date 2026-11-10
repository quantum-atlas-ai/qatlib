/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FrameMeasures.HaarFrames.MeasureDefs

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.FrameMeasures.HaarFrames

def imageContent {α β : Type*} (f : α → β) (μ : OuterMeasure β) : OuterMeasure α :=
  OuterMeasure.comap f μ

theorem imageContent_apply {α β : Type*} (f : α → β) (μ : OuterMeasure β) (X : Set α) :
    imageContent f μ X = μ (f '' X) := OuterMeasure.comap_apply _ _ _

theorem imageContent_univ {α β : Type*} (f : α → β) (μ : OuterMeasure β)
    (h : μ (Set.range f) = 1) : imageContent f μ Set.univ = 1 := by
  simpa only [imageContent_apply, Set.image_univ] using h

end Qatlib.Foundations.FrameMeasures.HaarFrames
