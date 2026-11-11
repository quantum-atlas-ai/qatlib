/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FrameMeasures.HaarFrames.MeasureDefs

/-!
# Outer measure content through observation maps

This module defines `imageContent` for an arbitrary map by applying a target outer measure to
images of source sets. The formula `imageContent_apply` holds without a measurability
hypothesis, and `imageContent_univ` gives total content one when the target range has outer
measure one.

This interface supports observation-space volume estimates, such as those arising in quantum
circuit approximation [Knill1995].

## Main statements

* `imageContent_apply`: The image content of `X` equals the target outer measure of `f '' X`.
* `imageContent_univ`: If the range of `f` has outer measure one, the image content of the whole
  source is one.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.FrameMeasures.HaarFrames

/-- The outer measure on the source obtained by evaluating `μ` on images under `f`. -/
def imageContent {α β : Type*} (f : α → β) (μ : OuterMeasure β) : OuterMeasure α :=
  OuterMeasure.comap f μ

/-- The image content of `X` equals the target outer measure of `f '' X`. -/
theorem imageContent_apply {α β : Type*} (f : α → β) (μ : OuterMeasure β) (X : Set α) :
    imageContent f μ X = μ (f '' X) := OuterMeasure.comap_apply _ _ _

/-- If the range of `f` has outer measure one, the image content of the whole source is one. -/
theorem imageContent_univ {α β : Type*} (f : α → β) (μ : OuterMeasure β)
    (h : μ (Set.range f) = 1) : imageContent f μ Set.univ = 1 := by
  simpa only [imageContent_apply, Set.image_univ] using h

end Qatlib.Foundations.FrameMeasures.HaarFrames
