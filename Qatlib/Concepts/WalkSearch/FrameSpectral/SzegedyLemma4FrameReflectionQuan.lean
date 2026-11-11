/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma4FrameReflectionStat
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Projection and reflection for orthonormal frames

The theorem `szegedyLemma4FrameReflection` proves that the outer product sum of an orthonormal
frame is an orthogonal projector. It computes its action and the associated reflection on frame
vectors and on states orthogonal to every frame vector. The quantum walk spectral framework is
developed in [Szegedy2004].

## Main statements

* `szegedyLemma4FrameReflection`: Projector and reflection actions for an orthonormal frame.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- For an orthonormal frame, its outer product sum is an orthogonal projector fixing the frame
vectors and annihilating their orthogonal complement. The associated reflection fixes the
frame vectors and negates the orthogonal complement [Szegedy, Lemma 4][Szegedy2004]. -/
theorem szegedyLemma4FrameReflection : SzegedyLemma4FrameReflection := by
  intro H ι _ _ _ _ v h
  let V : Matrix H ι ℂ := fun x i => v i x
  have hV : IsIsometry V := by
    ext i j
    change Inner (v i) (v j) = _
    simpa only [Matrix.one_apply] using h i j
  have hP : paperFrameProjection v = V*Vᴴ := by
    ext x y
    simp [paperFrameProjection, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, V]
  have hcol (l : ι) : Vᴴ*ᵥv l = fun i => if i=l then 1 else 0 := by
    funext i
    exact h i l
  have hfix (l : ι) : paperFrameProjection v *ᵥ v l = v l := by
    rw [hP, ← Matrix.mulVec_mulVec, hcol]
    ext x
    simp [Matrix.mulVec, dotProduct, V]
  have hzero (w : QState H) (hw : ∀ l, Inner (v l) w = 0) :
      paperFrameProjection v *ᵥ w = 0 := by
    have hvw : Vᴴ*ᵥw = 0 := by funext i; exact hw i
    rw [hP, ← Matrix.mulVec_mulVec, hvw, Matrix.mulVec_zero]
  refine ⟨?_, hfix, hzero, ?_, ?_⟩
  · rw [hP]
    exact rangeProjector_isOrthogonalProjector hV
  · intro l
    rw [reflectionAbout_mulVec, hfix]
    module
  · intro w hw
    rw [reflectionAbout_mulVec, hzero w hw, smul_zero, zero_sub]

end Qatlib.Concepts.WalkSearch.FrameSpectral
