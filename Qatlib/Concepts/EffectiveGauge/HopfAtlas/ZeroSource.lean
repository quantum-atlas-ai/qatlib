/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicIntegral
import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false

/-!
# The zero first-bound branch derives every higher source bound

The original first bound is stated on the physical cube. Actual derivative
periodicity extends its zero value to all space, and the true Fréchet
derivative then vanishes. This justifies the frame's higher zero bounds
without querying the original higher-bound program.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `periodicSource_zero_first_fderiv` guarantee for the `ZeroSource` construction; the complete source hypotheses are retained. -/
theorem periodicSource_zero_first_fderiv (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hp : IsPeriodicField v)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖fderiv ℝ v x (EuclideanSpace.single i 1)‖ ≤ 0)
    (x : SpatialPoint) : fderiv ℝ v x=0 := by
  have hper := periodicField_fderiv v hv hp
  have hwrap : fderiv ℝ v (wrapPoint x)=fderiv ℝ v x := by
    rw [wrapPoint_shift]
    exact hper x _
  have haxes (i : Fin 3) : fderiv ℝ v x (EuclideanSpace.single i 1)=0 := by
    have h := norm_le_zero_iff.mp (hb (wrapPoint x) (wrapPoint_cube x) i)
    rw [hwrap] at h
    exact h
  apply ContinuousLinearMap.ext
  intro w
  change fderiv ℝ v x w=0
  have hw : w=w 0 • EuclideanSpace.single 0 (1 : ℝ)+
      w 1 • EuclideanSpace.single 1 (1 : ℝ)+w 2 • EuclideanSpace.single 2 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  rw [hw]
  simp only [map_add,map_smul,haxes,smul_zero,add_zero]

/-- Original `periodicSource_zero_first_constant` guarantee for the `ZeroSource` construction; the complete source hypotheses are retained. -/
theorem periodicSource_zero_first_constant (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hp : IsPeriodicField v)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖fderiv ℝ v x (EuclideanSpace.single i 1)‖ ≤ 0) :
    v=fun _ => v 0 := by
  funext x
  exact is_const_of_fderiv_eq_zero (hv.differentiable (by simp))
    (periodicSource_zero_first_fderiv v hv hp hb) x 0

/-- Original `periodicSource_zero_first_word` guarantee for the `ZeroSource` construction; the complete source hypotheses are retained. -/
theorem periodicSource_zero_first_word (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hp : IsPeriodicField v)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖fderiv ℝ v x (EuclideanSpace.single i 1)‖ ≤ 0)
    (w : List (Fin 3)) (hw : w≠[]) : spatialWordPartial v w=fun _ => 0 := by
  rw [periodicSource_zero_first_constant v hv hp hb,spatialWordPartial_const]
  simp only [hw,ite_false]

/-- Every positive original multi-index derivative is exactly zero, on all
space. A positive raw higher bound is not needed in this branch. -/
theorem periodicSource_zero_first_jet (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hp : IsPeriodicField v)
    (hb : ∀ x, InFundamentalCube x → ∀ i, ‖fderiv ℝ v x (EuclideanSpace.single i 1)‖ ≤ 0)
    (alpha : Fin 3 → ℕ) (ha : 0<(∑ i : Fin 3, alpha i)) :
    sourceCanonicalJet v alpha=fun _ => 0 := by
  have hword : sourceCanonicalWord alpha≠[] := by
    intro h
    have hl := sourceCanonicalWord_length alpha
    rw [h,List.length_nil] at hl
    omega
  exact periodicSource_zero_first_word v hv hp hb _ hword

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
