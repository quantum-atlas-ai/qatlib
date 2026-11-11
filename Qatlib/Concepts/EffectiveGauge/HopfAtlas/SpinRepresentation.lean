/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Model
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Isometric original three-vector spin representation and actual derivatives -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of spin Of Vector in the Hopf Atlas construction. -/
def spinOfVector (v : SpatialPoint) : ℍ := ⟨0,v 0,v 1,v 2⟩

/-- Original `spinOfVector_norm` guarantee for the `SpinRepresentation` construction; the complete source hypotheses are retained. -/
theorem spinOfVector_norm (v : SpatialPoint) : ‖spinOfVector v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hv : ‖v‖^2=(v 0)^2+(v 1)^2+(v 2)^2 := by
    calc
      _ = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
      _ = _ := by
        rw [PiLp.inner_apply]
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, Fin.sum_univ_three]
        ring
  rw [hv, pow_two, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [spinOfVector]

/-- Definition of spin Embedding in the Hopf Atlas construction. -/
def spinEmbedding : SpatialPoint →ₗᵢ[ℝ] ℍ where
  toFun := spinOfVector
  map_add' a b := by ext <;> simp [spinOfVector]
  map_smul' r v := by ext <;> simp [spinOfVector]
  norm_map' := spinOfVector_norm

/-- Original `spin_field_isSmooth` guarantee for the `SpinRepresentation` construction; the complete source hypotheses are retained. -/
theorem spin_field_isSmooth {v : SpatialPoint → SpatialPoint}
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) :
    IsSmoothSpin (fun x => spinOfVector (v x)) := by
  refine ⟨spinEmbedding.toContinuousLinearMap.contDiff.comp hv, ?_⟩
  intro x
  exact ⟨rfl, (spinOfVector_norm (v x)).trans (hu x)⟩

/-- Original `spinOfVector_hasDerivAt` guarantee for the `SpinRepresentation` construction; the complete source hypotheses are retained. -/
theorem spinOfVector_hasDerivAt {s : ℝ → SpatialPoint} {v : SpatialPoint} {t : ℝ}
    (hs : HasDerivAt s v t) :
    HasDerivAt (fun u => spinOfVector (s u)) (spinOfVector v) t :=
  spinEmbedding.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hs

/-- Original `spin_field_periodic` guarantee for the `SpinRepresentation` construction; the complete source hypotheses are retained. -/
theorem spin_field_periodic {v : SpatialPoint → SpatialPoint} (hv : IsPeriodicField v) :
    IsPeriodicField (fun x => spinOfVector (v x)) := by
  intro x n
  exact congrArg spinOfVector (hv x n)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
