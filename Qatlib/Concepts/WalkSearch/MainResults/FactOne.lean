/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Errors of approximate line reflections

`lineProj`, `lineRefl`, and `reflError` describe projection onto a vector span, reflection about
that span, and the discrepancy of a linear isometry from this reflection. The error vanishes on
a fixed reference vector, and the assumed homogeneous bound specializes to a unit vector bound
on its orthogonal complement. For background on search via quantum walks, see
[MagniezNayakRolandSantha2011].

## Main statements

* `lineProj`: The orthogonal projection onto the complex span of `u`, viewed as a continuous
  linear endomorphism of the ambient space.
* `reflError_bound_unit`: For a unit vector orthogonal to `u`, the homogeneous discrepancy
  hypothesis bounds the reflection error by `β`; see [Magniez et al., Fact
  1][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.WalkSearch.MainResults.FactOne

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- The orthogonal projection onto the complex span of `u`, viewed as a continuous linear
endomorphism of the ambient space. -/
noncomputable def lineProj (u : W) : W →L[ℂ] W :=
  (Submodule.subtypeL (Submodule.span ℂ {u})).comp
    (Submodule.orthogonalProjection (Submodule.span ℂ {u}))

/-- The continuous linear map `2 • lineProj u - id` reflecting about the span of `u`. -/
noncomputable def lineRefl (u : W) : W →L[ℂ] W :=
  2 • lineProj u - ContinuousLinearMap.id ℂ W

/-- The pointwise difference between the linear isometry `R` and reflection about the span of
`u`. -/
noncomputable def reflError (R : W ≃ₗᵢ[ℂ] W) (u : W) : W → W :=
  fun ψ => R ψ - ((2 : ℂ) • lineProj u ψ - ψ)

/-- Projection onto the span of `u` fixes `u`. -/
theorem lineProj_apply_self (u : W) : lineProj u u = u := by
  have h : lineProj u u = (Submodule.span ℂ ({u} : Set W)).starProjection u := rfl
  rw [h, Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self u)]

/-- Projection onto the span of `u` vanishes on its orthogonal complement. -/
theorem lineProj_apply_eq_zero_of_mem_orthogonal {u ψ : W}
    (hψ : ψ ∈ (Submodule.span ℂ ({u} : Set W))ᗮ) : lineProj u ψ = 0 := by
  have h : lineProj u ψ = (Submodule.span ℂ ({u} : Set W)).starProjection ψ := rfl
  rw [h, (Submodule.starProjection_apply_eq_zero_iff
    (K := Submodule.span ℂ ({u} : Set W))).mpr hψ]

/-- If `R` fixes `u`, its reflection error at `u` is zero, as in [Magniez et al., Fact
1][MagniezNayakRolandSantha2011]. -/
theorem reflError_apply_self (R : W ≃ₗᵢ[ℂ] W) (u : W) (hfix : R u = u) :
    reflError R u u = 0 := by
  have hlin : lineProj u u = u := lineProj_apply_self u
  unfold reflError
  rw [hlin, hfix]
  module

/-- On the orthogonal complement of the span of `u`, the reflection error equals `R ψ + ψ`. -/
theorem reflError_apply_of_mem_orthogonal (R : W ≃ₗᵢ[ℂ] W) {u ψ : W}
    (hψ : ψ ∈ (Submodule.span ℂ ({u} : Set W))ᗮ) :
    reflError R u ψ = R ψ + ψ := by
  have hzero : lineProj u ψ = 0 := lineProj_apply_eq_zero_of_mem_orthogonal hψ
  unfold reflError
  rw [hzero]
  module

/-- The assumed homogeneous reflection discrepancy bound implies `‖reflError R u ψ‖ ≤ β * ‖ψ‖`
for vectors orthogonal to `u`. -/
theorem reflError_bound_of_mem_orthogonal (R : W ≃ₗᵢ[ℂ] W) {u ψ : W} {β : ℝ}
    (hψ : ψ ∈ (Submodule.span ℂ ({u} : Set W))ᗮ)
    (hbound : ∀ ψ ∈ (Submodule.span ℂ ({u} : Set W))ᗮ,
      ‖R ψ + ψ - (2 : ℂ) • lineProj u ψ‖ ≤ β * ‖ψ‖) :
    ‖reflError R u ψ‖ ≤ β * ‖ψ‖ := by
  have hzero : lineProj u ψ = 0 := lineProj_apply_eq_zero_of_mem_orthogonal hψ
  have hEq : R ψ + ψ - (2 : ℂ) • lineProj u ψ = R ψ + ψ := by
    rw [hzero, smul_zero, sub_zero]
  rw [reflError_apply_of_mem_orthogonal R hψ, ← hEq]
  exact hbound ψ hψ

/-- For a unit vector orthogonal to `u`, the homogeneous discrepancy hypothesis bounds the
reflection error by `β`; see [Magniez et al., Fact 1][MagniezNayakRolandSantha2011]. -/
theorem reflError_bound_unit (R : W ≃ₗᵢ[ℂ] W) {u ψ : W} {β : ℝ}
    (hψ : ψ ∈ (Submodule.span ℂ ({u} : Set W))ᗮ) (hunit : ‖ψ‖ = 1)
    (hbound : ∀ ψ ∈ (Submodule.span ℂ ({u} : Set W))ᗮ,
      ‖R ψ + ψ - (2 : ℂ) • lineProj u ψ‖ ≤ β * ‖ψ‖) :
    ‖reflError R u ψ‖ ≤ β := by
  have h := reflError_bound_of_mem_orthogonal R hψ hbound
  rwa [hunit, mul_one] at h

end Qatlib.Concepts.WalkSearch.MainResults.FactOne
