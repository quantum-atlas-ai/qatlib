/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Nontrivial.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Rayleigh energies, compressions, and self-energy

This module defines real quadratic-form energies and their infima on unit vectors, both globally
and within a subspace. The compression, resolvent, and self-energy constructions provide the
operator vocabulary for [KempeKitaevRegev2006], while the remaining lemmas establish basic norm
bounds and properties of the energy sets.

## Main statements

* `groundEnergy`: Defines the infimum of unit-vector Rayleigh values.
* `selfEnergy`: Defines self-energy using a compressed resolvent.
* `sectionEnergy_mul_le`: Bounds a quadratic form below using its subspace energy.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

noncomputable section

open scoped ComplexOrder
open InnerProductSpace

namespace Qatlib.Papers.LocalHam06.MainResults.OperatorDefs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

/-- The real part of the quadratic form `inner ℂ v (H v)`. -/
def rayleigh (H : E →L[ℂ] E) (v : E) : ℝ := (inner ℂ v (H v)).re

/-- The set of real Rayleigh values of `H` on unit vectors. -/
def rect (H : E →L[ℂ] E) : Set ℝ := rayleigh H '' {v : E | ‖v‖ = 1}

/-- The set of real Rayleigh values of `H` on unit vectors lying in `S`. -/
def sectionSet (S : Submodule ℂ E) (H : E →L[ℂ] E) : Set ℝ :=
  rayleigh H '' {v : E | ‖v‖ = 1 ∧ v ∈ S}

/-- The infimum of the unit-vector Rayleigh values of `H`. -/
def groundEnergy (H : E →L[ℂ] E) : ℝ := sInf (rect H)

/-- The infimum of the Rayleigh values of `H` on unit vectors in `S`. -/
def sectionEnergy (S : Submodule ℂ E) (H : E →L[ℂ] E) : ℝ := sInf (sectionSet S H)

/-- The operator on `L` obtained by restricting the input to `L` and orthogonally projecting the
output back to `L`. -/
def compressedOperator (L : Submodule ℂ E) (T : E →L[ℂ] E) : L →L[ℂ] L :=
  ((L.starProjection : E →L[ℂ] E).comp (T.comp L.subtypeL)).codRestrict L
    (fun x => L.starProjection_apply_mem (T x))

/-- The ring inverse of `z • 1 - T`. -/
def resolventOperator (T : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  Ring.inverse (z • (1 : E →L[ℂ] E) - T)

/-- The self-energy operator `z • 1` minus the ring inverse of the resolvent of `H + V`
compressed to `L`. -/
def selfEnergy (L : Submodule ℂ E) (H V : E →L[ℂ] E) (z : ℝ) : L →L[ℂ] L :=
  (z : ℂ) • (1 : L →L[ℂ] L) -
    Ring.inverse (compressedOperator L (resolventOperator (H + V) (z : ℂ)))

/-- The Rayleigh value at the zero vector is zero. -/
lemma rayleigh_zero (H : E →L[ℂ] E) : rayleigh H 0 = 0 := by
  simp [rayleigh]

/-- The absolute Rayleigh value is at most `‖H‖ * ‖v‖^2`. -/
lemma abs_rayleigh_le (H : E →L[ℂ] E) (v : E) :
    |rayleigh H v| ≤ ‖H‖ * ‖v‖ ^ 2 := by
  calc
    |rayleigh H v| = |(inner ℂ v (H v)).re| := rfl
    _ ≤ ‖inner ℂ v (H v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v‖ * ‖H v‖ := norm_inner_le_norm v (H v)
    _ ≤ ‖v‖ * (‖H‖ * ‖v‖) := by
        gcongr
        exact H.le_opNorm v
    _ = ‖H‖ * ‖v‖ ^ 2 := by ring

/-- The Rayleigh value is at least `-(‖H‖ * ‖v‖^2)`. -/
lemma rayleigh_neg_le (H : E →L[ℂ] E) (v : E) :
    -(‖H‖ * ‖v‖ ^ 2) ≤ rayleigh H v := by
  have h := abs_rayleigh_le H v
  have h2 := neg_abs_le (rayleigh H v)
  linarith

/-- The Rayleigh value is at most `‖H‖ * ‖v‖^2`. -/
lemma rayleigh_le (H : E →L[ℂ] E) (v : E) :
    rayleigh H v ≤ ‖H‖ * ‖v‖ ^ 2 := by
  have h := abs_rayleigh_le H v
  have h2 := le_abs_self (rayleigh H v)
  linarith

/-- Scaling the input vector by a real scalar scales its Rayleigh value by the square of that
scalar. -/
lemma rayleigh_smul_real (H : E →L[ℂ] E) (r : ℝ) (v : E) :
    rayleigh H (r • v) = r ^ 2 * rayleigh H v := by
  have hsmul : (r : ℂ) • v = r • v := IsScalarTower.algebraMap_smul ℂ (r : ℝ) v
  unfold rayleigh
  rw [← hsmul, map_smul, inner_smul_left, inner_smul_right]
  have hstar : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    simpa using Complex.conj_ofReal r
  rw [hstar]
  have hcomp : ((r : ℂ) * ((r : ℂ) * inner ℂ v (H v))).re =
      r ^ 2 * (inner ℂ v (H v)).re := by
    have hval : (r : ℂ) * ((r : ℂ) * inner ℂ v (H v)) =
        ((r * r : ℝ) : ℂ) * inner ℂ v (H v) := by
      rw [Complex.ofReal_mul]
      ring
    rw [hval, Complex.re_ofReal_mul]
    ring
  exact hcomp

/-- The nontrivial inner product space contains a unit vector. -/
lemma exists_norm_eq_one : ∃ v : E, ‖v‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  refine ⟨‖v‖⁻¹ • v, ?_⟩
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm : ‖(‖v‖⁻¹ : ℝ)‖ = ‖v‖⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  rw [norm_smul, hnorm]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

/-- The set of unit-vector Rayleigh values is bounded below. -/
lemma bddBelow_rect (H : E →L[ℂ] E) : BddBelow (rect H) := by
  refine ⟨-‖H‖, ?_⟩
  rintro x ⟨v, hv, rfl⟩
  have h := rayleigh_neg_le H v
  rw [hv] at h
  simpa using h

/-- The set of Rayleigh values on unit vectors in a subspace is bounded below. -/
lemma bddBelow_sectionSet (S : Submodule ℂ E) (H : E →L[ℂ] E) :
    BddBelow (sectionSet S H) := by
  refine ⟨-‖H‖, ?_⟩
  rintro x ⟨v, ⟨hv, _⟩, rfl⟩
  have h := rayleigh_neg_le H v
  rw [hv] at h
  simpa using h

/-- The set of unit-vector Rayleigh values is nonempty. -/
lemma rect_nonempty (H : E →L[ℂ] E) : (rect H).Nonempty := by
  obtain ⟨v, hv⟩ := exists_norm_eq_one (E := E)
  exact ⟨rayleigh H v, v, hv, rfl⟩

/-- A nonzero subspace has a nonempty set of unit-vector Rayleigh values. -/
lemma sectionSet_nonempty (S : Submodule ℂ E) (H : E →L[ℂ] E) (hS : S ≠ ⊥) :
    (sectionSet S H).Nonempty := by
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  refine ⟨rayleigh H (‖v‖⁻¹ • v), ‖v‖⁻¹ • v, ⟨?_, S.smul_mem _ hvS⟩, rfl⟩
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hnorm : ‖(‖v‖⁻¹ : ℝ)‖ = ‖v‖⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  rw [norm_smul, hnorm]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

/-- The subspace energy is at most the Rayleigh value of any unit vector in that subspace. -/
lemma sectionEnergy_le_rayleigh (S : Submodule ℂ E) (H : E →L[ℂ] E)
    {v : E} (hv : ‖v‖ = 1) (hvS : v ∈ S) :
    sectionEnergy S H ≤ rayleigh H v :=
  csInf_le (bddBelow_sectionSet S H) ⟨v, ⟨hv, hvS⟩, rfl⟩

/-- For a vector in `S`, its Rayleigh value is at least `sectionEnergy S H * ‖v‖^2`. -/
lemma sectionEnergy_mul_le (S : Submodule ℂ E) (H : E →L[ℂ] E)
    {v : E} (hvS : v ∈ S) :
    sectionEnergy S H * ‖v‖ ^ 2 ≤ rayleigh H v := by
  by_cases hv : v = 0
  · subst hv
    simp [rayleigh]
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
      have hnorm : ‖(‖v‖⁻¹ : ℝ)‖ = ‖v‖⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      rw [norm_smul, hnorm]
      exact inv_mul_cancel₀ (ne_of_gt hpos)
    have hmem : (‖v‖⁻¹ : ℝ) • v ∈ S := S.smul_mem _ hvS
    have hle := sectionEnergy_le_rayleigh S H hunit hmem
    rw [rayleigh_smul_real] at hle
    have hpow : ((‖v‖ ^ 2)⁻¹ : ℝ) = (‖v‖⁻¹) ^ 2 := by rw [inv_pow]
    have hle' : sectionEnergy S H ≤ rayleigh H v / ‖v‖ ^ 2 := by
      rw [div_eq_inv_mul, hpow]
      exact hle
    calc
      sectionEnergy S H * ‖v‖ ^ 2 ≤ (rayleigh H v / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hle' (le_of_lt (by positivity))
      _ = rayleigh H v := div_mul_cancel₀ _ (ne_of_gt (by positivity))

/-- For a nonzero subspace, the section energy is at most the operator norm. -/
lemma sectionEnergy_le_norm (S : Submodule ℂ E) (H : E →L[ℂ] E) (hS : S ≠ ⊥) :
    sectionEnergy S H ≤ ‖H‖ := by
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
    have hnorm : ‖(‖v‖⁻¹ : ℝ)‖ = ‖v‖⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    rw [norm_smul, hnorm]
    exact inv_mul_cancel₀ (ne_of_gt hpos)
  have hmem : (‖v‖⁻¹ : ℝ) • v ∈ S := S.smul_mem _ hvS
  calc
    sectionEnergy S H ≤ rayleigh H (‖v‖⁻¹ • v) :=
      sectionEnergy_le_rayleigh S H hunit hmem
    _ = (‖v‖⁻¹) ^ 2 * rayleigh H v := rayleigh_smul_real H _ v
    _ ≤ (‖v‖⁻¹) ^ 2 * (‖H‖ * ‖v‖ ^ 2) := by
        gcongr
        exact rayleigh_le H v
    _ = ‖H‖ := by
        have hsq : (‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2 = 1 := by
          rw [inv_pow]
          exact inv_mul_cancel₀ (ne_of_gt (by positivity))
        calc
          (‖v‖⁻¹) ^ 2 * (‖H‖ * ‖v‖ ^ 2) = ‖H‖ * ((‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2) := by ring
          _ = ‖H‖ := by rw [hsq, mul_one]

end Qatlib.Papers.LocalHam06.MainResults.OperatorDefs
