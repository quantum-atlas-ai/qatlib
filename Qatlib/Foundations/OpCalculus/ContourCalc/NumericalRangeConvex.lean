/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Physlib.QuantumMechanics.Operators.SpectralTheory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open Qatlib.Foundations.OpCalculus.ContourCalc

/-!
Auxiliary geometric lemmas for the Toeplitz--Hausdorff proof.  The real
three-dimensional sphere has a convex image under every real-linear map to
the complex plane.  Connecting this representation to actual Rayleigh
quotients is proved by identifying the actual range with the total-domain
partial-map model used by the pinned Physlib Toeplitz--Hausdorff theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Foundations.OpCalculus.ContourCalc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Moving along a nonzero kernel vector lifts every vector in the unit ball
to the unit sphere without changing its linear image. -/
theorem exists_unit_vector_same_linear_image
    (L : F →ₗ[ℝ] ℂ) (v : F) (hv : v ≠ 0) (hLv : L v = 0)
    (x : F) (hx : ‖x‖ ≤ 1) :
    ∃ y : F, ‖y‖ = 1 ∧ L y = L x := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let T : ℝ := (2 + ‖x‖) / ‖v‖
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have htv : ‖T • v‖ = 2 + ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]
    dsimp [T]
    exact div_mul_cancel₀ _ hvn.ne'
  have htriangle : ‖T • v‖ ≤ ‖x + T • v‖ + ‖x‖ := by
    have h := norm_add_le (x + T • v) (-x)
    simpa only [add_neg_cancel_comm, norm_neg] using h
  have hlarge : 1 ≤ ‖x + T • v‖ := by rw [htv] at htriangle; linarith
  have hcontinuous : Continuous (fun t : ℝ => ‖x + t • v‖) := by fun_prop
  have hone : 1 ∈ Set.Icc (‖x + (0 : ℝ) • v‖) (‖x + T • v‖) := by
    simpa using And.intro hx hlarge
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hT hcontinuous.continuousOn hone
  refine ⟨x + t • v, ht, ?_⟩
  rw [L.map_add, L.map_smul, hLv, smul_zero, add_zero]

/-- A nontrivial kernel makes the unit-sphere image equal the unit-ball image. -/
theorem linear_image_unit_sphere_eq_unit_ball
    (L : F →ₗ[ℝ] ℂ) (hker : ∃ v : F, v ≠ 0 ∧ L v = 0) :
    L '' Metric.sphere (0 : F) 1 = L '' Metric.closedBall (0 : F) 1 := by
  obtain ⟨v, hv, hLv⟩ := hker
  apply Set.Subset.antisymm
  · exact Set.image_mono Metric.sphere_subset_closedBall
  · rintro z ⟨x, hx, rfl⟩
    have hxn : ‖x‖ ≤ 1 := by simpa using hx
    obtain ⟨y, hy, hLy⟩ := exists_unit_vector_same_linear_image L v hv hLv x hxn
    exact ⟨y, by simpa using hy, hLy⟩

/-- Every real-linear map from real three-space to the complex plane has a
nonzero kernel vector, since the codomain has real dimension two. -/
theorem real_three_to_complex_has_kernel
    (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ) :
    ∃ v, v ≠ 0 ∧ L v = 0 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective L := by
    intro x y hxy
    by_contra hne
    have hzero : L (x - y) = 0 := by rw [L.map_sub, hxy, sub_self]
    exact h (x - y) (sub_ne_zero.mpr hne) hzero
  have hdim := L.finrank_le_finrank_of_injective hinj
  norm_num [finrank_euclideanSpace_fin, Complex.finrank_real_complex] at hdim

/-- The Bloch-sphere geometric step: all real-linear images of the real
three-dimensional unit sphere in the complex plane are convex. -/
theorem convex_real_three_sphere_linear_image
    (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ) :
    Convex ℝ (L '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  rw [linear_image_unit_sphere_eq_unit_ball L (real_three_to_complex_has_kernel L)]
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).linear_image L

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The actual continuous-linear-map Rayleigh quotients equal the pinned
Physlib partial-map range when its domain is the whole space. -/
theorem numericalRange_eq_total_linearPMap (A : E →L[ℂ] E) :
    numericalRange A = (A.toLinearMap.toPMap ⊤).numericalRange := by
  ext z
  constructor
  · rintro ⟨x, hx, hquot⟩
    exact ⟨⟨x, Submodule.mem_top⟩, hx, hquot⟩
  · rintro ⟨x, hx, hquot⟩
    exact ⟨x.val, hx, hquot⟩

/-- G12: the actual complex numerical range is real convex.  The reused
Toeplitz--Hausdorff theorem is proved in pinned Physlib; no convexity or
convex enclosure is supplied as a premise.  Finite dimensionality is not
needed for this stronger statement, so zero-dimensional spaces are covered. -/
theorem numericalRange_convex (A : E →L[ℂ] E) : Convex ℝ (numericalRange A) := by
  rw [numericalRange_eq_total_linearPMap]
  exact LinearPMap.numericalRange_convex _

end Qatlib.Foundations.OpCalculus.ContourCalc
