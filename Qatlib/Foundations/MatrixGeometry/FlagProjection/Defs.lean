/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.FlagProjection
open scoped BigOperators
variable {X : Type*} [DecidableEq X]

def project (S : Finset X) (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => if x ∈ S then v.ofLp x else 0)

def mass (S : Finset X) (v : EuclideanSpace ℂ X) : ℝ :=
  ∑ x ∈ S, ‖v.ofLp x‖ ^ 2

theorem project_add (S : Finset X) (v u : EuclideanSpace ℂ X) :
    project S (v+u) = project S v + project S u := by
  ext x
  by_cases hx : x ∈ S <;> simp [project, hx]

theorem project_smul (S : Finset X) (c : ℂ) (v : EuclideanSpace ℂ X) :
    project S (c • v) = c • project S v := by
  ext x
  by_cases hx : x ∈ S <;> simp [project, hx]

theorem project_idem (S : Finset X) (v : EuclideanSpace ℂ X) :
    project S (project S v) = project S v := by
  ext x
  by_cases hx : x ∈ S <;> simp [project, hx]

omit [DecidableEq X] in

theorem mass_nonneg (S : Finset X) (v : EuclideanSpace ℂ X) : 0 ≤ mass S v := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem project_norm_sq [Fintype X] (S : Finset X) (v : EuclideanSpace ℂ X) :
    ‖project S v‖ ^ 2 = mass S v := by
  rw [EuclideanSpace.norm_sq_eq]
  have he (x : X) : ‖(if x ∈ S then v.ofLp x else (0 : ℂ))‖ ^ 2 =
      if x ∈ S then ‖v.ofLp x‖ ^ 2 else 0 := by
    by_cases hx : x ∈ S <;> simp [hx]
  simp only [project, WithLp.ofLp_toLp, he]
  simp [mass]

theorem project_inner [Fintype X] (S : Finset X) (v : EuclideanSpace ℂ X) :
    inner ℂ (project S v) v = (mass S v : ℂ) := by
  rw [PiLp.inner_apply]
  change (∑ x, inner ℂ (if x ∈ S then v.ofLp x else 0) (v.ofLp x)) = _
  have he (x : X) : inner ℂ (if x ∈ S then v.ofLp x else 0) (v.ofLp x) =
      if x ∈ S then (‖v.ofLp x‖ : ℂ)^2 else 0 := by
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx, inner_self_eq_norm_sq_to_K]
      rfl
    · simp [hx]
  simp_rw [he]
  simp [mass]

noncomputable def tail (S : Finset X) (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  ((Real.sqrt (mass S v) : ℂ)⁻¹) • project S v

theorem project_tail (S : Finset X) (v : EuclideanSpace ℂ X) :
    project S (tail S v) = tail S v := by
  simp [tail, project_smul, project_idem]

theorem project_source (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) :
    project S v = (Real.sqrt (mass S v) : ℂ) • tail S v := by
  have hs : (Real.sqrt (mass S v) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hp)
  simp [tail, smul_smul, hs]

theorem tail_unit [Fintype X] (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) :
    inner ℂ (tail S v) (tail S v) = 1 := by
  have hnorm : ‖tail S v‖^2 = 1 := by
    rw [tail, norm_smul, mul_pow, project_norm_sq]
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hp.le, ne_of_gt hp]
  rw [inner_self_eq_norm_sq_to_K]
  simpa only [map_pow, map_one] using congrArg (algebraMap ℝ ℂ) hnorm

theorem tail_inner [Fintype X] (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) :
    inner ℂ (tail S v) v = (Real.sqrt (mass S v) : ℂ) := by
  have hs : (Real.sqrt (mass S v) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hp)
  have hsq : (Real.sqrt (mass S v) : ℂ)^2 = (mass S v : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  rw [tail, inner_smul_left, project_inner]
  simp only [map_inv₀, Complex.conj_ofReal]
  rw [← hsq]
  field_simp
end Qatlib.Foundations.MatrixGeometry.FlagProjection
