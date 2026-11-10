/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Qatlib.Foundations.MatrixAlgebra.FrameProject
variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem analysis_bound_of_synthesis (F : I → E) (c : ℝ) (hc : 0 < c)
    (hF : ∀ a : I → ℂ, c * (∑ i, ‖a i‖^2) ≤ ‖∑ i, a i • F i‖^2)
    (w : E) (hw : w ∈ Submodule.span ℂ (Set.range F)) :
    c * ‖w‖^2 ≤ ∑ i, ‖inner ℂ (F i) w‖^2 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  let av : EuclideanSpace ℂ I := WithLp.toLp 2 a
  let yv : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => inner ℂ (F i) w)
  have hinner : inner ℂ av yv = inner ℂ w w := by
    calc
      inner ℂ av yv = ∑ i, star (a i) * inner ℂ (F i) w := by
        simp [PiLp.inner_apply, RCLike.inner_apply, av, yv, mul_comm]
      _ = inner ℂ (∑ i, a i • F i) w := by simp [sum_inner, inner_smul_left]
      _ = inner ℂ w w := by rw [ha]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) av yv
  rw [hinner, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg w)] at hcs
  have hs : (‖w‖^2)^2 ≤ (‖av‖*‖yv‖)^2 :=
    pow_le_pow_left₀ (by positivity) hcs 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  have hl := hF a
  rw [ha] at hl
  change c * (∑ i, ‖a i‖^2) ≤ ‖w‖^2 at hl
  change (‖w‖^2)^2 ≤ (∑ i, ‖a i‖^2) * (∑ i, ‖inner ℂ (F i) w‖^2) at hs
  have hy : 0 ≤ ∑ i, ‖inner ℂ (F i) w‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs' := mul_le_mul_of_nonneg_left hs hc.le
  have hl' := mul_le_mul_of_nonneg_right hl hy
  by_cases hw0 : ‖w‖=0
  · simpa [hw0] using hy
  · have hp : 0 < ‖w‖^2 := sq_pos_of_ne_zero hw0
    nlinarith

theorem synthesis_bound_subtype (F : I → E) (c : ℝ)
    (hF : ∀ a : I → ℂ, c * (∑ i, ‖a i‖^2) ≤ ‖∑ i, a i • F i‖^2)
    (p : I → Prop) [DecidablePred p] (a : {i // p i} → ℂ) :
    c * (∑ i, ‖a i‖^2) ≤ ‖∑ i : {i // p i}, a i • F i‖^2 := by
  let b : I → ℂ := fun i => if h : p i then a ⟨i,h⟩ else 0
  have hb1 (i : {i // p i}) : b i = a i := dif_pos i.property
  have hb0 (i : {i // ¬p i}) : b i = 0 := dif_neg i.property
  have hb : (∑ i, ‖b i‖^2) = ∑ i, ‖a i‖^2 := by
    have hs := Fintype.sum_subtype_add_sum_subtype p (fun i => ‖b i‖^2)
    simpa only [hb1, hb0, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), Finset.sum_const_zero,
        add_zero] using hs.symm
  have hv : (∑ i, b i • F i) = ∑ i : {i // p i}, a i • F i := by
    have hs := Fintype.sum_subtype_add_sum_subtype p (fun i => b i • F i)
    simpa only [hb1, hb0, zero_smul, Finset.sum_const_zero, add_zero] using hs.symm
  simpa only [hb, hv] using hF b

theorem orthonormal_analysis_bound [FiniteDimensional ℂ E]
    {J : Type*} [Fintype J] (F : I → E) (c : ℝ) (hc : 0<c)
    (hF : ∀ a : I → ℂ, c * (∑ i, ‖a i‖^2) ≤ ‖∑ i, a i • F i‖^2)
    (u : J → E) (hu : Orthonormal ℂ u)
    (hspan : ∀ j, u j ∈ Submodule.span ℂ (Set.range F)) (v : E) :
    c * (∑ j, ‖inner ℂ (u j) v‖^2) ≤ ∑ i, ‖inner ℂ (F i) v‖^2 := by
  let S := Submodule.span ℂ (Set.range F)
  have heq (z : E) (hz : z ∈ S) : inner ℂ z (S.starProjection v)=inner ℂ z v := by
    calc
      _ = inner ℂ (S.starProjection z) v :=
        (Submodule.inner_starProjection_left_eq_right S z v).symm
      _ = _ := by rw [S.starProjection_eq_self_iff.mpr hz]
  have hb := hu.sum_inner_products_le (s := Finset.univ) (S.starProjection v)
  simp only [heq _ (hspan _)] at hb
  have ha := analysis_bound_of_synthesis F c hc hF (S.starProjection v)
    (S.starProjection_apply_mem v)
  have hFm (i : I) : F i ∈ S := Submodule.subset_span (Set.mem_range_self i)
  simp only [heq _ (hFm _)] at ha
  exact (mul_le_mul_of_nonneg_left hb hc.le).trans ha

end Qatlib.Foundations.MatrixAlgebra.FrameProject
