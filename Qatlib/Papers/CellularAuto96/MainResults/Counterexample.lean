/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# A finite-torus counterexample to volume-only sizing

This module constructs a homogeneous unitary scalar kernel on `ZMod 8 × ZMod 4` with two nonzero
displacement weights. It satisfies the displayed volume inequality while failing to be a scalar
multiple of a translation, illustrating the finite-size scope issue considered alongside
[Meyer1996].

## Main statements

* `torusKernel_unitary`: proves unitarity of the explicit kernel.
* `torusStep_not_translation`: rules out a single-translation evolution formula.
* `source_sizing_counterexample`: collects the size, homogeneity, support, and nontranslation
  properties.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

namespace Qatlib.Papers.CellularAuto96.MainResults.SourceCounter

/-- The complex coefficient `(1 + i) / 2` for the positive cyclic displacement. -/
def alpha : ℂ := (1+Complex.I)/2

/-- The complex coefficient `(1 - i) / 2` for the negative cyclic displacement. -/
def beta : ℂ := (1-Complex.I)/2

/-- The weight on `ZMod 4` supported at displacements one and minus one, with coefficients
`alpha` and `beta`. -/
def cyclicWeight (e : ZMod 4) : ℂ :=
  (if e=1 then alpha else 0) + (if e= -1 then beta else 0)

/-- The cyclic transition matrix with entry `cyclicWeight (y - x)`. -/
def cyclicKernel : Matrix (ZMod 4) (ZMod 4) ℂ := fun x y => cyclicWeight (y-x)
set_option maxHeartbeats 600000 in

/-- The explicit four-site cyclic kernel is unitary. -/
theorem cyclicKernel_unitary : cyclicKernel ∈ Matrix.unitaryGroup (ZMod 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hu : (Finset.univ : Finset (ZMod 4)) = {0,1,2,3} := by decide
  have hm : (-1 : ZMod 4) = 3 := by decide
  have hsub00 : ((0 : ZMod 4) - 0) = 0 := by decide
  have hsub01 : ((0 : ZMod 4) - 1) = 3 := by decide
  have hsub02 : ((0 : ZMod 4) - 2) = 2 := by decide
  have hsub03 : ((0 : ZMod 4) - 3) = 1 := by decide
  have hsub10 : ((1 : ZMod 4) - 0) = 1 := by decide
  have hsub11 : ((1 : ZMod 4) - 1) = 0 := by decide
  have hsub12 : ((1 : ZMod 4) - 2) = 3 := by decide
  have hsub13 : ((1 : ZMod 4) - 3) = 2 := by decide
  have hsub20 : ((2 : ZMod 4) - 0) = 2 := by decide
  have hsub21 : ((2 : ZMod 4) - 1) = 1 := by decide
  have hsub22 : ((2 : ZMod 4) - 2) = 0 := by decide
  have hsub23 : ((2 : ZMod 4) - 3) = 3 := by decide
  have hsub30 : ((3 : ZMod 4) - 0) = 3 := by decide
  have hsub31 : ((3 : ZMod 4) - 1) = 2 := by decide
  have hsub32 : ((3 : ZMod 4) - 2) = 1 := by decide
  have hsub33 : ((3 : ZMod 4) - 3) = 0 := by decide
  have hne01 : (0 : ZMod 4) ≠ 1 := by decide
  have hne02 : (0 : ZMod 4) ≠ 2 := by decide
  have hne03 : (0 : ZMod 4) ≠ 3 := by decide
  have hne12 : (1 : ZMod 4) ≠ 2 := by decide
  have hne13 : (1 : ZMod 4) ≠ 3 := by decide
  have hne23 : (2 : ZMod 4) ≠ 3 := by decide
  have hall : ∀ x : ZMod 4, x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by decide
  ext x y
  rcases hall x with rfl | rfl | rfl | rfl <;>
    rcases hall y with rfl | rfl | rfl | rfl
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub00, if_neg, hne12, hne13, hsub01, Ne.symm hne13, if_pos, hne23, hsub02, Ne.symm hne12, Finset.sum_singleton, hsub03, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub00, if_neg, hsub10, if_pos, hne13, hne12, hsub01, Ne.symm hne13, hsub11, hne23, hsub02, Ne.symm hne12, hsub12, Finset.sum_singleton, hsub03, hsub13, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub00, if_neg, hsub20, Ne.symm hne12, hne23, hne12, hne13, hsub01, Ne.symm hne13, if_pos, hsub21, hsub02, hsub22, Finset.sum_singleton, hsub03, hsub23, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub00, if_neg, hsub30, Ne.symm hne13, if_pos, hne12, hne13, hsub01, hsub31, Ne.symm hne12, hne23, hsub02, hsub32, Finset.sum_singleton, hsub03, hsub33, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub10, if_pos, hne13, if_neg, hsub00, hne12, hsub11, hsub01, Ne.symm hne13, hne23, hsub12, hsub02, Ne.symm hne12, Finset.sum_singleton, hsub13, hsub03, one_apply, Ne.symm hne01]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub10, if_pos, hne13, if_neg, hne12, hsub11, hne23, hsub12, Ne.symm hne13, Finset.sum_singleton, hsub13, Ne.symm hne12, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub10, if_pos, hne13, if_neg, hsub20, Ne.symm hne12, hne23, hne12, hsub11, hsub21, hsub12, Ne.symm hne13, hsub22, Finset.sum_singleton, hsub13, hsub23, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub10, if_pos, hne13, if_neg, hsub30, Ne.symm hne13, hne12, hsub11, hsub31, Ne.symm hne12, hne23, hsub12, hsub32, Finset.sum_singleton, hsub13, hsub33, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub20, Ne.symm hne12, if_neg, hne23, hsub00, hne12, hne13, hsub21, if_pos, hsub01, Ne.symm hne13, hsub22, hsub02, Finset.sum_singleton, hsub23, hsub03, one_apply, Ne.symm hne02]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub20, Ne.symm hne12, if_neg, hne23, hsub10, if_pos, hne13, hne12, hsub21, hsub11, hsub22, hsub12, Ne.symm hne13, Finset.sum_singleton, hsub23, hsub13, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub20, Ne.symm hne12, if_neg, hne23, hne12, hne13, hsub21, if_pos, hsub22, Finset.sum_singleton, hsub23, Ne.symm hne13, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub20, Ne.symm hne12, if_neg, hne23, hsub30, Ne.symm hne13, if_pos, hne12, hne13, hsub21, hsub31, hsub22, hsub32, Finset.sum_singleton, hsub23, hsub33, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub30, Ne.symm hne13, if_neg, if_pos, hsub00, hne12, hne13, hsub31, Ne.symm hne12, hne23, hsub01, hsub32, hsub02, Finset.sum_singleton, hsub33, hsub03, one_apply, Ne.symm hne03]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub30, Ne.symm hne13, if_neg, if_pos, hsub10, hne13, hne12, hsub31, Ne.symm hne12, hne23, hsub11, hsub32, hsub12, Finset.sum_singleton, hsub33, hsub13, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub30, Ne.symm hne13, if_neg, if_pos, hsub20, Ne.symm hne12, hne23, hne12, hne13, hsub31, hsub21, hsub32, hsub22, Finset.sum_singleton, hsub33, hsub23, one_apply, Ne.symm hne23]
    norm_num [alpha,beta,Complex.ext_iff]
  · simp only [mul_apply, hu, star_apply, cyclicKernel, cyclicWeight, hm, Finset.mem_insert, hne01, hne02, Finset.mem_singleton, hne03, or_self, not_false_eq_true, Finset.sum_insert, hsub30, Ne.symm hne13, if_neg, if_pos, hne12, hne13, hsub31, Ne.symm hne12, hne23, hsub32, Finset.sum_singleton, hsub33, one_apply]
    norm_num [alpha,beta,Complex.ext_iff]

/-- The finite torus `ZMod 8 × ZMod 4` used for the sizing counterexample. -/
abbrev Torus := ZMod 8 × ZMod 4

/-- The torus displacement `(0, 1)`. -/
def cellPlus : Torus := (0,1)

/-- The torus displacement `(0, -1)`. -/
def cellMinus : Torus := (0,-1)

/-- The torus weight supported at `cellPlus` and `cellMinus`, with coefficients `alpha` and
`beta`. -/
def torusWeight (e : Torus) : ℂ :=
  (if e=cellPlus then alpha else 0) + (if e=cellMinus then beta else 0)

/-- The torus transition matrix with entry `torusWeight (y - x)`. -/
def torusKernel : Matrix Torus Torus ℂ := fun x y => torusWeight (y-x)

/-- The torus kernel is the tensor product of the identity on `ZMod 8` and the cyclic kernel on
`ZMod 4`. -/
theorem torusKernel_tensor : torusKernel =
    TensorGate (1 : Matrix (ZMod 8) (ZMod 8) ℂ) cyclicKernel := by
  ext ⟨x,a⟩ ⟨y,b⟩
  by_cases h : y=x
  · subst y
    simp [torusKernel,torusWeight,cellPlus,cellMinus,TensorGate,cyclicKernel,cyclicWeight,Prod.ext_iff]
  · have h' : x ≠ y := Ne.symm h
    simp [torusKernel,torusWeight,cellPlus,cellMinus,TensorGate,cyclicKernel,cyclicWeight,
      Prod.ext_iff,sub_eq_zero,h,h']

/-- The explicit torus kernel is unitary. -/
theorem torusKernel_unitary : torusKernel ∈ Matrix.unitaryGroup Torus ℂ := by
  rw [torusKernel_tensor]
  exact tensorGate_unitary (Submonoid.one_mem _) cyclicKernel_unitary

/-- Simultaneously translating the row and column indices leaves the torus kernel unchanged. -/
theorem torusKernel_homogeneous (t x y : Torus) :
    torusKernel (x+t) (y+t) = torusKernel x y := by
  simp only [torusKernel,add_sub_add_right_eq_sub]

/-- The numerical volume inequality `1 + 4 * (1 + 4) * 1 ≤ 8 * 4` holds for the chosen torus
dimensions. -/
theorem source_volume_condition : 1+4*(1+4)*1 ≤ 8*4 := by norm_num

/-- The two chosen torus displacements are distinct and both carry nonzero weights. -/
theorem two_nonzero_weights : cellPlus ≠ cellMinus ∧ torusWeight cellPlus ≠ 0 ∧ torusWeight cellMinus ≠ 0 := by
  have hd : (1 : ZMod 4) ≠ -1 := by decide
  norm_num [cellPlus,cellMinus,torusWeight,alpha,beta,hd,Ne.symm hd,Complex.ext_iff]

/-- The torus kernel acts as `alpha` times the positive displacement of the state plus `beta`
times its negative displacement. -/
theorem torusKernel_step (φ : Torus → ℂ) (x : Torus) :
    (torusKernel *ᵥ φ) x = alpha*φ (x+cellPlus) + beta*φ (x+cellMinus) := by
  simp [Matrix.mulVec,dotProduct,torusKernel,torusWeight,add_mul,
    Finset.sum_add_distrib,sub_eq_iff_eq_add,add_comm]

/-- The torus kernel cannot be represented as the matrix of a single translation multiplied by a
scalar. -/
theorem torusKernel_not_translation :
    ¬ ∃ (e : Torus) (c : ℂ), ∀ x y,
      torusKernel x y = if y=x+e then c else 0 := by
  rintro ⟨e,c,h⟩
  have hp : torusKernel 0 cellPlus ≠ 0 := by simpa [torusKernel] using two_nonzero_weights.2.1
  have hm : torusKernel 0 cellMinus ≠ 0 := by simpa [torusKernel] using two_nonzero_weights.2.2
  have hep : cellPlus=e := by
    by_contra he
    have hh := h 0 cellPlus
    simp only [zero_add,if_neg he] at hh
    exact hp hh
  have hem : cellMinus=e := by
    by_contra he
    have hh := h 0 cellMinus
    simp only [zero_add,if_neg he] at hh
    exact hm hh
  exact two_nonzero_weights.1 (hep.trans hem.symm)

/-- Every displacement with nonzero torus weight is either `cellPlus` or `cellMinus`. -/
theorem torusWeight_support (e : Torus) (h : torusWeight e ≠ 0) :
    e=cellPlus ∨ e=cellMinus := by
  by_cases hp : e=cellPlus
  · exact Or.inl hp
  · by_cases hm : e=cellMinus
    · exact Or.inr hm
    · simp only [torusWeight,if_neg hp,if_neg hm,zero_add] at h
      exact (h rfl).elim

/-- No fixed displacement and scalar express the torus kernel action as a scalar multiple of
translation on every state function. -/
theorem torusStep_not_translation :
    ¬ ∃ (e : Torus) (c : ℂ), ∀ (φ : Torus → ℂ) (x : Torus),
      (torusKernel *ᵥ φ) x = c*φ (x+e) := by
  rintro ⟨e,c,h⟩
  apply torusKernel_not_translation
  refine ⟨e,c,?_⟩
  intro x y
  have hh := h (fun z => if z=y then 1 else 0) x
  simpa [Matrix.mulVec,dotProduct,mul_ite,eq_comm] using hh

/-- The 32-site torus satisfies the displayed volume inequality and carries the explicit
homogeneous unitary kernel supported on two displacements, whose action is not a scalar
multiple of translation. This provides the finite sizing counterexample considered here
alongside [Meyer1996]. -/
theorem source_sizing_counterexample :
    Fintype.card Torus = 32 ∧ 1 + 4 * (1 + 4) * 1 ≤ Fintype.card Torus ∧
      torusKernel ∈ Matrix.unitaryGroup Torus ℂ ∧
      (∀ t x y : Torus, torusKernel (x+t) (y+t) = torusKernel x y) ∧
      (∀ e, torusWeight e ≠ 0 → e = cellPlus ∨ e = cellMinus) ∧
      (¬ ∃ (e : Torus) (c : ℂ), ∀ (φ : Torus → ℂ) (x : Torus),
        (torusKernel *ᵥ φ) x = c * φ (x+e)) := by
  have hcard : Fintype.card Torus = 32 := by decide
  exact ⟨hcard, hcard ▸ source_volume_condition, torusKernel_unitary,
    torusKernel_homogeneous, torusWeight_support, torusStep_not_translation⟩

end Qatlib.Papers.CellularAuto96.MainResults.SourceCounter
