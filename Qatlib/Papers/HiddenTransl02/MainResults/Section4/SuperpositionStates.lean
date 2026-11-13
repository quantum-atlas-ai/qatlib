/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

/-!
# Uniform subgroup and coset states

This module defines the uniform amplitude functions `subgroupState` and `cosetState` used in the
subgroup and translating-coset superpositions of [FriedlEtAl2014]. It proves their
normalization, characterizes their supports, and establishes invariance of subgroup states under
subgroup multiplication.

## Main statements

* `normalized_subgroupState`: proves normalization of the uniform subgroup state.
* `normalized_cosetState`: proves normalization of the uniform left-coset state.

## References

* [Friedl et al., 2014][FriedlEtAl2014]
-/

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section4

open Qatlib.Foundations.PureStateMath
open scoped Classical

set_option autoImplicit false

noncomputable section

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The complex amplitude `1 / sqrt m` used for uniform superpositions. -/
def uniformAmplitude (m : ℕ) : ℂ := ((Real.sqrt (m : ℝ) : ℂ))⁻¹

/-- The amplitude function equal to `1 / sqrt |H|` on `H` and zero outside `H`. -/
def subgroupState (H : Subgroup G) [Fintype H] : QState G :=
  fun x => if x ∈ H then uniformAmplitude (Fintype.card H) else 0

/-- The amplitude function equal to `1 / sqrt |H|` on the left coset `uH` and zero outside it. -/
def cosetState (u : G) (H : Subgroup G) [Fintype H] : QState G :=
  fun x => if u⁻¹ * x ∈ H then uniformAmplitude (Fintype.card H) else 0

section Subgroup

variable (H : Subgroup G) [Fintype H]

omit [Fintype G] [DecidableEq G] in

/-- The uniform amplitude for the cardinality of a finite subgroup is nonzero. -/
theorem uniformAmplitude_ne_zero : uniformAmplitude (Fintype.card H) ≠ 0 := by
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card H : ℝ) := Real.sqrt_pos_of_pos hcard
  have hne : (Real.sqrt (Fintype.card H : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsqrt
  unfold uniformAmplitude
  exact inv_ne_zero hne

omit [Fintype G] [DecidableEq G] in

/-- The norm of the uniform amplitude for `H` is `1 / sqrt |H|`. -/
theorem norm_uniformAmplitude :
    ‖uniformAmplitude (Fintype.card H)‖ = (Real.sqrt (Fintype.card H : ℝ))⁻¹ := by
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card H : ℝ) := Real.sqrt_pos_of_pos hcard
  unfold uniformAmplitude
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]

/-- The subgroup-state amplitude at `x` is nonzero exactly when `x ∈ H`. -/
theorem subgroupState_ne_zero_iff {x : G} :
    subgroupState H x ≠ 0 ↔ x ∈ H := by
  unfold subgroupState
  constructor
  · intro h
    by_contra hx
    exact h (ite_eq_right hx)
  · intro hx
    rw [ite_eq_left hx]
    exact uniformAmplitude_ne_zero H

/-- The uniform subgroup state is normalized, as required for subgroup superposition in
[FriedlEtAl2014]. -/
theorem normalized_subgroupState : Normalized (subgroupState H) := by
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hstep : ∀ x : G,
      ‖subgroupState H x‖ ^ 2 =
        if x ∈ H then (Fintype.card H : ℝ)⁻¹ else 0 := by
    intro x
    unfold subgroupState
    by_cases hx : x ∈ H
    · rw [ite_eq_left hx, ite_eq_left hx, norm_uniformAmplitude H, inv_pow,
        Real.sq_sqrt (show (0:ℝ) ≤ (Fintype.card H : ℝ) by positivity)]
    · rw [ite_eq_right hx, ite_eq_right hx, norm_zero, zero_pow (by norm_num)]
  unfold Normalized
  simp only [hstep]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard' : (Finset.univ.filter (fun x : G => x ∈ H)).card = Fintype.card H := by
    have hset : (Finset.univ.filter (fun x : G => x ∈ H))
        = (Finset.univ : Finset H).image (fun h : H => (h : G)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨h, -, rfl⟩; exact h.2⟩
    rw [hset, Finset.card_image_of_injective _ (fun a b hab => Subtype.ext hab),
      Finset.card_univ]
  rw [hcard']
  field_simp

omit [Fintype G] [DecidableEq G] in

/-- Left multiplication by an element of `H` preserves the subgroup-state amplitude. -/
theorem subgroupState_mul_left {h x : G} (hh : h ∈ H) :
    subgroupState H (h * x) = subgroupState H x := by
  unfold subgroupState
  by_cases hx : x ∈ H
  · rw [ite_eq_left (H.mul_mem hh hx), ite_eq_left hx]
  · rw [ite_eq_right (fun hmem => hx ?_), ite_eq_right hx]
    have : h⁻¹ * (h * x) ∈ H := H.mul_mem (H.inv_mem hh) hmem
    simpa using this

omit [Fintype G] [DecidableEq G] in

/-- Right multiplication by an element of `H` preserves the subgroup-state amplitude. -/
theorem subgroupState_mul_right {h x : G} (hh : h ∈ H) :
    subgroupState H (x * h) = subgroupState H x := by
  unfold subgroupState
  by_cases hx : x ∈ H
  · rw [ite_eq_left (H.mul_mem hx hh), ite_eq_left hx]
  · rw [ite_eq_right (fun hmem => hx ?_), ite_eq_right hx]
    have : (x * h) * h⁻¹ ∈ H := H.mul_mem hmem (H.inv_mem hh)
    simpa using this

end Subgroup

section Coset

variable (H : Subgroup G) [Fintype H]

/-- The coset-state amplitude at `x` is nonzero exactly when `u⁻¹ * x ∈ H`. -/
theorem cosetState_ne_zero_iff (u : G) {x : G} :
    cosetState u H x ≠ 0 ↔ u⁻¹ * x ∈ H := by
  unfold cosetState
  constructor
  · intro h
    by_contra hx
    exact h (ite_eq_right hx)
  · intro hx
    rw [ite_eq_left hx]
    exact uniformAmplitude_ne_zero H

/-- The uniform state on the left coset represented by `u` is normalized. -/
theorem normalized_cosetState (u : G) : Normalized (cosetState u H) := by
  have hstep : ∀ x : G,
      ‖cosetState u H x‖ ^ 2 =
        if u⁻¹ * x ∈ H then (Fintype.card H : ℝ)⁻¹ else 0 := by
    intro x
    unfold cosetState
    by_cases hx : u⁻¹ * x ∈ H
    · rw [ite_eq_left hx, ite_eq_left hx, norm_uniformAmplitude H, inv_pow,
        Real.sq_sqrt (show (0:ℝ) ≤ (Fintype.card H : ℝ) by positivity)]
    · rw [ite_eq_right hx, ite_eq_right hx, norm_zero, zero_pow (by norm_num)]
  unfold Normalized
  simp only [hstep]

  have hset : (Finset.univ.filter (fun x : G => u⁻¹ * x ∈ H))
      = (Finset.univ : Finset H).image (fun h : H => u * (h : G)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨⟨u⁻¹ * x, hx⟩, ?_⟩
      simp
    · rintro ⟨h, -, rfl⟩
      simp only [inv_mul_cancel_left]
      exact h.2
  rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul,
    Finset.card_image_of_injective _ (fun a b hab => by
      simpa using mul_left_cancel hab), Finset.card_univ]
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  field_simp

end Coset

end

end Qatlib.Papers.HiddenTransl02.MainResults.Section4
