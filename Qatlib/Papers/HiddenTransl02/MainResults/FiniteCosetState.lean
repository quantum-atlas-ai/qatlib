/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# HiddenTransl02 — exact translating-coset state

This module isolates the state-level content of [FriedlEtAl2014], Corollary 4.6.
For a finite group `G`, a subgroup
`H`, and a translating element `u`, the translating-coset superposition has
constant amplitude `1 / √|H|` on the left coset `uH` and amplitude zero off that
coset.  We prove the exact Euclidean `ℓ₂` normalization, its support, and the
right `H`-invariance used by the translating-coset construction.  The circuit
and its asymptotic running-time bound remain outside this state-level theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HiddenTransl02.MainResults

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Squared Euclidean `ℓ₂` norm of a finite complex amplitude function. -/
def l2NormSq (ψ : G → ℂ) : ℝ := ∑ x : G, ‖ψ x‖ ^ 2

/-- The amplitude used by an exact uniform subgroup/coset state. -/
def uniformAmplitude (m : ℕ) : ℂ := ((Real.sqrt (m : ℝ) : ℂ))⁻¹

/-- Exact translating-coset state for the pair `(u,H)`, with support `uH`. -/
def translatingCosetState (u : G) (H : Subgroup G) [Fintype H] : G → ℂ :=
  by classical exact fun x => if u⁻¹ * x ∈ H then uniformAmplitude (Fintype.card H) else 0

omit [Fintype G] [DecidableEq G] in
private theorem uniformAmplitude_ne_zero (H : Subgroup G) [Fintype H] :
    uniformAmplitude (Fintype.card H) ≠ 0 := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card H : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card H : ℝ) :=
    Real.sqrt_pos.2 hcard
  have hne : (Real.sqrt (Fintype.card H : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsqrt
  exact inv_ne_zero hne

omit [Fintype G] [DecidableEq G] in
private theorem norm_uniformAmplitude (H : Subgroup G) [Fintype H] :
    ‖uniformAmplitude (Fintype.card H)‖ = (Real.sqrt (Fintype.card H : ℝ))⁻¹ := by
  classical
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card H : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast Fintype.card_pos
  unfold uniformAmplitude
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]

omit [Fintype G] [DecidableEq G] in
/-- The exact support predicate for the translating-coset state. -/
theorem translatingCosetState_ne_zero_iff [Fintype G] [DecidableEq G]
    (u : G) (H : Subgroup G) [Fintype H] {x : G} :
    translatingCosetState u H x ≠ 0 ↔ u⁻¹ * x ∈ H := by
  classical
  unfold translatingCosetState
  constructor
  · intro h
    by_contra hx
    exact h (ite_eq_right hx)
  · intro hx
    rw [ite_eq_left hx]
    exact uniformAmplitude_ne_zero H

/-- The translating-coset state has exact Euclidean `ℓ₂` norm one. -/
theorem translatingCosetState_l2NormSq (u : G) (H : Subgroup G) [Fintype H] :
    l2NormSq (translatingCosetState u H) = 1 := by
  classical
  have hstep : ∀ x : G,
      ‖translatingCosetState u H x‖ ^ 2 =
        if u⁻¹ * x ∈ H then (Fintype.card H : ℝ)⁻¹ else 0 := by
    intro x
    unfold translatingCosetState
    by_cases hx : u⁻¹ * x ∈ H
    · rw [ite_eq_left hx, norm_uniformAmplitude H, inv_pow]
      rw [Real.sq_sqrt]
      · simp [hx]
      · exact_mod_cast (Fintype.card H).zero_le
    · simp [hx]
  rw [l2NormSq]
  simp_rw [hstep]
  have hset : (Finset.univ.filter (fun x : G => u⁻¹ * x ∈ H)) =
      (Finset.univ : Finset H).image (fun h : H => u * (h : G)) := by
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
  have hcard : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Fintype G] [DecidableEq G] in
/-- Right multiplication by a subgroup element preserves the exact state. -/
theorem translatingCosetState_mul_right [Fintype G] [DecidableEq G]
    (u : G) (H : Subgroup G) [Fintype H]
    {h x : G} (hh : h ∈ H) :
    translatingCosetState u H (x * h) = translatingCosetState u H x := by
  classical
  unfold translatingCosetState
  by_cases hx : u⁻¹ * x ∈ H
  · have hpos : u⁻¹ * (x * h) ∈ H := by
      simpa [mul_assoc] using H.mul_mem hx hh
    rw [ite_eq_left hpos, ite_eq_left hx]
  · have hnot : u⁻¹ * (x * h) ∉ H := by
      intro hmem
      have hback := H.mul_mem hmem (H.inv_mem hh)
      apply hx
      simpa [mul_assoc] using hback
    rw [ite_eq_right hnot, ite_eq_right hx]

/-- Main state-level theorem for the translating-coset superposition. -/
theorem translatingCosetState_spec (u : G) (H : Subgroup G) [Fintype H] :
    l2NormSq (translatingCosetState u H) = 1 ∧
      (∀ x : G, translatingCosetState u H x ≠ 0 ↔ u⁻¹ * x ∈ H) ∧
      (∀ h x : G, h ∈ H →
        translatingCosetState u H (x * h) = translatingCosetState u H x) := by
  classical
  refine ⟨translatingCosetState_l2NormSq u H, ?_, ?_⟩
  · intro x
    exact translatingCosetState_ne_zero_iff u H
  · intro h x hh
    exact translatingCosetState_mul_right u H hh

end Qatlib.Papers.HiddenTransl02.MainResults
