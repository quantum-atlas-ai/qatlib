/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Reduction
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

open scoped ComplexInnerProductSpace

variable {n : ℕ}

def ScaleRelation (V : JonesValue n) (Δ : ℝ) (amp : BraidWord n → ℝ) : Prop :=
  ∀ b : BraidWord n, ‖V b‖ = Δ * amp b

theorem ScaleRelation.amp_nonneg {V : JonesValue n} {Δ : ℝ} {amp : BraidWord n → ℝ}
    (hΔ : 0 < Δ) (h : ScaleRelation V Δ amp) (b : BraidWord n) : 0 ≤ amp b := by
  have hb := h b
  have := norm_nonneg (V b)
  nlinarith

theorem jones_band_le {V : JonesValue n} {Δ : ℝ} {amp : BraidWord n → ℝ}
    (hΔ : 0 < Δ) (h : ScaleRelation V Δ amp) {b : BraidWord n} {lo : ℝ}
    (hb : amp b ≤ lo) : ‖V b‖ ≤ Δ * lo := by
  rw [h b]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt hΔ)

theorem jones_band_ge {V : JonesValue n} {Δ : ℝ} {amp : BraidWord n → ℝ}
    (hΔ : 0 < Δ) (h : ScaleRelation V Δ amp) {b : BraidWord n} {hi : ℝ}
    (hb : hi ≤ amp b) : Δ * hi ≤ ‖V b‖ := by
  rw [h b]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt hΔ)

theorem amp_le_of_close {a c ε lo L : ℝ} (h : |a - c| ≤ ε) (hc : c ≤ lo)
    (hslack : lo + ε ≤ L) : a ≤ L := by
  have h' := (abs_le.mp h).2
  linarith

theorem amp_ge_of_close {a c ε hi L : ℝ} (h : |a - c| ≤ ε) (hc : hi ≤ c)
    (hslack : L ≤ hi - ε) : L ≤ a := by
  have h' := (abs_le.mp h).1
  linarith

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_apply_bound (A B : E →L[ℂ] E) (ε : ℝ)
    (h : ∀ x : E, ‖(A - B) x‖ ≤ ε * ‖x‖) (α : E) :
    ‖⟪α, (A - B) α⟫‖ ≤ ε * ‖α‖ ^ 2 := by
  have h1 : ‖⟪α, (A - B) α⟫‖ ≤ ‖α‖ * ‖(A - B) α‖ :=
    norm_inner_le_norm _ _
  have h2 : ‖(A - B) α‖ ≤ ε * ‖α‖ := h α
  have hα : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
  calc ‖⟪α, (A - B) α⟫‖ ≤ ‖α‖ * ‖(A - B) α‖ := h1
    _ ≤ ‖α‖ * (ε * ‖α‖) := mul_le_mul_of_nonneg_left h2 hα
    _ = ε * ‖α‖ ^ 2 := by ring

theorem inner_apply_bound_unit (A B : E →L[ℂ] E) (ε : ℝ)
    (h : ∀ x : E, ‖(A - B) x‖ ≤ ε * ‖x‖) (α : E) (hα : ‖α‖ = 1) :
    ‖⟪α, (A - B) α⟫‖ ≤ ε := by
  have := inner_apply_bound A B ε h α
  rw [hα] at this
  simpa using this

end InnerProduct

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
