/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Reduction

/-!
# Amplitude estimates and Jones promise bands

This module relates real amplitudes to scaled norms of Jones values through `ScaleRelation`. It
transfers upper and lower amplitude bands to Jones-value bands and bounds matrix-element errors
from a uniform relative operator estimate. See [AharonovArad2011].

## Main statements

* `jones_band_le`: transfers an upper amplitude bound.
* `jones_band_ge`: transfers a lower amplitude bound.
* `inner_apply_bound_unit`: bounds the matrix-element error on a unit vector.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

open scoped ComplexInnerProductSpace

variable {n : ℕ}

/-- Every Jones-value norm equals `Δ` times the specified real amplitude. -/
def ScaleRelation (V : JonesValue n) (Δ : ℝ) (amp : BraidWord n → ℝ) : Prop :=
  ∀ b : BraidWord n, ‖V b‖ = Δ * amp b

/-- Under a positive scale relation, every specified amplitude is nonnegative. -/
theorem ScaleRelation.amp_nonneg {V : JonesValue n} {Δ : ℝ} {amp : BraidWord n → ℝ}
    (hΔ : 0 < Δ) (h : ScaleRelation V Δ amp) (b : BraidWord n) : 0 ≤ amp b := by
  have hb := h b
  have := norm_nonneg (V b)
  nlinarith

/-- Under a positive scale relation, an amplitude upper bound `lo` gives the Jones-value bound
`Δ * lo`. -/
theorem jones_band_le {V : JonesValue n} {Δ : ℝ} {amp : BraidWord n → ℝ}
    (hΔ : 0 < Δ) (h : ScaleRelation V Δ amp) {b : BraidWord n} {lo : ℝ}
    (hb : amp b ≤ lo) : ‖V b‖ ≤ Δ * lo := by
  rw [h b]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt hΔ)

/-- Under a positive scale relation, an amplitude lower bound `hi` gives the Jones-value lower
bound `Δ * hi`. -/
theorem jones_band_ge {V : JonesValue n} {Δ : ℝ} {amp : BraidWord n → ℝ}
    (hΔ : 0 < Δ) (h : ScaleRelation V Δ amp) {b : BraidWord n} {hi : ℝ}
    (hb : hi ≤ amp b) : Δ * hi ≤ ‖V b‖ := by
  rw [h b]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt hΔ)

/-- If `a` lies within `ε` of `c`, with `c ≤ lo` and `lo + ε ≤ L`, then `a ≤ L`. -/
theorem amp_le_of_close {a c ε lo L : ℝ} (h : |a - c| ≤ ε) (hc : c ≤ lo)
    (hslack : lo + ε ≤ L) : a ≤ L := by
  have h' := (abs_le.mp h).2
  linarith

/-- If `a` lies within `ε` of `c`, with `hi ≤ c` and `L ≤ hi - ε`, then `L ≤ a`. -/
theorem amp_ge_of_close {a c ε hi L : ℝ} (h : |a - c| ≤ ε) (hc : hi ≤ c)
    (hslack : L ≤ hi - ε) : L ≤ a := by
  have h' := (abs_le.mp h).1
  linarith

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A uniform bound `‖(A - B) x‖ ≤ ε * ‖x‖` bounds the matrix element at `α` by `ε * ‖α‖ ^ 2`.
See [Aharonov and Arad, Theorem 3.1][AharonovArad2011]. -/
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

/-- On a unit vector, a uniform relative error bound `ε` for `A - B` gives matrix-element error
at most `ε`. -/
theorem inner_apply_bound_unit (A B : E →L[ℂ] E) (ε : ℝ)
    (h : ∀ x : E, ‖(A - B) x‖ ≤ ε * ‖x‖) (α : E) (hα : ‖α‖ = 1) :
    ‖⟪α, (A - B) α⟫‖ ≤ ε := by
  have := inner_apply_bound A B ε h α
  rw [hα] at this
  simpa using this

end InnerProduct

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
