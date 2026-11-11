/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Composition norms and approximation rescaling

Defines `compList` for ordered composition of continuous complex-linear endomorphisms and bounds
its norm by the product of the individual norms. This estimate supplies the norm-product control
used in the swallowing construction of [AradLandau2010].

The scalar results transfer upper and lower error bounds from a normalized value to the original
scale and bound normalized amplitudes by one.

## Main statements

* `norm_compList_le`: bounds the norm of an ordered composition.
* `rescale_error`: transfers an upper error bound to a positive scale.
* `normalized_amplitude_bound`: bounds a normalized complex value by one.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option autoImplicit false

noncomputable section

open Finset BigOperators

namespace Qatlib.Papers.TensorNetwork08.MainResults.SwallowNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The ordered composition of a list of continuous complex-linear endomorphisms, with the
identity for the empty list. -/
def compList (l : List (E →L[ℂ] E)) : E →L[ℂ] E :=
  l.foldr (fun f g => f.comp g) (ContinuousLinearMap.id ℂ E)

/-- On a nontrivial normed space, the norm of `compList l` is at most the product of the norms
of the maps in `l`. See [AradLandau2010]. -/
theorem norm_compList_le [Nontrivial E] (l : List (E →L[ℂ] E)) :
    ‖compList l‖ ≤ (l.map (fun f => ‖f‖)).prod := by
  induction l with
  | nil =>
      simp [compList, ContinuousLinearMap.norm_id]
  | cons f t ih =>
      have hstep : ‖f.comp (compList t)‖ ≤ ‖f‖ * ‖compList t‖ :=
        ContinuousLinearMap.opNorm_comp_le f (compList t)
      have hprod : ‖f‖ * ‖compList t‖
          ≤ ‖f‖ * (t.map (fun g => ‖g‖)).prod := by
        exact mul_le_mul_of_nonneg_left ih (norm_nonneg f)
      calc ‖compList (f :: t)‖
          = ‖f.comp (compList t)‖ := rfl
        _ ≤ ‖f‖ * ‖compList t‖ := hstep
        _ ≤ ‖f‖ * (t.map (fun g => ‖g‖)).prod := hprod
        _ = (List.map (fun g => ‖g‖) (f :: t)).prod := by simp

/-- For positive `Δ`, an error bound `‖r - T / Δ‖ ≤ ε` implies `‖Δ * r - T‖ ≤ ε * Δ`. See
[AradLandau2010]. -/
theorem rescale_error (T r : ℂ) (ε Δ : ℝ) (hΔ : 0 < Δ)
    (h : ‖r - T / (Δ : ℂ)‖ ≤ ε) :
    ‖(Δ : ℂ) * r - T‖ ≤ ε * Δ := by
  have hΔc : (Δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hΔ
  have hfactor : (Δ : ℂ) * r - T = (Δ : ℂ) * (r - T / (Δ : ℂ)) := by
    field_simp
  have hnorm : ‖(Δ : ℂ)‖ = Δ := by simp [abs_of_pos hΔ]
  rw [hfactor, norm_mul, hnorm]
  calc Δ * ‖r - T / (Δ : ℂ)‖ ≤ Δ * ε := mul_le_mul_of_nonneg_left h (le_of_lt hΔ)
    _ = ε * Δ := by ring

/-- For positive `Δ`, a lower error bound `ε ≤ ‖r' - T / Δ‖` implies `ε * Δ ≤ ‖Δ * r' - T‖`. -/
theorem rescale_probability (T r' : ℂ) (ε Δ : ℝ) (hΔ : 0 < Δ)
    (h : ε ≤ ‖r' - T / (Δ : ℂ)‖) :
    ε * Δ ≤ ‖(Δ : ℂ) * r' - T‖ := by
  have hΔc : (Δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hΔ
  have hfactor : (Δ : ℂ) * r' - T = (Δ : ℂ) * (r' - T / (Δ : ℂ)) := by
    field_simp
  have hnorm : ‖(Δ : ℂ)‖ = Δ := by simp [abs_of_pos hΔ]
  rw [hfactor, norm_mul, hnorm]
  calc ε * Δ ≤ ‖r' - T / (Δ : ℂ)‖ * Δ := mul_le_mul_of_nonneg_right h (le_of_lt hΔ)
    _ = Δ * ‖r' - T / (Δ : ℂ)‖ := by ring

/-- If `Δ` is nonzero and `‖T‖ ≤ ‖Δ‖`, then the normalized value `T / Δ` has norm at most one.
See [AradLandau2010]. -/
theorem normalized_amplitude_bound (T Δ : ℂ) (hΔ : Δ ≠ 0)
    (h : ‖T‖ ≤ ‖Δ‖) :
    ‖T / Δ‖ ≤ 1 := by
  rw [norm_div]
  rw [div_le_one (norm_pos_iff.mpr hΔ)]
  exact h

end Qatlib.Papers.TensorNetwork08.MainResults.SwallowNorm
