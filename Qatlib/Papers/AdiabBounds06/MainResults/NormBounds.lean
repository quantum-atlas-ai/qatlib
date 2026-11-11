/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.Twiddle

/-!
# Operator norm estimates for the twiddle transform

`isProj_norm_le_one` bounds the operator norm of a Hermitian projection. Applying this estimate
term by term to the reduced-resolvent expression for the twiddle transform gives
`twiddle_norm_bound`, with explicit bound `2 * m * ‖X‖ / g` for the supplied band data. The
development follows [JansenRuskaiSeiler2007].

## Main statements

* `isProj_norm_le_one`: bounds the norm of an orthogonal projection by one.
* `twiddle_norm_bound`: bounds the twiddle transform by `2 * m * ‖X‖ / g`.

## References

* [Jansen et al., 2007][JansenRuskaiSeiler2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

/-- The operator norm of a Hermitian idempotent matrix is at most one. -/
theorem isProj_norm_le_one {P : Matrix (Fin n) (Fin n) ℂ} (h : IsProj P) : ‖P‖ ≤ 1 := by
  obtain ⟨hPP, hPstar⟩ := h
  have hsq : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self]
    rw [show star P = P from hPstar, hPP]
  nlinarith [sq_nonneg (‖P‖ - 1)]

/-- For the band data `D`, the twiddle transform satisfies `‖D.twiddle X‖ ≤ 2 * D.m * ‖X‖ /
D.g`. This termwise reduced-resolvent estimate is related to the sharper bound in [Jansen et
al., 2007, Lemma 7][JansenRuskaiSeiler2007]. -/
theorem twiddle_norm_bound {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖D.twiddle X‖ ≤ 2 * (D.m : ℝ) * ‖X‖ / D.g := by
  have hPj : ∀ j : Fin D.m, ‖D.Pj j‖ ≤ 1 := fun j => isProj_norm_le_one (D.Pj_proj j)
  have hX : 0 ≤ ‖X‖ := norm_nonneg X
  have hg : 0 ≤ 1 / D.g := le_of_lt (one_div_pos.mpr D.hg)
  have hXg : 0 ≤ ‖X‖ / D.g := div_nonneg hX D.hg.le
  have hterm : ∀ j : Fin D.m,
      ‖D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j‖ ≤ 2 * ‖X‖ / D.g := by
    intro j
    have h1 : ‖D.Pj j * X * D.Rhat j‖ ≤ ‖X‖ / D.g := by
      calc ‖D.Pj j * X * D.Rhat j‖
          ≤ ‖D.Pj j * X‖ * ‖D.Rhat j‖ := norm_mul_le _ _
        _ ≤ (‖D.Pj j‖ * ‖X‖) * ‖D.Rhat j‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 * ‖X‖) * (1 / D.g) := by
            apply mul_le_mul
            · exact mul_le_mul (hPj j) le_rfl hX zero_le_one
            · exact D.Rhat_bound j
            · exact norm_nonneg _
            · exact mul_nonneg zero_le_one hX
        _ = ‖X‖ / D.g := by ring
    have h2 : ‖D.Rhat j * X * D.Pj j‖ ≤ ‖X‖ / D.g := by
      calc ‖D.Rhat j * X * D.Pj j‖
          ≤ ‖D.Rhat j * X‖ * ‖D.Pj j‖ := norm_mul_le _ _
        _ ≤ (‖D.Rhat j‖ * ‖X‖) * ‖D.Pj j‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 / D.g * ‖X‖) * 1 := by
            apply mul_le_mul
            · exact mul_le_mul (D.Rhat_bound j) le_rfl hX hg
            · exact hPj j
            · exact norm_nonneg _
            · exact mul_nonneg hg hX
        _ = ‖X‖ / D.g := by ring
    calc ‖D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j‖
        ≤ ‖D.Pj j * X * D.Rhat j‖ + ‖D.Rhat j * X * D.Pj j‖ := norm_add_le _ _
      _ ≤ ‖X‖ / D.g + ‖X‖ / D.g := add_le_add h1 h2
      _ = 2 * ‖X‖ / D.g := by ring
  calc ‖D.twiddle X‖
      = ‖∑ j, (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j)‖ := by
        rw [D.twiddle_eq_sum_resolvents X]
        simp
    _ ≤ ∑ j, ‖D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, 2 * ‖X‖ / D.g := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (D.m : ℝ) * (2 * ‖X‖ / D.g) := by simp
    _ = 2 * (D.m : ℝ) * ‖X‖ / D.g := by ring

end Qatlib.Papers.AdiabBounds06.MainResults
