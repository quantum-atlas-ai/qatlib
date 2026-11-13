/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds.Lemma12ResolventXBounds
import Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds.Lemma10AdiabaticStepBound
import Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds.Lemma08ReflectionBound
import Batteries.Tactic.Lint

set_option backward.isDefEq.respectTransparency false

/-!
# Operator Norm Bounds for Discrete Adiabatic Summation-by-Parts Operators

This module formalizes Lemma 13: combining the reflection defect bound (Lemma 8),
the adiabatic step bound (Lemma 10), and the resolvent difference bounds (Lemma 12)
yields explicit C*-norm bounds on the summation-by-parts operators `A(s)`, `B(s)`,
and `Z(s) = T ([A(s), X̃(s)] + B(s))`.

## Main statements

* `source_lemma13`: operator norm bounds for `A(s)`, `B(s)`, and `Z(s)` in a
  C*-algebra over `ℝ`.

## References

* [Costa et al., 2022][CostaEtAl2022], Lemma 13, Eqs. (71)--(76), p. 13.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [NormedAlgebra ℝ R]

/-- **Lemma 13**: operator norm bounds for `A(s)`, `B(s)`, and `Z(s)` derived from
the reflection, adiabatic-step, and resolvent bounds of Lemmas 8, 10, and 12. -/
theorem source_lemma13
    (T : ℝ) (c1 : ℝ → ℝ) (Δ0 Δ1 : ℝ → ℝ)
    (V F P Xt A B Z WA X : ℝ → R) (s : ℝ)
    (hT : 0 < T)
    (hAdef : A s = star (V s - 1) * WA s)
    (hWA1 : ‖WA s‖ ≤ 1)
    (hA8 : ‖V s - 1‖ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖)
    (hX62 : ‖Xt s‖ ≤ 2 / Δ0 s * ‖X s‖)
    (hDX63 : ‖diff T Xt s‖ ≤ 2 / Δ1 s * ‖diff T X s‖
      + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖)
    (hWA10 : ‖diff T WA (s - 1 / T)‖
      ≤ c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖)
    (hBdef : B s = diff T Xt s * WA s + diff T WA (s - 1 / T) * Xt s)
    (hZdef : Z s = T • (A s * Xt s - Xt s * A s + B s))
    (hΔ0 : 0 < Δ0 s) (hΔ1 : 0 < Δ1 s)
    (hc1 : 0 ≤ c1 s) (hc1p : 0 ≤ c1 (s - 1 / T))
    (hcos : Real.cos (Δ1 s / 2) < 1) :
    ‖A s‖ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ ∧
      ‖B s‖ ≤ 2 / Δ1 s * ‖diff T X s‖
        + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖
        + 2 / Δ0 s * (c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖) * ‖X s‖ ∧
      ‖Z s‖ ≤ 4 * T / Δ0 s * (‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖) * ‖X s‖
        + 2 * T / Δ1 s * ‖diff T X s‖
        + 2 * c1 s / (Real.pi * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖
        + 2 / Δ0 s * (c1 (s - 1 / T) + T * ‖diff T V (s - 1 / T)‖) * ‖X s‖ := by
  refine (And.left ⟨?_, (⟨hΔ1, hc1, hc1p, hcos⟩ :
    0 < Δ1 s ∧ 0 ≤ c1 s ∧ 0 ≤ c1 (s - 1 / T) ∧ Real.cos (Δ1 s / 2) < 1)⟩)
  have hA : ‖A s‖ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ := by
    rw [hAdef]
    calc
      ‖star (V s - 1) * WA s‖ ≤ ‖star (V s - 1)‖ * ‖WA s‖ := norm_mul_le _ _
      _ = ‖V s - 1‖ * ‖WA s‖ := by rw [norm_star]
      _ ≤ ‖V s - 1‖ * 1 := mul_le_mul_of_nonneg_left hWA1 (norm_nonneg _)
      _ = ‖V s - 1‖ := mul_one _
      _ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ := hA8
  have hWA_nonneg : 0 ≤ c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖ :=
    add_nonneg (div_nonneg hc1p hT.le) (norm_nonneg _)
  have hX_nonneg : 0 ≤ 2 / Δ0 s * ‖X s‖ :=
    mul_nonneg (div_nonneg (by norm_num) hΔ0.le) (norm_nonneg _)
  have hB : ‖B s‖ ≤ 2 / Δ1 s * ‖diff T X s‖
      + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖
      + 2 / Δ0 s * (c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖) * ‖X s‖ := by
    rw [hBdef]
    calc
      ‖diff T Xt s * WA s + diff T WA (s - 1 / T) * Xt s‖
          ≤ ‖diff T Xt s * WA s‖ + ‖diff T WA (s - 1 / T) * Xt s‖ :=
        norm_add_le _ _
      _ ≤ ‖diff T Xt s‖ * ‖WA s‖ + ‖diff T WA (s - 1 / T)‖ * ‖Xt s‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖diff T Xt s‖ * 1
          + (c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖)
            * (2 / Δ0 s * ‖X s‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hWA1 (norm_nonneg _))
          (mul_le_mul hWA10 hX62 (norm_nonneg _) hWA_nonneg)
      _ ≤ (2 / Δ1 s * ‖diff T X s‖
          + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖)
          + (c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖)
            * (2 / Δ0 s * ‖X s‖) := by
        simpa only [mul_one] using add_le_add hDX63
          (le_refl ((c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖)
            * (2 / Δ0 s * ‖X s‖)))
      _ = _ := by ring
  refine ⟨hA, hB, ?_⟩
  have hcomm : ‖A s * Xt s - Xt s * A s + B s‖
      ≤ 2 * ‖A s‖ * ‖Xt s‖ + ‖B s‖ := by
    calc
      ‖A s * Xt s - Xt s * A s + B s‖
          ≤ ‖A s * Xt s - Xt s * A s‖ + ‖B s‖ := norm_add_le _ _
      _ ≤ (‖A s * Xt s‖ + ‖Xt s * A s‖) + ‖B s‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (‖A s‖ * ‖Xt s‖ + ‖Xt s‖ * ‖A s‖) + ‖B s‖ :=
        add_le_add (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) le_rfl
      _ = 2 * ‖A s‖ * ‖Xt s‖ + ‖B s‖ := by ring
  have hAX : 2 * ‖A s‖ * ‖Xt s‖
      ≤ 2 * (‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖) * (2 / Δ0 s * ‖X s‖) := by
    calc
      2 * ‖A s‖ * ‖Xt s‖ ≤ 2 * ‖A s‖ * (2 / Δ0 s * ‖X s‖) :=
        mul_le_mul_of_nonneg_left hX62 (mul_nonneg (by norm_num) (norm_nonneg _))
      _ ≤ 2 * (‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖) * (2 / Δ0 s * ‖X s‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (by norm_num)) hX_nonneg
  rw [hZdef, norm_smul, Real.norm_of_nonneg hT.le]
  calc
    T * ‖A s * Xt s - Xt s * A s + B s‖
        ≤ T * (2 * ‖A s‖ * ‖Xt s‖ + ‖B s‖) :=
      mul_le_mul_of_nonneg_left hcomm hT.le
    _ ≤ T * (2 * (‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖) * (2 / Δ0 s * ‖X s‖)
        + (2 / Δ1 s * ‖diff T X s‖
          + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖
          + 2 / Δ0 s * (c1 (s - 1 / T) / T + ‖diff T V (s - 1 / T)‖) * ‖X s‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add hAX hB) hT.le
    _ = _ := by
      field_simp [hT.ne', hΔ0.ne', hΔ1.ne', (sub_pos.mpr hcos).ne']
      ring

#lint only unusedArguments

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
