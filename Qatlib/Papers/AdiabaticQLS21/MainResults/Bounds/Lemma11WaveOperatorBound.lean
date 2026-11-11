/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds.Lemma08ReflectionBound

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11: difference of the wave operator

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 11 / Eqs. (59)--(61), page 12.

The proof of the paper uses Proposition 5, Eq. (36) and the definition of the
wave operator to write

`D Ω_T(s) = U^A_T(s + 1/T)† (V_T(s) - I)† U^A_T(s + 1/T) Ω_T(s)`,   (Eq. (60))

then observes that `U^A_T` and `Ω_T` are unitary, hence
`‖D Ω_T(s)‖ = ‖(V_T(s) - I)†‖ = ‖V_T(s) - I‖`, and applies Lemma 8.

The conjugation identity of Eq. (60) is the paper's Proposition 5 statement and
is carried as the hypothesis `hstep`.  The norm computation is fully proved:
conjugation by a unitary preserves the C*-norm (`norm_conj_eq`), `star`
preserves the norm, and multiplying by the unitary `Ω_T(s)` costs nothing.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R] [NormOneClass R] [StarRing R] [CStarRing R]

/-- Fixed arXiv:2111.08152, Lemma 11 (Eq. (59), p. 12): under the paper's
Eq. (60) (`DΩ_T(s) = U^A_T(s+1/T)† (V_T(s)-I)† U^A_T(s+1/T) Ω_T(s)`) and
unitarity of `U^A_T(s+1/T)` and `Ω_T(s)`,
`‖D Ω_T(s)‖ ≤ ‖F_T(s) - I‖ + ‖DP_T(s)‖ ‖F_T(s)‖`. -/
theorem source_lemma11
    (T : ℝ) (P F V Ω UA : ℝ → R) (s : ℝ)
    (hstep : diff T Ω s
      = star (UA (s + 1 / T)) * star (V s - 1) * UA (s + 1 / T) * Ω s)
    (hUA : IsUnitary (UA (s + 1 / T)))
    (hΩ : IsUnitary (Ω s))
    (hlem8 : ‖V s - 1‖ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖) :
    ‖diff T Ω s‖ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ := by
  have hconj : ‖star (UA (s + 1 / T)) * star (V s - 1) * UA (s + 1 / T)‖
      = ‖V s - 1‖ := by
    have hu : IsUnitary (star (UA (s + 1 / T))) := hUA.star
    have hEq : star (UA (s + 1 / T)) * star (V s - 1) * UA (s + 1 / T)
        = star (UA (s + 1 / T)) * star (V s - 1) * star (star (UA (s + 1 / T))) := by
      rw [star_star]
    rw [hEq, norm_conj_eq hu, norm_star]
  rw [hstep]
  calc ‖star (UA (s + 1 / T)) * star (V s - 1) * UA (s + 1 / T) * Ω s‖
      ≤ ‖star (UA (s + 1 / T)) * star (V s - 1) * UA (s + 1 / T)‖ * ‖Ω s‖ :=
        norm_mul_le _ _
    _ = ‖V s - 1‖ * ‖Ω s‖ := by rw [hconj]
    _ = ‖V s - 1‖ := by rw [hΩ.norm_eq_one, mul_one]
    _ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ := hlem8

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
