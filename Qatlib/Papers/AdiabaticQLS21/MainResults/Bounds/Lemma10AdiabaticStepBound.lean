/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 10: difference of the adiabatic walk operator

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 10 / Eqs. (57)--(58), page 11.

With `W^A_T(s) = V_T(s) W_T(s)` (Eq. (24)), the discrete product rule gives

`D W^A_T(s) = D V_T(s) · W_T(s + 1/T) + V_T(s) · D W_T(s)`.

Since `W_T` and `V_T` are unitary they have norm one, and Definition 1 bounds
`‖D W_T(s)‖ ≤ c_1(s)/T`; the triangle inequality and submultiplicativity then
give `‖D W^A_T(s)‖ ≤ c_1(s)/T + ‖D V_T(s)‖`.

Unitarity is represented by the norm hypotheses `‖W t‖ ≤ 1`, `‖V t‖ ≤ 1`,
which is the only property used in the paper (the `†` factors are absent from
the estimate).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R]

/-- Fixed arXiv:2111.08152, Lemma 10 (Eq. (57), p. 11): for the adiabatic walk
`W^A_T(s) = V_T(s) W_T(s)` built from unitaries `V_T`, `W_T` and satisfying
Definition 1 with coefficient `c_1`,
`‖D W^A_T(s)‖ ≤ c_1(s)/T + ‖D V_T(s)‖`. -/
theorem source_lemma10
    (T : ℝ) (c1 : ℝ → ℝ) (V W WA : ℝ → R) (s : ℝ)
    (hWA : ∀ t, WA t = V t * W t)
    (hWnorm : ∀ t, ‖W t‖ ≤ 1)
    (hVnorm : ∀ t, ‖V t‖ ≤ 1)
    (hWd : ‖diff T W s‖ ≤ c1 s / T) :
    ‖diff T WA s‖ ≤ c1 s / T + ‖diff T V s‖ := by
  have hdecomp : diff T WA s = diff T V s * W (s + 1 / T) + V s * diff T W s := by
    simp only [diff, hWA]
    noncomm_ring
  rw [hdecomp]
  calc ‖diff T V s * W (s + 1 / T) + V s * diff T W s‖
      ≤ ‖diff T V s * W (s + 1 / T)‖ + ‖V s * diff T W s‖ := norm_add_le _ _
    _ ≤ ‖diff T V s‖ * ‖W (s + 1 / T)‖ + ‖V s‖ * ‖diff T W s‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖diff T V s‖ * 1 + 1 * (c1 s / T) := by
        have h1 : ‖diff T V s‖ * ‖W (s + 1 / T)‖ ≤ ‖diff T V s‖ * 1 :=
          mul_le_mul_of_nonneg_left (hWnorm (s + 1 / T)) (norm_nonneg _)
        have h2 : ‖V s‖ * ‖diff T W s‖ ≤ 1 * (c1 s / T) :=
          mul_le_mul (hVnorm s) hWd (norm_nonneg _) zero_le_one
        linarith
    _ = c1 s / T + ‖diff T V s‖ := by ring

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
