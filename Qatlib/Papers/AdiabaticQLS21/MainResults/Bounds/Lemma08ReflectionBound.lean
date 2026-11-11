/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds.Lemma07PolarDecomposition

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 8: norm bound for `V_T(s) - I`

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 8 / Eqs. (48)--(50), page 10.

From Lemma 7,
`V_T(s) - I = (F_T(s) - I) + F_T(s) DP_T(s) (2P_T(s) - I)`;
the triangle inequality and submultiplicativity give
`‖V_T(s) - I‖ ≤ ‖F_T(s) - I‖ + ‖F_T(s)‖ ‖DP_T(s)‖ ‖2P_T(s) - I‖`,
and `2P_T(s) - I` is a reflection, so its norm is at most one (Eq. (50)).
The proof below performs exactly this chain.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R]

/-- Fixed arXiv:2111.08152, Lemma 8 (Eq. (48), p. 10): if `V_T(s)` has the
polar-decomposition form of Lemma 7 and `2P_T(s) - I` is a reflection
(`‖2P_T(s) - I‖ ≤ 1`), then
`‖V_T(s) - I‖ ≤ ‖F_T(s) - I‖ + ‖DP_T(s)‖ ‖F_T(s)‖`. -/
theorem source_lemma8
    (T : ℝ) (P F V : ℝ → R) (s : ℝ)
    (hV : ∀ t, V t = F t * (1 + diff T P t * refl (P t)))
    (hreflect : ‖refl (P s)‖ ≤ 1) :
    ‖V s - 1‖ ≤ ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ := by
  have hdecomp : V s - 1 = (F s - 1) + F s * (diff T P s * refl (P s)) := by
    rw [hV s]
    noncomm_ring
  rw [hdecomp]
  calc ‖(F s - 1) + F s * (diff T P s * refl (P s))‖
      ≤ ‖F s - 1‖ + ‖F s * (diff T P s * refl (P s))‖ := norm_add_le _ _
    _ ≤ ‖F s - 1‖ + ‖F s‖ * ‖diff T P s * refl (P s)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖F s - 1‖ + ‖F s‖ * (‖diff T P s‖ * ‖refl (P s)‖) := by
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖F s - 1‖ + ‖F s‖ * (‖diff T P s‖ * 1) := by
        gcongr
    _ = ‖F s - 1‖ + ‖diff T P s‖ * ‖F s‖ := by ring

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
