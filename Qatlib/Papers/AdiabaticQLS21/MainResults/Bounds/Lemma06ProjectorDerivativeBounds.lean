/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6: bounds on `D P_T(s)` and `D^(2) P_T(s)`

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 6 / Eqs. (42)--(44), pages 9--10,
proof in Appendix B, pages 31--34.

The paper's proof writes the Riesz-projector differences as contour integrals of
the resolvent `R_T(s,z) = (W_T(s) - zI)^{-1}` (Eqs. (B2) and (B9)) and evaluates
them along the straight-line contours `Γ_T(s,1)` and `Γ_T(s,2)` that pass through
the gaps `Δ₁(s)` and `Δ₂(s)`:

* for `D P_T(s)`, Eqs. (B3)--(B6) give
  `‖D P_T(s)‖ ≤ c₁(s)/(T·2π) · ∫ ≤ c₁(s)/(T·2π) · (4π/Δ₁(s)) = 2c₁(s)/(T Δ₁(s))`;
* for `D^(2) P_T(s)`, Eq. (B9) splits the difference into three contour
  integrals, and Eqs. (B10)--(B12) bound them by
  `c₁(s)²/(π(1-cos(Δ₂(s)/2)))`, `2c₂(s)/Δ₂(s)` and
  `c₁(s)c₁(s+1/T)/(π(1-cos(Δ₂(s)/2)))` respectively, all over `T²`.

Contour integration and resolvent spectra are not available in this
paper-layer model, so the two *evaluated* contour estimates (B3)+(B6) and
(B9)+(B10)--(B12) are carried as hypotheses `hDP` and `hD2P`.  The arithmetic
combining them into Eqs. (42)--(43) is proved below.  The side conditions
`0 < Δ₁(s)`, `0 < Δ₂(s)`, `cos(Δ₂(s)/2) < 1` and `0 < T` are part of the
paper's gap/contour setup (the contour is only defined when the gaps separate
the spectrum); they are made explicit because the divisions require them.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R]

/-- Fixed arXiv:2111.08152, Lemma 6 (Eqs. (42)--(44), pp. 9--10): for the
Riesz projectors `P_T(s)` of the walk, with Definition-1 coefficients `c₁, c₂`
and Definition-2 gaps `Δ₁, Δ₂`,

`‖D P_T(s)‖ ≤ 2c₁(s)/(T Δ₁(s))`  and
`‖D^(2) P_T(s)‖ ≤ G_{T,1}(s)/T²` with `G_{T,1}` as in Eq. (44).

The contour-integral evaluations of Appendix B are the hypotheses `hDP` and
`hD2P`. -/
theorem source_lemma6
    (T : ℝ) (P : ℝ → R) (c1 c2 Δ1 Δ2 : ℝ → ℝ) (s : ℝ)
    (hT : 0 < T) (hΔ1 : 0 < Δ1 s) (hΔ2 : 0 < Δ2 s)
    (hcos : Real.cos (Δ2 s / 2) < 1)
    (hDP : ‖diff T P s‖ ≤ c1 s / (T * (2 * Real.pi)) * (4 * Real.pi / Δ1 s))
    (hD2P : ‖diff2 T P s‖ ≤
      c1 s ^ 2 / (Real.pi * (1 - Real.cos (Δ2 s / 2))) / T ^ 2
        + 2 * c2 s / (T ^ 2 * Δ2 s)
        + c1 s * c1 (s + 1 / T) / (Real.pi * (1 - Real.cos (Δ2 s / 2))) / T ^ 2) :
    ‖diff T P s‖ ≤ 2 * c1 s / (T * Δ1 s) ∧
      ‖diff2 T P s‖ ≤ GT1 T c1 c2 Δ2 s / T ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcosne : 1 - Real.cos (Δ2 s / 2) ≠ 0 := by
    have : 0 < 1 - Real.cos (Δ2 s / 2) := by linarith
    exact ne_of_gt this
  constructor
  · have hEq : c1 s / (T * (2 * Real.pi)) * (4 * Real.pi / Δ1 s)
        = 2 * c1 s / (T * Δ1 s) := by
      field_simp
      ring
    exact hDP.trans hEq.le
  · have hEq : c1 s ^ 2 / (Real.pi * (1 - Real.cos (Δ2 s / 2))) / T ^ 2
          + 2 * c2 s / (T ^ 2 * Δ2 s)
          + c1 s * c1 (s + 1 / T) / (Real.pi * (1 - Real.cos (Δ2 s / 2))) / T ^ 2
        = GT1 T c1 c2 Δ2 s / T ^ 2 := by
      unfold GT1
      field_simp
      ring
    exact hD2P.trans hEq.le

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
