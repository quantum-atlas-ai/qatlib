/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12: bounds for `X̃(s)` and `D X̃(s)`

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 12 / Eqs. (62)--(70), pages 12--13.

`X̃(s)` is the resolvent sandwich of Eq. (38),
`X̃(s) = -(1/2πi) ∮_{Γ_T(s)} R_T(s,z) X(s) R_T(s,z) dz`.
The paper bounds it by the contour integral (64) and the geometric evaluation
(B6) (with `Δ₁` replaced by `Δ₀`, since only one step of the walk is enclosed),
and bounds `D X̃(s)` by Eq. (69) using (B6) and (B8), obtaining Eq. (70).

Contour integrals and resolvents are not modelled here.  The evaluated
contour-integral quantities are carried as the reals `I1` (the `∫‖R‖²|dz|`
of (B6)) and `J` (the `∫‖R‖³|dz|` of (B8)), with the paper's bounds
`I1 ≤ 4π/Δ₁(s)` and `J ≤ 2/(1-cos(Δ₁(s)/2))` as hypotheses.  The arithmetic
turning (64) and (69) into Eqs. (62) and (63) is proved below.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R]

/-- Fixed arXiv:2111.08152, Lemma 12 (Eqs. (62)--(63), p. 12): with the
Appendix-B contour evaluations `I1 ≤ 4π/Δ₁(s)` and
`J ≤ 2/(1-cos(Δ₁(s)/2))`,

`‖X̃(s)‖ ≤ (2/Δ₀(s)) ‖X(s)‖` and
`‖D X̃(s)‖ ≤ (2/Δ₁(s)) ‖DX(s)‖
             + (2c₁(s)/(πT(1-cos(Δ₁(s)/2)))) ‖X(s)‖`. -/
theorem source_lemma12
    (T : ℝ) (c1 Δ0 Δ1 : ℝ → ℝ) (Xt X : ℝ → R) (s : ℝ)
    (hT : 0 < T) (hΔ0 : 0 < Δ0 s) (hΔ1 : 0 < Δ1 s)
    (hc1 : 0 ≤ c1 s) (hcos : Real.cos (Δ1 s / 2) < 1)
    (I0 I1 J : ℝ)
    (hI0 : I0 ≤ 4 * Real.pi / Δ0 s)
    (hI1 : I1 ≤ 4 * Real.pi / Δ1 s)
    (hJ : J ≤ 2 / (1 - Real.cos (Δ1 s / 2)))
    (hXtil : ‖Xt s‖ ≤ (1 / (2 * Real.pi)) * I0 * ‖X s‖)
    (hDXtil : ‖diff T Xt s‖ ≤
      ‖diff T X s‖ / (2 * Real.pi) * I1
        + ‖X s‖ / (2 * Real.pi) * (c1 s / T * J + c1 s / T * J)) :
    ‖Xt s‖ ≤ 2 / Δ0 s * ‖X s‖ ∧
      ‖diff T Xt s‖ ≤ 2 / Δ1 s * ‖diff T X s‖
        + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖ := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hcospos : 0 < 1 - Real.cos (Δ1 s / 2) := by linarith
  have hcoe : (0:ℝ) ≤ c1 s / T := div_nonneg hc1 hT.le
  constructor
  · have hstep : (1 / (2 * Real.pi)) * I0 ≤ 2 / Δ0 s := by
      have h := mul_le_mul_of_nonneg_left hI0 (show (0:ℝ) ≤ 1 / (2 * Real.pi) by positivity)
      have heq : (1 / (2 * Real.pi)) * (4 * Real.pi / Δ0 s) = 2 / Δ0 s := by
        field_simp
        ring
      linarith [h, heq]
    exact hXtil.trans (mul_le_mul_of_nonneg_right hstep (norm_nonneg _))
  · have hI1' : I1 ≤ 4 * Real.pi / Δ1 s := hI1
    have hJ' : c1 s / T * J ≤ c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2))) :=
      mul_le_mul_of_nonneg_left hJ hcoe
    have h1 : ‖diff T X s‖ / (2 * Real.pi) * I1
        ≤ ‖diff T X s‖ / (2 * Real.pi) * (4 * Real.pi / Δ1 s) :=
      mul_le_mul_of_nonneg_left hI1' (by positivity)
    have h2 : (c1 s / T * J + c1 s / T * J)
        ≤ c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2)))
            + c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2))) := by linarith [hJ']
    have h3 : ‖X s‖ / (2 * Real.pi) * (c1 s / T * J + c1 s / T * J)
        ≤ ‖X s‖ / (2 * Real.pi) *
            (c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2)))
              + c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2)))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hsum : ‖diff T X s‖ / (2 * Real.pi) * I1
          + ‖X s‖ / (2 * Real.pi) * (c1 s / T * J + c1 s / T * J)
        ≤ ‖diff T X s‖ / (2 * Real.pi) * (4 * Real.pi / Δ1 s)
          + ‖X s‖ / (2 * Real.pi) *
            (c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2)))
              + c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2)))) := by
      linarith [h1, h3]
    have heq : ‖diff T X s‖ / (2 * Real.pi) * (4 * Real.pi / Δ1 s)
          + ‖X s‖ / (2 * Real.pi) *
            (c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2)))
              + c1 s / T * (2 / (1 - Real.cos (Δ1 s / 2))))
        = 2 / Δ1 s * ‖diff T X s‖
          + 2 * c1 s / (Real.pi * T * (1 - Real.cos (Δ1 s / 2))) * ‖X s‖ := by
      field_simp
      ring
    exact hDXtil.trans (hsum.trans heq.le)

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
