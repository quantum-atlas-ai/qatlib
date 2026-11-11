/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds.Lemma08ReflectionBound

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9: norm bound for `D V_T(s)`

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
fixed arXiv:2111.08152, Lemma 9 / Eqs. (51)--(56), page 11.

Applying the discrete product rule to Lemma 7,

`D V_T(s) = D F_T(s) [I + DP_T(s+1/T)(2P_T(s+1/T)-I)]
           + F_T(s) [D^(2)P_T(s)(2P_T(s+1/T)-I) + 2 (DP_T(s))²]`   (Eq. (53))

and hence
`‖D V_T(s)‖ ≤ ‖D F_T(s)‖ (1 + ‖DP_T(s+1/T)‖)
             + ‖F_T(s)‖ (‖D^(2)P_T(s)‖ + 2‖DP_T(s)‖²)`.           (Eq. (54))

The paper then bounds `‖D F_T(s)‖` by the Taylor series of `F_T` in terms of
`D₃` (Eqs. (55)--(56)):
`‖D F_T(s)‖ ≤ ‖D^(2)P_T(s)‖ D₃(max(‖DP_T(s+1/T)‖, ‖DP_T(s)‖))`.

The operator algebra and the norm chain (53)--(54) are fully proved below.
The Taylor-series estimate (56) is carried as the hypothesis `hTaylor`: it is
the one analytic input of the lemma (an infinite series for the inverse square
root of `I - (DP_T)²`), which the paper derives from the scalar expansion of
`D₃`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- Fixed arXiv:2111.08152, Lemma 9 (Eq. (51), p. 11): if `V_T` has the form of
Lemma 7 and the Taylor estimate Eq. (56) holds, then

`‖D V_T(s)‖ ≤ (1 + ‖DP_T(s+1/T)‖) ‖D^(2)P_T(s)‖ D₃(max(‖DP_T(s+1/T)‖,‖DP_T(s)‖))
             + ‖F_T(s)‖ (‖D^(2)P_T(s)‖ + 2‖DP_T(s)‖²)`. -/
theorem source_lemma9
    (T : ℝ) (P F V : ℝ → R) (s : ℝ)
    (hV : ∀ t, V t = F t * (1 + diff T P t * Setup.refl (P t)))
    (hreflect : ∀ t, ‖Setup.refl (P t)‖ ≤ 1)
    (hTaylor : ‖diff T F s‖ ≤
      ‖diff2 T P s‖ * Dfun3 (max ‖diff T P (s + 1 / T)‖ ‖diff T P s‖)) :
    ‖diff T V s‖ ≤
      (1 + ‖diff T P (s + 1 / T)‖) * ‖diff2 T P s‖ *
          Dfun3 (max ‖diff T P (s + 1 / T)‖ ‖diff T P s‖)
        + ‖F s‖ * (‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2) := by
  -- (53): the discrete product rule applied to the form of Lemma 7.
  -- Generic noncommutative-ring cancellation (with `R'` and `R` the reflections
  -- at `s+1/T` and `s`): `F'(1+bR') - F(1+aR)
  -- = (F'-F)(1+bR') + F((b-a)R' + a(R'-R))`.
  have hgen : ∀ (F₀ F₁ R₀ R₁ a b : R),
      F₁ * (1 + b * R₁) - F₀ * (1 + a * R₀)
        = (F₁ - F₀) * (1 + b * R₁) + F₀ * ((b - a) * R₁ + a * (R₁ - R₀)) := by
    intro F₀ F₁ R₀ R₁ a b
    noncomm_ring
  -- the reflection difference is twice the first difference of `P`: `R' - R = 2a`
  have hRR : Setup.refl (P (s + 1 / T)) - Setup.refl (P s)
      = diff T P s + diff T P s := by
    simp only [Setup.refl, diff]
    noncomm_ring
  have hDV : diff T V s =
      diff T F s * (1 + diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T)))
        + F s * (diff2 T P s * Setup.refl (P (s + 1 / T))
          + diff T P s * (diff T P s + diff T P s)) := by
    show V (s + 1 / T) - V s = _
    rw [hV (s + 1 / T), hV s,
      hgen (F s) (F (s + 1 / T)) (Setup.refl (P s))
        (Setup.refl (P (s + 1 / T))) (diff T P s) (diff T P (s + 1 / T)),
      hRR]
    rw [show diff T P (s + 1 / T) - diff T P s = diff2 T P s from rfl]
    rw [show diff T F s = F (s + 1 / T) - F s from rfl]
  have hnorm1 : ‖1 + diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T))‖
      ≤ 1 + ‖diff T P (s + 1 / T)‖ := by
    calc ‖1 + diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T))‖
        ≤ ‖(1 : R)‖ + ‖diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T))‖ :=
          norm_add_le _ _
      _ ≤ 1 + ‖diff T P (s + 1 / T)‖ * ‖Setup.refl (P (s + 1 / T))‖ := by
          rw [norm_one]
          linarith [norm_mul_le (diff T P (s + 1 / T)) (Setup.refl (P (s + 1 / T)))]
      _ ≤ 1 + ‖diff T P (s + 1 / T)‖ * 1 := by
          have h := mul_le_mul_of_nonneg_left (hreflect (s + 1 / T))
            (norm_nonneg (diff T P (s + 1 / T)))
          linarith
      _ = 1 + ‖diff T P (s + 1 / T)‖ := by ring
  have hnorm2 : ‖diff2 T P s * Setup.refl (P (s + 1 / T))
        + diff T P s * (diff T P s + diff T P s)‖
      ≤ ‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2 := by
    have hsq : ‖diff T P s * (diff T P s + diff T P s)‖ ≤ 2 * ‖diff T P s‖ ^ 2 := by
      calc ‖diff T P s * (diff T P s + diff T P s)‖
          ≤ ‖diff T P s‖ * ‖diff T P s + diff T P s‖ := norm_mul_le _ _
        _ ≤ ‖diff T P s‖ * (‖diff T P s‖ + ‖diff T P s‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ = 2 * ‖diff T P s‖ ^ 2 := by ring
    calc ‖diff2 T P s * Setup.refl (P (s + 1 / T))
          + diff T P s * (diff T P s + diff T P s)‖
        ≤ ‖diff2 T P s * Setup.refl (P (s + 1 / T))‖
            + ‖diff T P s * (diff T P s + diff T P s)‖ := norm_add_le _ _
      _ ≤ ‖diff2 T P s‖ * 1 + 2 * ‖diff T P s‖ ^ 2 := by
          have h1 : ‖diff2 T P s * Setup.refl (P (s + 1 / T))‖ ≤ ‖diff2 T P s‖ * 1 :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_left (hreflect (s + 1 / T)) (norm_nonneg _))
          linarith
      _ = ‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2 := by ring
  calc ‖diff T V s‖
      = ‖diff T F s * (1 + diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T)))
          + F s * (diff2 T P s * Setup.refl (P (s + 1 / T))
            + diff T P s * (diff T P s + diff T P s))‖ := by rw [hDV]
    _ ≤ ‖diff T F s * (1 + diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T)))‖
          + ‖F s * (diff2 T P s * Setup.refl (P (s + 1 / T))
            + diff T P s * (diff T P s + diff T P s))‖ := norm_add_le _ _
    _ ≤ ‖diff T F s‖ * (1 + ‖diff T P (s + 1 / T)‖)
          + ‖F s‖ * (‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2) := by
        have h1 : ‖diff T F s * (1 + diff T P (s + 1 / T) * Setup.refl (P (s + 1 / T)))‖
            ≤ ‖diff T F s‖ * (1 + ‖diff T P (s + 1 / T)‖) :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left hnorm1 (norm_nonneg _))
        have h2 : ‖F s * (diff2 T P s * Setup.refl (P (s + 1 / T))
              + diff T P s * (diff T P s + diff T P s))‖
            ≤ ‖F s‖ * (‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2) :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left hnorm2 (norm_nonneg _))
        linarith
    _ ≤ (1 + ‖diff T P (s + 1 / T)‖) * ‖diff2 T P s‖ *
          Dfun3 (max ‖diff T P (s + 1 / T)‖ ‖diff T P s‖)
        + ‖F s‖ * (‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2) := by
        have h1 : ‖diff T F s‖ * (1 + ‖diff T P (s + 1 / T)‖)
            ≤ (1 + ‖diff T P (s + 1 / T)‖) *
                (‖diff2 T P s‖ *
                  Dfun3 (max ‖diff T P (s + 1 / T)‖ ‖diff T P s‖)) := by
          calc ‖diff T F s‖ * (1 + ‖diff T P (s + 1 / T)‖)
              = (1 + ‖diff T P (s + 1 / T)‖) * ‖diff T F s‖ := mul_comm _ _
            _ ≤ (1 + ‖diff T P (s + 1 / T)‖) *
                  (‖diff2 T P s‖ *
                    Dfun3 (max ‖diff T P (s + 1 / T)‖ ‖diff T P s‖)) :=
                mul_le_mul_of_nonneg_left hTaylor
                  (add_nonneg zero_le_one (norm_nonneg (diff T P (s + 1 / T))))
        nlinarith [h1]
    _ = (1 + ‖diff T P (s + 1 / T)‖) * ‖diff2 T P s‖ *
          Dfun3 (max ‖diff T P (s + 1 / T)‖ ‖diff T P s‖)
        + ‖F s‖ * (‖diff2 T P s‖ + 2 * ‖diff T P s‖ ^ 2) := by ring

end Qatlib.Papers.AdiabaticQLS21.MainResults.Bounds
