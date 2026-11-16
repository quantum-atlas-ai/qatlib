/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section


/-! Polynomial resource substitution for the source SDP runtime expression. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSDPSpeedup16.MainResults.Corollary5Runtime
/-- The source runtime expression before primitive-cost substitution. -/
def theorem4RuntimeRHS (R δ Gh GM TMeas : ℝ) : ℝ :=
  (R ^ 21 / δ ^ 11) * Gh * GM + (R ^ 13 / δ ^ 5) * TMeas

/-- The target runtime monomial of Corollary 5: `√n √m s² R³² / δ¹⁸`. -/
def corollary5RuntimeRHS (n m s R δ : ℝ) : ℝ :=
  Real.sqrt n * Real.sqrt m * s ^ 2 * R ^ 32 / δ ^ 18

/-- Corollary 5 / Corollary 17 (p. 20): substituting the source bounds
`G_h ≤ c₁ √m R²/δ`, `G_M ≤ c₂ √n s² R⁹/δ⁶`, `T_Meas ≤ c₃ s (16R/δ)²` into Theorem 4's
runtime `(R²¹/δ¹¹) G_h G_M + (R¹³/δ⁵) T_Meas` yields
`(c₁c₂ + 256c₃) √n √m s² R³²/δ¹⁸`.

The hypotheses `1 ≤ n`, `1 ≤ m`, `1 ≤ s`, `1 ≤ R`, `δ ≤ 1` are the source's
normalisation regime (dimensions, sparsity and size parameter at least one; additive
error at most one) and are used exactly to absorb the measurement term into the Gibbs
term as on p. 20. -/
theorem corollary5_runtime (n m s R δ Gh GM TMeas c₁ c₂ c₃ : ℝ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hs : 1 ≤ s) (hR : 1 ≤ R) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hGM0 : 0 ≤ GM) (hc₁ : 0 ≤ c₁) (hc₃ : 0 ≤ c₃)
    (hGh : Gh ≤ c₁ * Real.sqrt m * R ^ 2 / δ)
    (hGM : GM ≤ c₂ * Real.sqrt n * s ^ 2 * R ^ 9 / δ ^ 6)
    (hTMeas : TMeas ≤ c₃ * s * (16 * R / δ) ^ 2) :
    theorem4RuntimeRHS R δ Gh GM TMeas ≤
      (c₁ * c₂ + 256 * c₃) * corollary5RuntimeRHS n m s R δ := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsqrtn : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
  have hsqrtm : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm
  have hs0 : 0 ≤ s := by linarith
  -- First (Gibbs) term after Eq. (96)–(97).
  have ht1 :
      (R ^ 21 / δ ^ 11) * Gh * GM ≤
        c₁ * c₂ * corollary5RuntimeRHS n m s R δ := by
    have hstep :
        (R ^ 21 / δ ^ 11) * Gh * GM ≤
          (R ^ 21 / δ ^ 11) * (c₁ * Real.sqrt m * R ^ 2 / δ) *
            (c₂ * Real.sqrt n * s ^ 2 * R ^ 9 / δ ^ 6) := by
      have h1 : (R ^ 21 / δ ^ 11) * Gh ≤ (R ^ 21 / δ ^ 11) * (c₁ * Real.sqrt m * R ^ 2 / δ) :=
        mul_le_mul_of_nonneg_left hGh (by positivity)
      exact mul_le_mul h1 hGM hGM0 (by positivity)
    have hid :
        (R ^ 21 / δ ^ 11) * (c₁ * Real.sqrt m * R ^ 2 / δ) *
            (c₂ * Real.sqrt n * s ^ 2 * R ^ 9 / δ ^ 6) =
          c₁ * c₂ * corollary5RuntimeRHS n m s R δ := by
      unfold corollary5RuntimeRHS
      field_simp
    linarith
  -- Second (measurement) term after Lemma 12 and Eq. (95).
  have ht2 :
      (R ^ 13 / δ ^ 5) * TMeas ≤ 256 * c₃ * corollary5RuntimeRHS n m s R δ := by
    have hstep :
        (R ^ 13 / δ ^ 5) * TMeas ≤ (R ^ 13 / δ ^ 5) * (c₃ * s * (16 * R / δ) ^ 2) :=
      mul_le_mul_of_nonneg_left hTMeas (by positivity)
    have hid : (R ^ 13 / δ ^ 5) * (c₃ * s * (16 * R / δ) ^ 2) =
        256 * c₃ * (s * R ^ 15 / δ ^ 7) := by
      field_simp
      ring
    -- Absorb the measurement monomial into the target monomial: this is where
    -- `1 ≤ n`, `1 ≤ m`, `1 ≤ s`, `1 ≤ R`, `δ ≤ 1` enter.
    have hdiv : 1 ≤ R ^ 17 / δ ^ 11 := by
      rw [one_le_div (by positivity)]
      calc δ ^ 11 ≤ 1 := pow_le_one₀ hδ0.le hδ1
        _ ≤ R ^ 17 := one_le_pow₀ hR
    have hcomb : 1 ≤ Real.sqrt n * Real.sqrt m * s * (R ^ 17 / δ ^ 11) := by
      have h1 : 1 ≤ Real.sqrt n * Real.sqrt m := one_le_mul_of_one_le_of_one_le hsqrtn hsqrtm
      have h2 : 1 ≤ Real.sqrt n * Real.sqrt m * s := one_le_mul_of_one_le_of_one_le h1 hs
      exact one_le_mul_of_one_le_of_one_le h2 hdiv
    have hmain : s * R ^ 15 / δ ^ 7 ≤ corollary5RuntimeRHS n m s R δ := by
      have heq : corollary5RuntimeRHS n m s R δ =
          (s * R ^ 15 / δ ^ 7) * (Real.sqrt n * Real.sqrt m * s * (R ^ 17 / δ ^ 11)) := by
        unfold corollary5RuntimeRHS
        field_simp
      have hnonneg : 0 ≤ s * R ^ 15 / δ ^ 7 := by positivity
      calc s * R ^ 15 / δ ^ 7 = (s * R ^ 15 / δ ^ 7) * 1 := by ring
        _ ≤ (s * R ^ 15 / δ ^ 7) *
              (Real.sqrt n * Real.sqrt m * s * (R ^ 17 / δ ^ 11)) :=
            mul_le_mul_of_nonneg_left hcomb hnonneg
        _ = corollary5RuntimeRHS n m s R δ := heq.symm
    have hcoef : 0 ≤ 256 * c₃ := by positivity
    calc (R ^ 13 / δ ^ 5) * TMeas
        ≤ (R ^ 13 / δ ^ 5) * (c₃ * s * (16 * R / δ) ^ 2) := hstep
      _ = 256 * c₃ * (s * R ^ 15 / δ ^ 7) := hid
      _ ≤ 256 * c₃ * corollary5RuntimeRHS n m s R δ :=
          mul_le_mul_of_nonneg_left hmain hcoef
  unfold theorem4RuntimeRHS
  have hsum := add_le_add ht1 ht2
  calc (R ^ 21 / δ ^ 11) * Gh * GM + (R ^ 13 / δ ^ 5) * TMeas
      ≤ c₁ * c₂ * corollary5RuntimeRHS n m s R δ +
          256 * c₃ * corollary5RuntimeRHS n m s R δ := hsum
    _ = (c₁ * c₂ + 256 * c₃) * corollary5RuntimeRHS n m s R δ := by ring


end Qatlib.Papers.QSDPSpeedup16.MainResults.Corollary5Runtime
