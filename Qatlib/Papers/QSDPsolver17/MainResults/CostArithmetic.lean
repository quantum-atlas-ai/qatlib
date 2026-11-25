/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Width and cost arithmetic in arXiv:1705.01843v4

Lemma 17 relates the support-size requirement to the width needed over
the solver's iterations. Lemma 16 uses additive bounds for the cost
components. These statements operate on the numeric bounds supplied
by the corresponding analyses.
-/

set_option autoImplicit false

open Qatlib.Papers.QSDPsolver17.MainResults

namespace Qatlib.Papers.QSDPsolver17.MainResults

/-- Taking the square root of a support-size estimate yields the explicit
pointwise width lower bound. -/
private theorem width_sqrt_bound (ℓ k L w C : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hw : 0 ≤ w) (hC : 0 < C)
    (h : ℓ ≤ k * L * (C * w ^ 2)) :
    (1 / Real.sqrt C) * Real.sqrt (ℓ / (k * L)) ≤ w := by
  have hs := Real.sqrt_le_sqrt ((div_le_iff₀ (mul_pos hk hL)).mpr
    (by linarith only [h] : ℓ ≤ C * w ^ 2 * (k * L)))
  rw [Real.sqrt_mul hC.le, Real.sqrt_sq hw] at hs
  rw [one_div_mul_eq_div, div_le_iff₀ (Real.sqrt_pos_of_pos hC)]
  simpa [mul_comm] using hs

/-- Lemma 17's argument when the iteration parameter is unrounded.
The constant is explicit in the pointwise width inequality. -/
theorem lemma17_width_lower_bound {ℓ k : ℕ} {T w R ε L : ℝ}
    (hk : 0 < (k : ℝ)) (hw : 0 < w) (hR : 0 < R) (hε : 0 < ε) (hL : 0 < L)
    (hkT : 1 ≤ (k : ℝ) * T) (hT : T = 9 * w ^ 2 * R ^ 2 * L / ε ^ 2)
    (hℓ : (ℓ : ℝ) ≤ (k : ℝ) * T + 1) :
    BigOmegaAt (R * w / ε) (Real.sqrt ((ℓ : ℝ) / ((k : ℝ) * L))) := by
  refine ⟨1 / Real.sqrt 18, by positivity, ?_⟩
  apply width_sqrt_bound _ _ _ _ 18 hk hL (by positivity) (by norm_num)
  calc
    (ℓ : ℝ) ≤ 2 * (k : ℝ) * T := by linarith only [hℓ, hkT]
    _ = (k : ℝ) * L * (18 * (R * w / ε) ^ 2) := by rw [hT]; ring

/-- With the ceiling from Theorem 5, the same width scale follows
whenever the unrounded iteration parameter is at least one. -/
theorem lemma17_rounded_rounds_lower_bound {ℓ k : ℕ} {w R ε L : ℝ}
    (hk : 0 < k) (hw : 0 < w) (hR : 0 < R) (hε : 0 < ε) (hL : 0 < L)
    (hT : 1 ≤ 9 * w ^ 2 * R ^ 2 * L / ε ^ 2)
    (hℓ : ℓ ≤ k * Nat.ceil (9 * w ^ 2 * R ^ 2 * L / ε ^ 2) + 1) :
    BigOmegaAt (R * w / ε) (Real.sqrt ((ℓ : ℝ) / ((k : ℝ) * L))) := by
  let T : ℝ := 9 * w ^ 2 * R ^ 2 * L / ε ^ 2
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (Nat.ceil T : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ T)).le
  have hℓ' : (ℓ : ℝ) ≤ (k : ℝ) * (Nat.ceil T : ℝ) + 1 := by exact_mod_cast hℓ
  have hc := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg k)
  have hkt := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg k)
  refine ⟨1 / Real.sqrt 27, by positivity, ?_⟩
  apply width_sqrt_bound _ _ _ _ 27 (by positivity) hL (by positivity) (by norm_num)
  calc
    (ℓ : ℝ) ≤ 3 * (k : ℝ) * T := by linarith only [hℓ', hc, hkt, hk₁]
    _ = (k : ℝ) * L * (27 * (R * w / ε) ^ 2) := by dsimp [T]; ring

/-- Pointwise cost annotations with nonnegative comparison quantities
can be added, as in the search and minimization budget of Lemma 16. -/
theorem bigOAt_add {a b c d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hab : BigOAt a b) (hcd : BigOAt c d) : BigOAt (a + c) (b + d) := by
  obtain ⟨C₁, h₁, hab⟩ := hab
  obtain ⟨C₂, _, hcd⟩ := hcd
  refine ⟨max C₁ C₂, h₁.trans_le (le_max_left _ _), ?_⟩
  rw [mul_add]
  exact add_le_add (hab.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hb))
    (hcd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd))

end Qatlib.Papers.QSDPsolver17.MainResults
