/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.GroverPlane.Angle — Lemma 10: lower bound for the Grover angle increment

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Lemma 10, Eq. (B26), p. 21.

The Grover angle is `ϑ_k := arcsin √q_k ∈ (0, π/2]` (Eq. (B18)).  With
`u₀ := √(q₀(1-q₀))` and `ω* := min{1/48, cρR*/4}`, Lemma 10 proves that, as long as the
iterate is outside the Newton region (`e_k > r_N`),

`ϑ_{k+1} - ϑ_k ≥ ω* u₀`   (Eq. (B26)).

The proof combines

* Eq. (B27): `sin(2ϑ_k) ≥ u₀/16`, from `sin(2ϑ_k) = 2ξ_k u₀` and Lemma 8's `ξ_k ≥ 1/32`;
* Eq. (B28): `q_{k+1} - q_k ≥ (cρR*/2) u₀ sin(2ϑ_k)`, from the Armijo condition and the
  accepted-radius bound of Lemma 9;
* Eq. (B29): `q_{k+1} - q_k = sin(2ϑ_k + Δ_k) sin Δ_k ≤ (sin(2ϑ_k) + Δ_k) sin Δ_k`,

and a contradiction argument on `Δ_k := ϑ_{k+1} - ϑ_k`.  This file formalizes the
contradiction argument; the displayed estimates (B27)–(B29), which involve the Grover-plane
geometry of Lemmas 8–9 and elementary sine inequalities, enter as hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.GroverPlane.Angle

/-- **Lemma 10, angle increment** (arXiv:2603.26039v3, Eq. (B26), p. 21).  Let
`ω = ω* = min{1/48, cρR*/4}` with `0 < c ≤ 1/8`, `0 < ρ < 1`, `R* > 0`, and
`u₀ = √(q₀(1-q₀)) > 0`.  Suppose the Grover angles `ϑ_k`, the increments
`Δ_k = ϑ_{k+1}-ϑ_k` (with `0 ≤ Δ_k ≤ π`) and the probability increments
`qdiff k = q_{k+1} - q_k` satisfy the paper's estimates

* (B27) `u₀/16 ≤ sin(2ϑ_k)`;
* (B28) `(cρR*/2) u₀ sin(2ϑ_k) ≤ qdiff k`;
* (B29) `qdiff k ≤ (sin(2ϑ_k) + Δ_k) sin(Δ_k)` and `sin(Δ_k) ≤ Δ_k`.

Then `Δ_k ≥ ω* u₀` for every `k`. -/
theorem lemma10_grover_angle_increment
    (c ρ Rstar ω u0 : ℝ) (hc : 0 < c) (hc8 : c ≤ 1 / 8)
    (hρ : 0 < ρ) (hRstar : 0 < Rstar) (hu0 : 0 < u0)
    (hω : ω = min (1 / 48) (c * ρ * Rstar / 4))
    (ϑ qdiff Δ : ℕ → ℝ)
    (hΔ0 : ∀ k, 0 ≤ Δ k) (hΔpi : ∀ k, Δ k ≤ Real.pi)
    (hB27 : ∀ k, u0 / 16 ≤ Real.sin (2 * ϑ k))
    (hB28 : ∀ k, c * ρ * Rstar / 2 * u0 * Real.sin (2 * ϑ k) ≤ qdiff k)
    (hB29 : ∀ k, qdiff k ≤ (Real.sin (2 * ϑ k) + Δ k) * Real.sin (Δ k))
    (hsinΔ : ∀ k, Real.sin (Δ k) ≤ Δ k) :
    ∀ k, ω * u0 ≤ Δ k := by
  intro k
  have hcρR : 0 < c * ρ * Rstar := by positivity
  have hω0 : 0 < ω := by
    rw [hω]
    exact lt_min (by norm_num) (by positivity)
  have hω1 : ω ≤ 1 / 48 := by
    rw [hω]; exact min_le_left _ _
  have hω2 : ω ≤ c * ρ * Rstar / 4 := by
    rw [hω]; exact min_le_right _ _
  by_contra hcon
  push_neg at hcon
  -- Positivity of `sin(2ϑ_k)` (from (B27)) and of `sin(Δ_k)`.
  have hsinpos : 0 < Real.sin (2 * ϑ k) := lt_of_lt_of_le (by positivity) (hB27 k)
  have hsinD0 : 0 ≤ Real.sin (Δ k) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (hΔ0 k) (hΔpi k)
  -- `u₀ ≤ 16 sin(2ϑ_k)`, hence `ω u₀ ≤ sin(2ϑ_k)/3`.
  have hu0le : u0 ≤ 16 * Real.sin (2 * ϑ k) := by linarith [hB27 k]
  have hωu : ω * u0 ≤ (1 / 3) * Real.sin (2 * ϑ k) := by
    have h1 : ω * u0 ≤ (1 / 48) * u0 := mul_le_mul_of_nonneg_right hω1 hu0.le
    have h2 : (1 / 48 : ℝ) * u0 ≤ (1 / 48) * (16 * Real.sin (2 * ϑ k)) :=
      mul_le_mul_of_nonneg_left hu0le (by norm_num)
    have h3 : (1 / 48 : ℝ) * (16 * Real.sin (2 * ϑ k)) = (1 / 3) * Real.sin (2 * ϑ k) := by
      ring
    linarith [h1, h2, h3]
  -- `sin(2ϑ_k) + Δ_k < (4/3) sin(2ϑ_k)`.
  have hsum : Real.sin (2 * ϑ k) + Δ k < (4 / 3) * Real.sin (2 * ϑ k) := by
    linarith [hcon, hωu]
  -- Chain of inequalities from (B28) to a contradiction.
  have hchain1 : qdiff k ≤ (Real.sin (2 * ϑ k) + Δ k) * Real.sin (Δ k) := hB29 k
  have hchain2 : (Real.sin (2 * ϑ k) + Δ k) * Real.sin (Δ k)
      ≤ (Real.sin (2 * ϑ k) + Δ k) * Δ k :=
    mul_le_mul_of_nonneg_left (hsinΔ k) (by linarith [hsinpos, hΔ0 k])
  have hchain3 : (Real.sin (2 * ϑ k) + Δ k) * Δ k
      ≤ ((4 / 3) * Real.sin (2 * ϑ k)) * Δ k :=
    mul_le_mul_of_nonneg_right hsum.le (hΔ0 k)
  have hchain4 : ((4 / 3) * Real.sin (2 * ϑ k)) * Δ k
      < ((4 / 3) * Real.sin (2 * ϑ k)) * (ω * u0) :=
    mul_lt_mul_of_pos_left hcon (by positivity)
  have hω23 : (4 / 3) * ω ≤ c * ρ * Rstar / 2 := by
    nlinarith [hω2, hcρR]
  have hchain5 : ((4 / 3) * Real.sin (2 * ϑ k)) * (ω * u0)
      ≤ (c * ρ * Rstar / 2) * u0 * Real.sin (2 * ϑ k) := by
    have h1 : ((4 / 3) * ω) * u0 ≤ (c * ρ * Rstar / 2) * u0 :=
      mul_le_mul_of_nonneg_right hω23 (le_of_lt hu0)
    have h2 : ((4 / 3) * ω) * u0 * Real.sin (2 * ϑ k)
        ≤ ((c * ρ * Rstar / 2) * u0) * Real.sin (2 * ϑ k) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hsinpos)
    linarith [h2]
  have hfinal : qdiff k < (c * ρ * Rstar / 2) * u0 * Real.sin (2 * ϑ k) := by
    linarith [hchain1, hchain2, hchain3, hchain4, hchain5]
  linarith [hB28 k, hfinal]

end Qatlib.Papers.QSearchPrec26.RmSearch.GroverPlane.Angle
