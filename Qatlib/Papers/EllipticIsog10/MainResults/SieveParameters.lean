/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemmas A.4 and A.7: the sieve level parameters `Bᵢ = ⌊N/ρⁱ⌋`

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Appendix A.

Both parameter lemmas of the appendix choose the labels of the sieve stages as
`Bᵢ = ⌊N/ρⁱ⌋` and then verify the hypotheses of the combination procedure:

* **Lemma A.4** (cyclic `N`, power-of-two case): with `ρ = (N/2)^{1/m}` one has
  `B₀ = N`, `B_m = 2` and `4k ≤ B_{i-1}/B_i ≤ 2^k/k` for `i ∈ {1, …, m}`.  The
  upper bound comes from `B_{i-1}/B_i ≤ ρ/(1 - ρⁱ/N) ≤ 2ρ` together with
  `ρ ≤ 2^k/(2k)`; the lower bound from `B_{i-1}/B_i ≥ ρ - ρⁱ/N ≥ ρ - 1/2`
  together with `ρ - 1/2 ≥ 4k`.
* **Lemma A.7** (general finite abelian `A`, non-cyclic case): with `ρ = N^{1/m}`
  one has `B₀ = N`, `B_m = 1` and `B_{i-1}/B_i ≤ 2^k/(2k)`.

This module formalizes the *floor arithmetic*: the endpoint values `B₀ = N`,
`B_m = 2` / `B_m = 1`, and the ratio bounds `B_{i-1}/B_i ≤ 2ρ` and
`ρ - 1/2 ≤ B_{i-1}/B_i` that the source proves by "using `ρⁱ/N ≤ 1/2`".  The two
analytic estimates that the source obtains separately for `N > N₀` — namely
`ρ ≤ 2^k/(2k)` and `ρ - 1/2 ≥ 4k` (both derived there from
`ρ = 2^{Θ(k)}`) — are kept as explicit hypotheses, so these results are partial
formalizations of A.4/A.7; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

noncomputable section

/-- The `i`-th sieve level bound `Bᵢ = ⌊N/ρⁱ⌋` shared by Lemma A.4 and Lemma A.7. -/
def layerBound (N : ℕ) (ρ : ℝ) (i : ℕ) : ℕ := ⌊(N : ℝ) / ρ ^ i⌋₊

/-- **Lemma A.4 / A.7, first endpoint:** `B₀ = ⌊N/ρ⁰⌋ = N`. -/
theorem layerBound_zero (N : ℕ) (ρ : ℝ) : layerBound N ρ 0 = N := by
  simp [layerBound]

/-- **Lemma A.4, second endpoint:** `ρ = (N/2)^{1/m}` gives `ρᵐ = N/2`, hence
`B_m = ⌊N/(N/2)⌋ = 2`. -/
theorem layerBound_two {N m : ℕ} {ρ : ℝ} (hN : 0 < N)
    (hρm : ρ ^ m = (N : ℝ) / 2) : layerBound N ρ m = 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h : (N : ℝ) / ρ ^ m = 2 := by
    rw [hρm]
    field_simp
  rw [layerBound, h]
  norm_num

/-- **Lemma A.7, second endpoint:** `ρ = N^{1/m}` gives `ρᵐ = N`, hence
`B_m = ⌊N/N⌋ = 1`. -/
theorem layerBound_one {N m : ℕ} {ρ : ℝ} (hN : 0 < N)
    (hρm : ρ ^ m = (N : ℝ)) : layerBound N ρ m = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h : (N : ℝ) / ρ ^ m = 1 := by
    rw [hρm]
    field_simp
  rw [layerBound, h]
  norm_num

/-- **The stage estimate `Bᵢ ≥ 2`.** If `ρ > 0` and `ρⁱ ≤ N/2` then
`N/ρⁱ ≥ 2`, so the floor `Bᵢ` is at least `2`; in particular it is positive,
which is what the ratio computations below divide by.  In Lemma A.4 this is
applied with `i ≤ m` and `ρⁱ ≤ ρᵐ = N/2`; in Lemma A.7 with `ρ ≥ 2`. -/
theorem two_le_layerBound {N i : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ρ ^ i ≤ (N : ℝ) / 2) : 2 ≤ layerBound N ρ i := by
  have hpos : 0 < ρ ^ i := pow_pos hρ i
  have hden : (2 : ℝ) ≤ (N : ℝ) / ρ ^ i := by
    rw [le_div_iff₀ hpos]
    linarith
  exact (Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0)).mpr hden

/-- `Bᵢ = ⌊N/ρⁱ⌋ ≤ N/ρⁱ`. -/
theorem layerBound_le {N i : ℕ} {ρ : ℝ} (h : 0 ≤ (N : ℝ) / ρ ^ i) :
    (layerBound N ρ i : ℝ) ≤ (N : ℝ) / ρ ^ i :=
  Nat.floor_le h

/-- `N/ρⁱ < Bᵢ + 1`, the strict side of the floor. -/
theorem layerBound_lt {N i : ℕ} {ρ : ℝ} :
    (N : ℝ) / ρ ^ i < (layerBound N ρ i : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- **Upper ratio bound (Lemma A.4 / A.7).** For `1 ≤ i`, `ρ ≥ 1` and
`ρⁱ ≤ N/2`,

`B_{i-1}/B_i ≤ ρ/(1 - ρⁱ/N) ≤ 2ρ`.

The proof follows the source: `B_{i-1} ≤ N/ρ^{i-1} = ρ·(N/ρⁱ) < ρ·(Bᵢ + 1)`
and `Bᵢ ≥ 1`. -/
theorem layerBound_ratio_le_two_mul {N i : ℕ} {ρ : ℝ}
    (hρ1 : 1 ≤ ρ) (hi1 : 1 ≤ i) (hsmall : ρ ^ i ≤ (N : ℝ) / 2) :
    (layerBound N ρ (i - 1) : ℝ) ≤ 2 * ρ * (layerBound N ρ i : ℝ) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hhalf : 0 < (N : ℝ) / 2 := lt_of_lt_of_le (pow_pos hρpos i) hsmall
    linarith
  have hprev : (layerBound N ρ (i - 1) : ℝ) ≤ (N : ℝ) / ρ ^ (i - 1) :=
    layerBound_le (by positivity)
  have hlt : (N : ℝ) / ρ ^ i < (layerBound N ρ i : ℝ) + 1 := layerBound_lt
  have htwo : 2 ≤ layerBound N ρ i := two_le_layerBound hρpos hsmall
  have hB1 : (1 : ℝ) ≤ (layerBound N ρ i : ℝ) := by
    have h2 : (2 : ℝ) ≤ (layerBound N ρ i : ℝ) := by exact_mod_cast htwo
    linarith
  have hpow : ρ ^ (i - 1) * ρ = ρ ^ i := by
    rw [← pow_succ, Nat.sub_add_cancel hi1]
  have hρpowne : ρ ^ (i - 1) ≠ 0 := ne_of_gt (pow_pos hρpos _)
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hkey : (N : ℝ) / ρ ^ (i - 1) = ρ * ((N : ℝ) / ρ ^ i) := by
    rw [← hpow]
    field_simp
  calc (layerBound N ρ (i - 1) : ℝ) ≤ (N : ℝ) / ρ ^ (i - 1) := hprev
    _ = ρ * ((N : ℝ) / ρ ^ i) := hkey
    _ ≤ ρ * ((layerBound N ρ i : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hlt.le hρpos.le
    _ ≤ 2 * ρ * (layerBound N ρ i : ℝ) := by nlinarith

/-- **Lower ratio bound (Lemma A.4).** For `1 ≤ i`, `ρ ≥ 1` and `ρⁱ ≤ N/2`,

`B_{i-1}/B_i ≥ ρ - ρⁱ/N ≥ ρ - 1/2`.

The proof follows the source: `B_{i-1} > N/ρ^{i-1} - 1`,
`Bᵢ ≤ N/ρⁱ`, and `N/(2ρⁱ) ≥ 1`. -/
theorem layerBound_ratio_min {N i : ℕ} {ρ : ℝ}
    (hρ1 : 1 ≤ ρ) (hi1 : 1 ≤ i) (hsmall : ρ ^ i ≤ (N : ℝ) / 2) :
    ρ - 1 / 2 ≤ (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hhalf : 0 < (N : ℝ) / 2 := lt_of_lt_of_le (pow_pos hρpos i) hsmall
    linarith
  have htwo : 2 ≤ layerBound N ρ i := two_le_layerBound hρpos hsmall
  have hBpos : (0 : ℝ) < (layerBound N ρ i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) htwo)
  rw [le_div_iff₀ hBpos]
  have hBle : (layerBound N ρ i : ℝ) ≤ (N : ℝ) / ρ ^ i := layerBound_le (by positivity)
  have hpred : (N : ℝ) / ρ ^ (i - 1) - 1 < (layerBound N ρ (i - 1) : ℝ) := by
    have hlt : (N : ℝ) / ρ ^ (i - 1) < (layerBound N ρ (i - 1) : ℝ) + 1 := layerBound_lt
    linarith
  have hden : 1 ≤ ((N : ℝ) / ρ ^ i) / 2 := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) / ρ ^ i := le_trans (by exact_mod_cast htwo) hBle
    linarith
  have hpow : ρ ^ (i - 1) * ρ = ρ ^ i := by
    rw [← pow_succ, Nat.sub_add_cancel hi1]
  have hρpowne : ρ ^ (i - 1) ≠ 0 := ne_of_gt (pow_pos hρpos _)
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hkey : (N : ℝ) / ρ ^ (i - 1) - 1 = ρ * ((N : ℝ) / ρ ^ i) - 1 := by
    rw [← hpow]
    field_simp
  have hhalf : 0 ≤ ρ - 1 / 2 := by linarith
  have hstep : (ρ - 1 / 2) * (layerBound N ρ i : ℝ) ≤ (ρ - 1 / 2) * ((N : ℝ) / ρ ^ i) :=
    mul_le_mul_of_nonneg_left hBle hhalf
  have hstep2 : (ρ - 1 / 2) * ((N : ℝ) / ρ ^ i) ≤ ρ * ((N : ℝ) / ρ ^ i) - 1 := by
    nlinarith
  linarith

/-- **Lemma A.4, ratio bounds.** Under the source's two analytic estimates
`4k ≤ ρ - 1/2` and `2ρ ≤ 2^k/k`, every stage ratio of the sieve satisfies
`4k ≤ B_{i-1}/B_i ≤ 2^k/k`, which is the hypothesis of the combination
procedure (Lemma A.2). -/
theorem layerBound_ratio_bounds {N m k : ℕ} {ρ : ℝ}
    (hρ1 : 1 ≤ ρ) (hρm : ρ ^ m = (N : ℝ) / 2)
    (hlo : 4 * (k : ℝ) ≤ ρ - 1 / 2) (hhi : 2 * ρ ≤ (2 : ℝ) ^ k / (k : ℝ)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m →
      4 * (k : ℝ) ≤ (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ∧
        (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ≤ (2 : ℝ) ^ k / (k : ℝ) := by
  intro i hi1 him
  have hsmall : ρ ^ i ≤ (N : ℝ) / 2 := by
    rw [← hρm]
    exact pow_le_pow_right₀ hρ1 him
  have htwo : 2 ≤ layerBound N ρ i := two_le_layerBound (lt_of_lt_of_le zero_lt_one hρ1) hsmall
  have hBpos : (0 : ℝ) < (layerBound N ρ i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) htwo)
  have hdiv : (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ≤ 2 * ρ := by
    rw [div_le_iff₀ hBpos]
    linarith [layerBound_ratio_le_two_mul hρ1 hi1 hsmall]
  exact ⟨le_trans hlo (layerBound_ratio_min hρ1 hi1 hsmall), le_trans hdiv hhi⟩

/-- **Lemma A.4 assembled.** The endpoint values `B₀ = N`, `B_m = 2` and the
stage ratio bounds all hold for the source's choice `ρ = (N/2)^{1/m}`. -/
theorem lemmaA4 {N m k : ℕ} {ρ : ℝ}
    (hN : 0 < N) (hρ1 : 1 ≤ ρ) (hρm : ρ ^ m = (N : ℝ) / 2)
    (hlo : 4 * (k : ℝ) ≤ ρ - 1 / 2) (hhi : 2 * ρ ≤ (2 : ℝ) ^ k / (k : ℝ)) :
    layerBound N ρ 0 = N ∧ layerBound N ρ m = 2 ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ m →
        4 * (k : ℝ) ≤ (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ∧
          (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ≤ (2 : ℝ) ^ k / (k : ℝ) :=
  ⟨layerBound_zero N ρ, layerBound_two hN hρm,
    layerBound_ratio_bounds hρ1 hρm hlo hhi⟩

/-- **Lemma A.7, ratio bound.** For the general abelian case `ρ = N^{1/m}`, the
source only needs the upper bound `B_{i-1}/B_i ≤ 2^k/(2k)`.  For `i < m` this is
`B_{i-1}/B_i ≤ 2ρ` with `ρⁱ ≤ ρ^{m-1} = N/ρ ≤ N/2`; the endpoint `i = m` is
handled separately, where `B_{m-1} ≤ N/ρ^{m-1} = ρ` and `B_m = 1`. -/
theorem layerBound_ratio_bounds_A7 {N m k : ℕ} {ρ : ℝ}
    (hN : 0 < N) (hρ2 : 2 ≤ ρ) (hρm : ρ ^ m = (N : ℝ))
    (hhi : 2 * ρ ≤ (2 : ℝ) ^ k / (2 * (k : ℝ))) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m →
      (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ≤ (2 : ℝ) ^ k / (2 * (k : ℝ)) := by
  intro i hi1 him
  have hρ1 : 1 ≤ ρ := le_trans (by norm_num) hρ2
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiv : (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ≤ 2 * ρ := by
    rcases eq_or_lt_of_le him with hEq | hLt
    · have hm1 : 1 ≤ m := hEq ▸ hi1
      have hBm : layerBound N ρ m = 1 := layerBound_one hN hρm
      have hpow : ρ ^ (m - 1) * ρ = ρ ^ m := by
        rw [← pow_succ, Nat.sub_add_cancel hm1]
      have hkey : (N : ℝ) / ρ ^ (m - 1) = ρ := by
        rw [div_eq_iff (ne_of_gt (pow_pos hρpos _)), mul_comm, hpow, hρm]
      have hprev : (layerBound N ρ (m - 1) : ℝ) ≤ (N : ℝ) / ρ ^ (m - 1) :=
        layerBound_le (by positivity)
      rw [hEq, hBm]
      simp only [Nat.cast_one, div_one]
      linarith
    · have hm1 : 1 ≤ m := le_trans hi1 (le_of_lt hLt)
      have him1 : i ≤ m - 1 := Nat.le_pred_of_lt hLt
      have hpow : ρ ^ (m - 1) * ρ = ρ ^ m := by
        rw [← pow_succ, Nat.sub_add_cancel hm1]
      have hkey : ρ ^ (m - 1) = (N : ℝ) / ρ := by
        rw [eq_div_iff (ne_of_gt hρpos)]
        rw [hpow, hρm]
      have hsmall : ρ ^ i ≤ (N : ℝ) / 2 := by
        have h1 : ρ ^ i ≤ ρ ^ (m - 1) := pow_le_pow_right₀ hρ1 him1
        have h3 : (N : ℝ) / ρ ≤ (N : ℝ) / 2 :=
          div_le_div_of_nonneg_left hNpos.le (by norm_num : (0 : ℝ) < 2) hρ2
        linarith
      have htwo : 2 ≤ layerBound N ρ i := two_le_layerBound hρpos hsmall
      have hBpos : (0 : ℝ) < (layerBound N ρ i : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num) htwo)
      have hle : (layerBound N ρ (i - 1) : ℝ) ≤ 2 * ρ * (layerBound N ρ i : ℝ) :=
        layerBound_ratio_le_two_mul hρ1 hi1 hsmall
      rw [div_le_iff₀ hBpos]
      linarith
  exact le_trans hdiv hhi

/-- **Lemma A.7 assembled.** The endpoint values `B₀ = N`, `B_m = 1` and the
upper stage ratio bound for the source's choice `ρ = N^{1/m}`. -/
theorem lemmaA7 {N m k : ℕ} {ρ : ℝ}
    (hN : 0 < N) (hρ2 : 2 ≤ ρ) (hρm : ρ ^ m = (N : ℝ))
    (hhi : 2 * ρ ≤ (2 : ℝ) ^ k / (2 * (k : ℝ))) :
    layerBound N ρ 0 = N ∧ layerBound N ρ m = 1 ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ m →
        (layerBound N ρ (i - 1) : ℝ) / (layerBound N ρ i : ℝ) ≤ (2 : ℝ) ^ k / (2 * (k : ℝ)) :=
  ⟨layerBound_zero N ρ, layerBound_one hN hρm,
    layerBound_ratio_bounds_A7 hN hρ2 hρm hhi⟩

end

end Qatlib.Papers.EllipticIsog10.MainResults
