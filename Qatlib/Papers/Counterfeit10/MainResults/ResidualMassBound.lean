/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Counterfeit10.MainResults.ParityRestrictedIP

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Residual mass of the bounded-error coin-finding algorithm (Counterfeit10, Lemma 2)

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Section 2, Lemma 2.

One round of `Find∗(k)` leaves the register in the state

`|x⟩|0⟩ - 2 Σ_{q̃ ∈ Q_even ∩ Q_e} |q̃⟩|err_q̃⟩`,

so the failure mass is `ε = 4 Σ_{q̃} ‖err_q̃‖²`.  Each `‖err_q̃‖²` is at most `1/1600`
(the amplitude-amplification subroutine succeeds with probability at least `1599/1600`)
and `Q_even ∩ Q_e` is a subset of the parity-restricted query set with `2^{N-1}` elements,
while every branching coefficient carries the squared normalisation `γ² = 2^{-(N-1)}`.
Hence `ε ≤ 4 · 2^{-(N-1)} · 2^{N-1} / 1600 = 1/400`, which is the paper's Lemma 2.
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- The surviving branch set `Q_even ∩ Q_e` lives inside the parity-restricted queries and
therefore has at most `2^{N-1}` elements. -/
lemma card_le_evenQueries {N : ℕ} (hN : 0 < N) (t : Finset (CoinString N))
    (ht : t ⊆ evenQueries N) : t.card ≤ 2 ^ (N - 1) := by
  rw [← evenQueries_card hN]
  exact Finset.card_le_card ht

/-- Lemma 2 (arXiv:1009.0416v1, Section 2): the total residual mass `ε` of one round of
`Find∗(k)` is at most `1/400`.

`t` is the surviving branch set `Q_even ∩ Q_e` and `r q` is the squared norm `‖err_q‖²`
of the corresponding garbage component; the hypothesis `hrb` is the paper's
`1599/1600` amplitude-amplification success estimate. -/
theorem lemma2_residual_mass_bound {N : ℕ} (hN : 0 < N)
    (t : Finset (CoinString N)) (ht : t ⊆ evenQueries N) (r : CoinString N → ℚ)
    (hrb : ∀ q ∈ t, r q ≤ 1 / 1600) :
    4 * ∑ q ∈ t, ((2 : ℚ) ^ (N - 1))⁻¹ * r q ≤ 1 / 400 := by
  have hKpos : (0 : ℚ) < ((2 : ℚ) ^ (N - 1))⁻¹ := by positivity
  have hKne : ((2 : ℚ) ^ (N - 1)) ≠ 0 := by positivity
  have hcard : ((t.card : ℚ)) ≤ (2 : ℚ) ^ (N - 1) := by
    have hcast : ((2 ^ (N - 1) : ℕ) : ℚ) = (2 : ℚ) ^ (N - 1) := by push_cast; ring
    calc ((t.card : ℚ)) ≤ ((2 ^ (N - 1) : ℕ) : ℚ) := by
          exact_mod_cast card_le_evenQueries hN t ht
      _ = (2 : ℚ) ^ (N - 1) := hcast
  have hstep : ∑ q ∈ t, ((2 : ℚ) ^ (N - 1))⁻¹ * r q
      ≤ ∑ _q ∈ t, ((2 : ℚ) ^ (N - 1))⁻¹ * (1 / 1600) := by
    refine Finset.sum_le_sum (fun q hq => ?_)
    exact mul_le_mul_of_nonneg_left (hrb q hq) (le_of_lt hKpos)
  have hconst : ∑ _q ∈ t, ((2 : ℚ) ^ (N - 1))⁻¹ * (1 / 1600)
      = (t.card : ℚ) * (((2 : ℚ) ^ (N - 1))⁻¹ * (1 / 1600)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hmono : (t.card : ℚ) * (((2 : ℚ) ^ (N - 1))⁻¹ * (1 / 1600))
      ≤ (2 : ℚ) ^ (N - 1) * (((2 : ℚ) ^ (N - 1))⁻¹ * (1 / 1600)) := by
    refine mul_le_mul_of_nonneg_right hcard ?_
    positivity
  have hcollapse : (2 : ℚ) ^ (N - 1) * (((2 : ℚ) ^ (N - 1))⁻¹ * (1 / 1600)) = 1 / 1600 := by
    field_simp
  rw [hconst] at hstep
  linarith

end Qatlib.Papers.Counterfeit10.MainResults
