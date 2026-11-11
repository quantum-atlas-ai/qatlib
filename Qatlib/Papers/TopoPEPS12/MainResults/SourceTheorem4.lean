/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option backward.isDefEq.respectTransparency false

/-!
# SourceTheorem4 — polynomial-time preparation of G-injective PEPS

Schwarz--Cubitt--Temme--Verstraete--Pérez-García,
*Preparing topological PEPS on a quantum computer*, fixed arXiv:1211.4050v1 (16 Nov 2012),
PRA 88, 032321 (2013). Source location: Theorem 4 (Runtime), p. 4, right column; proof p. 5,
left column, Eq. (11).

Theorem 4 (paper). A state in the subspace spanned by the `G`-injective PEPS
`|A^1 ... A^N; K>` can be prepared with probability `1 - ε` in time
`O(N^4 κ_G^2 Δ^{-1} ε^{-1})`, with additional classical processing `O(N d^6)`, where
`Δ = min_t Δ_t` is the minimal spectral gap of the parent Hamiltonians and
`κ_G = max_t κ(A^t|_{S_G})`.

Formalisation boundary. The device-level quantum circuit (phase estimation for each parent
Hamiltonian, Hamiltonian simulation) is not rebuilt; its per-procedure cost is the paper's
`O(N^2/Δ)` count. What is formalised is the numerical composition that carries the proof
(Section "Runtime", p. 5): Lemma 3 bounds each step's failure probability `p ≤ 1/(2 m d_min)`
(Eq. (11)); Lemma 2 gives `d_min ≥ κ_G^{-2}`; choosing `m = ⌈N κ_G^2/(2ε)⌉` repetitions per step
gives total failure `≤ N p ≤ ε` over the `N` steps, and the total cost is
`N · m` phase estimations times `N^2/Δ`, i.e. at most `N^4 κ_G^2/(Δ ε)`. The hypothesis interval
`N κ_G^2/(2ε) ≤ m ≤ N κ_G^2/ε` is exactly the range of the algorithm's chosen count
(`⌈x⌉ ≤ 2x` for `x ≥ 1`); it is not an extra physical assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoPEPS12.MainResults

/-- Paper Theorem 4: the additional classical processing is `O(N d^6)`; here the exact
polynomial `N · d^6` (p. 4, Theorem 4; the paper attributes the bookkeeping to Ref. [5]). -/
def classicalProcessingCost (N : ℕ) (d : ℝ) : ℝ := (N : ℝ) * d ^ 6

/-- Paper Theorem 4, proof Eq. (11) (p. 5): with each of the `N` steps failing with probability
`p ≤ 1/(2 m d_min)` and `d_min ≥ κ_G^{-2}`, choosing `m ≥ N κ_G^2/(2ε)` repetitions per step makes
the total success probability `(1-p)^N` at least `1-ε`. -/
theorem theorem4_success_probability
    (N m : ℕ) (p κ dmin ε : ℝ)
    (hN : 1 ≤ N) (hm : 1 ≤ m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp3 : p ≤ 1 / (2 * (m : ℝ) * dmin))
    (hκ : 1 ≤ κ) (hdminpos : 0 < dmin) (hκ2 : (κ ^ 2)⁻¹ ≤ dmin)
    (hε : 0 < ε)
    (hmlo : (N : ℝ) * κ ^ 2 / (2 * ε) ≤ (m : ℝ)) :
    1 - ε ≤ (1 - p) ^ N := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hκ2pos : (0 : ℝ) < κ ^ 2 := by positivity
  -- `1 ≤ dmin * κ²`, hence `1/dmin ≤ κ²`
  have h1 : 1 ≤ dmin * κ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hκ2 hκ2pos.le
    rwa [inv_mul_cancel₀ hκ2pos.ne'] at hmul
  have hdmininv : dmin⁻¹ ≤ κ ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hdminpos]
    nlinarith [h1]
  -- `N · p ≤ ε`
  have hNp : (N : ℝ) * p ≤ ε := by
    have hstep : (N : ℝ) * p ≤ (N : ℝ) * (1 / (2 * (m : ℝ) * dmin)) :=
      mul_le_mul_of_nonneg_left hp3 (le_of_lt hNpos)
    have hstep2 : (N : ℝ) * (1 / (2 * (m : ℝ) * dmin)) ≤ ε := by
      have hrewrite : (N : ℝ) * (1 / (2 * (m : ℝ) * dmin))
          = (N : ℝ) / (2 * (m : ℝ) * dmin) := by ring
      rw [hrewrite, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) * dmin)]
      have hkey : (N : ℝ) * κ ^ 2 ≤ 2 * ε * (m : ℝ) := by
        have h2e : (0 : ℝ) < 2 * ε := by positivity
        have h := mul_le_mul_of_nonneg_right hmlo h2e.le
        rw [div_mul_cancel₀ _ (ne_of_gt h2e)] at h
        nlinarith [h]
      have hNle : (N : ℝ) ≤ 2 * ε * (m : ℝ) / κ ^ 2 := by
        rw [le_div_iff₀ hκ2pos]
        nlinarith [hkey]
      have hmono : 2 * ε * (m : ℝ) / κ ^ 2 ≤ 2 * ε * (m : ℝ) * dmin := by
        rw [div_le_iff₀ hκ2pos]
        have hpos : (0 : ℝ) ≤ 2 * ε * (m : ℝ) := by positivity
        have hsplit := mul_le_mul_of_nonneg_left h1 hpos
        nlinarith [hsplit]
      nlinarith [hNle, hmono]
    linarith [hstep, hstep2]
  -- Bernoulli: `1 - N p ≤ (1-p)^N`
  have hBern : 1 - (N : ℝ) * p ≤ (1 - p) ^ N := by
    have h := one_add_mul_le_pow (a := -p) (by linarith [hp1]) N
    have hcast : ((N : ℝ) : ℝ) = (N : ℝ) := rfl
    rw [hcast] at h
    simpa [mul_neg, sub_eq_add_neg] using h
  linarith [hNp, hBern]

/-- Paper Theorem 4: total runtime. `N` steps each perform `m` phase-estimation procedures of
cost `N^2/Δ`; with `m ≤ N κ_G^2/ε` the total is at most `N^4 κ_G^2/(Δ ε)`. -/
theorem theorem4_runtime_bound
    (N m : ℕ) (κ Δ ε : ℝ)
    (hκ : 1 ≤ κ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hmhi : (m : ℝ) ≤ (N : ℝ) * κ ^ 2 / ε) :
    (N : ℝ) * (m : ℝ) * ((N : ℝ) ^ 2 / Δ) ≤ (N : ℝ) ^ 4 * κ ^ 2 / (Δ * ε) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hstep : (N : ℝ) * (m : ℝ) * ((N : ℝ) ^ 2 / Δ)
      ≤ (N : ℝ) * ((N : ℝ) * κ ^ 2 / ε) * ((N : ℝ) ^ 2 / Δ) := by
    have h1 : (N : ℝ) * (m : ℝ) ≤ (N : ℝ) * ((N : ℝ) * κ ^ 2 / ε) :=
      mul_le_mul_of_nonneg_left hmhi hN0
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have heq : (N : ℝ) * ((N : ℝ) * κ ^ 2 / ε) * ((N : ℝ) ^ 2 / Δ)
      = (N : ℝ) ^ 4 * κ ^ 2 / (Δ * ε) := by
    field_simp
  rwa [heq] at hstep

/-- **Paper Theorem 4 (Runtime)**, p. 4, right column, with proof composition p. 5, Eq. (11).
For `N ≥ 1` steps, per-step failure `p ≤ 1/(2 m d_min)`, `d_min ≥ κ_G^{-2}`, `m` repetitions with
`N κ_G^2/(2ε) ≤ m ≤ N κ_G^2/ε`, the algorithm succeeds with probability at least `1-ε` and its
total runtime is at most `N^4 κ_G^2/(Δ ε)`; the classical bookkeeping is the polynomial
`classicalProcessingCost N d = N d^6`. -/
theorem theorem4_runtime
    (N m : ℕ) (p κ dmin Δ ε d : ℝ)
    (hN : 1 ≤ N) (hm : 1 ≤ m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : p ≤ 1 / (2 * (m : ℝ) * dmin))
    (hκ : 1 ≤ κ) (hdminpos : 0 < dmin) (hκ2 : (κ ^ 2)⁻¹ ≤ dmin)
    (hΔ : 0 < Δ) (hε : 0 < ε)
    (hmlo : (N : ℝ) * κ ^ 2 / (2 * ε) ≤ (m : ℝ))
    (hmhi : (m : ℝ) ≤ (N : ℝ) * κ ^ 2 / ε) :
    (1 - ε ≤ (1 - p) ^ N) ∧
    ((N : ℝ) * (m : ℝ) * ((N : ℝ) ^ 2 / Δ) ≤ (N : ℝ) ^ 4 * κ ^ 2 / (Δ * ε)) ∧
    (classicalProcessingCost N d = (N : ℝ) * d ^ 6) :=
  ⟨theorem4_success_probability N m p κ dmin ε hN hm hp0 hp1 hp3 hκ hdminpos hκ2 hε hmlo,
   theorem4_runtime_bound N m κ Δ ε hκ hΔ hε hmhi,
   rfl⟩

end Qatlib.Papers.TopoPEPS12.MainResults
