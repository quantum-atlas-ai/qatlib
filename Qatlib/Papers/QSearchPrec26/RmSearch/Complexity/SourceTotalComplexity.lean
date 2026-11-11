/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.Complexity.Total — Theorem 5: total complexity of Algorithm 2

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Theorem 5, Eq. (B31), p. 22.

Let `T_ε := min{k ≥ 0 : e_k = 1 - q_k ≤ ε}` be the first iteration at which the
success-probability error is at most `ε`.  For Algorithm 2 with the 5-factor retraction and
fixed parameters `0 < δ ≤ 1/2`, `0 < c ≤ 1/8`, `0 < ρ < 1`, and every `0 < ε < e⁻¹`,

`T_ε = O(√(N/M) + log log(1/ε))`   (Eq. (B31)).

The proof combines Proposition 3 (`K_enter = O(√(N/M))` iterations to enter the Newton
region) with Proposition 2: inside the region `e_{K+j+1} ≤ C_N e_{K+j}²`, so with
`a_j := C_N e_{K+j}` one has `a_{j+1} ≤ a_j²` and `a_0 ≤ 1/2`, whence
`a_j ≤ (1/2)^{2^j}` and `e_{K+j} ≤ ε` once `2^j ≳ log(1/ε)`, i.e. `j = O(log log(1/ε))`.

This file formalizes the double-logarithmic mechanism as the scalar lemma
`quadratic_iterate_bound` and states the total complexity bound (Eq. (B31)) faithfully.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Qatlib.Papers.QSearchPrec26.RmSearch.Complexity.Total

/-- The hitting time `T_ε = min{k ≥ 0 : e_k ≤ ε}` (paper p. 22), defined as the least `k`
with `e k ≤ ε`; the existence proof is supplied by convergence `e_k → 0`. -/
def hittingTime (e : ℕ → ℝ) (ε : ℝ) (h : ∃ k, e k ≤ ε) : ℕ := Nat.find h

/-- **Theorem 5, double-logarithmic iteration bound** (arXiv:2603.26039v3, proof of
Theorem 5, p. 22).  If `a_{j+1} ≤ a_j²`, `a_j ≥ 0` and `a_0 ≤ 1/2`, then
`a_j ≤ (1/2)^{2^j}`; this is the induction `a_{j+1} ≤ a_j²` that turns quadratic
convergence into the `log log(1/ε)` post-Newton iteration count. -/
theorem quadratic_iterate_bound (a : ℕ → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (hstart : a 0 ≤ 1 / 2) (hrec : ∀ j, a (j + 1) ≤ (a j) ^ 2) :
    ∀ j, a j ≤ (1 / 2 : ℝ) ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => simpa using hstart
  | succ j ih =>
    have h1 : a (j + 1) ≤ (a j) ^ 2 := hrec j
    have h2 : (a j) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ j)) ^ 2 :=
      pow_le_pow_left₀ (ha0 j) ih 2
    have h3 : ((1 / 2 : ℝ) ^ (2 ^ j)) ^ 2 = (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by
      rw [← pow_mul]
      congr 1
    linarith [h1, h2, h3.le, h3.ge]

/-- **Theorem 5, post-Newton phase** (arXiv:2603.26039v3, proof of Theorem 5, p. 22).
If the success-probability error decays quadratically from the entrance index `K` on,
`e_{K+j+1} ≤ e_{K+j}²` with `e_K ≤ 1/2`, then `e_{K+j} ≤ (1/2)^{2^j}` for every `j`; this
is the `log log(1/ε)` phase of the algorithm. -/
theorem quadratic_phase_iterates
    (e : ℕ → ℝ) (K : ℕ)
    (he0 : ∀ j, 0 ≤ e (K + j)) (heK : e K ≤ 1 / 2)
    (hquad : ∀ j, e (K + j + 1) ≤ (e (K + j)) ^ 2) :
    ∀ j, e (K + j) ≤ (1 / 2 : ℝ) ^ (2 ^ j) := by
  have h := quadratic_iterate_bound (fun j => e (K + j)) he0 heK (fun j => hquad j)
  exact h

/-- **Theorem 5** (arXiv:2603.26039v3, Theorem 5 / Eq. (B31), p. 22).  Let `e_k = 1 - q_k`
be the success-probability error of Algorithm 2 with the 5-factor retraction.  Suppose

* (entrance phase, Proposition 3) the Newton region is entered at index `K` with
  `K ≤ C₁ √(N/M)`;
* (Newton phase, Proposition 2) from `K` on the error decays quadratically,
  `e_{K+j+1} ≤ e_{K+j}²`, with `e_K ≤ 1/2`;
* (convergence, Proposition 1) `e` hits every positive level, giving the hitting time
  `T_ε = min{k : e_k ≤ ε}`.

Then there is `C > 0` such that, for every `0 < ε < e⁻¹`,
`T_ε ≤ C (√(N/M) + log log(1/ε))` (Eq. (B31)).

The proof takes the least `j` with `(1/2)^{2^j} ≤ ε`; the quadratic-phase bound gives
`e_{K+j} ≤ ε`, hence `T_ε ≤ K + j` by minimality of the hitting time.  Minimality of `j`
gives `2^{j-1} < log(1/ε)/log 2`, and `log 2 > 1/2` turns this into
`j ≤ 2 + 2 log log(1/ε)`.  Combining with the entrance bound `K ≤ C₁ √(N/M)` yields
Eq. (B31) with `C = max (C₁ + 2) 2`. -/
theorem theorem5_total_complexity
    (N M : ℕ) (hM : 0 < M) (hMN : M ≤ N)
    (δ c ρ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 8)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (e : ℕ → ℝ) (K : ℕ) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hK : (K : ℝ) ≤ C₁ * Real.sqrt ((N : ℝ) / M))
    (he0 : ∀ j, 0 ≤ e (K + j)) (heK : e K ≤ 1 / 2)
    (hquad : ∀ j, e (K + j + 1) ≤ (e (K + j)) ^ 2)
    (hHit : ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → ∃ k, e k ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)),
      (hittingTime e ε (hHit ε hε0 hε1) : ℝ)
        ≤ C * (Real.sqrt ((N : ℝ) / M) + Real.log (Real.log (1 / ε))) := by
  have hphase : ∀ j, e (K + j) ≤ (1 / 2 : ℝ) ^ (2 ^ j) :=
    quadratic_phase_iterates e K he0 heK hquad
  have hex : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ j : ℕ, (1 / 2 : ℝ) ^ (2 ^ j) ≤ ε := by
    intro ε hε0 hε1
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε0 (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, le_of_lt (lt_of_le_of_lt ?_ hn)⟩
    exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.le_of_lt Nat.lt_two_pow_self)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  refine ⟨max (C₁ + 2) 2, lt_max_of_lt_left (by linarith), ?_⟩
  intro ε hε0 hε1
  have hε1' : ε < 1 :=
    lt_trans hε1 (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
  have hL1 : 1 < Real.log (1 / ε) := by
    have hlogε : Real.log ε < -1 := by
      have h := Real.log_lt_log hε0 hε1
      rwa [Real.log_exp] at h
    rw [one_div, Real.log_inv]
    linarith
  have hLpos : 0 < Real.log (1 / ε) := by linarith
  have hlogLpos : 0 < Real.log (Real.log (1 / ε)) := Real.log_pos hL1
  let j := Nat.find (hex ε hε0 hε1')
  have hj : (j : ℝ) ≤ 2 + 2 * Real.log (Real.log (1 / ε)) := by
    by_cases hj0 : j = 0
    · rw [hj0]
      push_cast
      linarith [hlogLpos]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hnot : ¬ ((1 / 2 : ℝ) ^ (2 ^ (j - 1)) ≤ ε) :=
        Nat.find_min (hex ε hε0 hε1') (Nat.sub_one_lt hj0)
      have hlt : ε < (1 / 2 : ℝ) ^ (2 ^ (j - 1)) := lt_of_not_ge hnot
      have hloglt : Real.log ε < Real.log ((1 / 2 : ℝ) ^ (2 ^ (j - 1))) :=
        Real.log_lt_log hε0 hlt
      have hlogpow : Real.log ((1 / 2 : ℝ) ^ (2 ^ (j - 1)))
          = -(((2 : ℕ) ^ (j - 1) : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow, one_div, Real.log_inv]
        ring
      rw [hlogpow] at hloglt
      have hL : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
      have hpowlt : (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ) * Real.log 2
          < Real.log (1 / ε) := by
        rw [hL]
        linarith
      have hpowlt' : (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ) < Real.log (1 / ε) / Real.log 2 := by
        rw [lt_div_iff₀ hlog2pos]
        linarith
      have hquot : Real.log (1 / ε) / Real.log 2 < 2 * Real.log (1 / ε) := by
        rw [div_lt_iff₀ hlog2pos]
        nlinarith [hlog2, hLpos]
      have hmlt : (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ) < 2 * Real.log (1 / ε) :=
        lt_trans hpowlt' hquot
      have hlogmlt : Real.log ((((2 : ℕ) ^ (j - 1) : ℕ) : ℝ))
          < Real.log (2 * Real.log (1 / ε)) :=
        Real.log_lt_log (by positivity) hmlt
      have hlogm : Real.log ((((2 : ℕ) ^ (j - 1) : ℕ) : ℝ))
          = ((j - 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      have hlog2L : Real.log (2 * Real.log (1 / ε))
          = Real.log 2 + Real.log (Real.log (1 / ε)) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hLpos)]
      rw [hlogm, hlog2L] at hlogmlt
      have hdiv : ((j - 1 : ℕ) : ℝ) < 1 + Real.log (Real.log (1 / ε)) / Real.log 2 := by
        have hEq : 1 + Real.log (Real.log (1 / ε)) / Real.log 2
            = (Real.log 2 + Real.log (Real.log (1 / ε))) / Real.log 2 := by
          field_simp
        rw [hEq, lt_div_iff₀ hlog2pos]
        linarith [hlogmlt]
      have hinv : 1 / Real.log 2 ≤ 2 := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith [hlog2]
      have hmul : Real.log (Real.log (1 / ε)) / Real.log 2
          = (1 / Real.log 2) * Real.log (Real.log (1 / ε)) := by ring
      have hdiv2 : 1 + Real.log (Real.log (1 / ε)) / Real.log 2
          ≤ 1 + 2 * Real.log (Real.log (1 / ε)) := by
        rw [hmul]
        have := mul_le_mul_of_nonneg_right hinv (le_of_lt hlogLpos)
        linarith
      have hcast : ((j : ℕ) : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
        have h : j = (j - 1) + 1 := by omega
        rw [h]
        push_cast
        ring
      rw [hcast]
      linarith
  have hwit : e (K + j) ≤ ε := le_trans (hphase j) (Nat.find_spec (hex ε hε0 hε1'))
  have hT : hittingTime e ε (hHit ε hε0 hε1) ≤ K + j :=
    Nat.find_min' (hHit ε hε0 hε1) hwit
  have hT' : (hittingTime e ε (hHit ε hε0 hε1) : ℝ) ≤ (K : ℝ) + (j : ℝ) := by
    exact_mod_cast hT
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((N : ℝ) / M) := by
    have hsq : (1 : ℝ) ^ 2 ≤ (N : ℝ) / M := by
      rw [one_pow]
      exact (one_le_div (by exact_mod_cast hM)).mpr (by exact_mod_cast hMN)
    exact Real.le_sqrt_of_sq_le hsq
  have hstep : (K : ℝ) + (j : ℝ)
      ≤ C₁ * Real.sqrt ((N : ℝ) / M) + (2 + 2 * Real.log (Real.log (1 / ε))) :=
    add_le_add hK hj
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / M) := Real.sqrt_nonneg _
  have hmax1 : C₁ + 2 ≤ max (C₁ + 2) 2 := le_max_left _ _
  have hmax2 : (2 : ℝ) ≤ max (C₁ + 2) 2 := le_max_right _ _
  have hstep1 : C₁ * Real.sqrt ((N : ℝ) / M)
      ≤ max (C₁ + 2) 2 * Real.sqrt ((N : ℝ) / M) :=
    mul_le_mul_of_nonneg_right (le_trans (by linarith : C₁ ≤ C₁ + 2) hmax1) hs
  have hstep2 : (2 : ℝ) ≤ max (C₁ + 2) 2 * Real.sqrt ((N : ℝ) / M) := by
    calc (2 : ℝ) ≤ max (C₁ + 2) 2 := hmax2
      _ = max (C₁ + 2) 2 * 1 := by ring
      _ ≤ max (C₁ + 2) 2 * Real.sqrt ((N : ℝ) / M) := by gcongr
  have hstep3 : (2 : ℝ) * Real.log (Real.log (1 / ε))
      ≤ max (C₁ + 2) 2 * Real.log (Real.log (1 / ε)) :=
    mul_le_mul_of_nonneg_right hmax2 (le_of_lt hlogLpos)
  calc (hittingTime e ε (hHit ε hε0 hε1) : ℝ)
      ≤ (K : ℝ) + (j : ℝ) := hT'
    _ ≤ C₁ * Real.sqrt ((N : ℝ) / M) + (2 + 2 * Real.log (Real.log (1 / ε))) := hstep
    _ ≤ max (C₁ + 2) 2
          * (Real.sqrt ((N : ℝ) / M) + Real.log (Real.log (1 / ε))) := by
        have hsum := add_le_add hstep1 hstep3
        have htwo := hstep2
        nlinarith [hsum, htwo]

end Qatlib.Papers.QSearchPrec26.RmSearch.Complexity.Total
