/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.TermCountBound

set_option backward.isDefEq.respectTransparency false

/-!
# Lie-Algebraic Trotter-Suzuki Term Count for the Quantum Harmonic Oscillator

This module formalizes Eq. (15), the optimal-order exponential bound, and the
subpolynomial scaling in `m'` for simulating a single quantum harmonic oscillator
via Somma's Lie-algebraic Trotter-Suzuki product formula (`L = 3`, `β = 1`, `y = m'`).

## Main statements

* `qho_termCount_eq15`: Eq. (15) term-count bound for any Trotter-Suzuki order `p ≥ 1`.
* `qho_optimal_order`: subexponential term-count bound `O(t exp(2 √(log(m' t / ε) log 5))) + N_p` at `qhoOptimalOrder`.
* `qho_subpolynomial`: subpolynomiality `N / (m')^α → 0` as `m' → ∞` for every `α > 0`.

## References

* [Somma, 2016][Somma2016], Eq. (15), p. 4.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

private lemma optimal_order_factor_le {R : ℝ} (hR : 1 ≤ R) :
    let p := max 1 (Nat.ceil (Real.sqrt (Real.log R / Real.log 5) / 2))
    ((5 : ℝ) ^ (2 * p)) * R ^ (1 / (2 * (p : ℝ))) ≤
      25 * Real.exp (2 * Real.sqrt (Real.log R * Real.log 5)) := by
  let z := Real.log R
  let L5 := Real.log 5
  let x := Real.sqrt (z / L5) / 2
  let p := max 1 (Nat.ceil x)
  change (5 : ℝ) ^ (2 * p) * R ^ (1 / (2 * (p : ℝ))) ≤
    25 * Real.exp (2 * Real.sqrt (z * L5))
  have hz : 0 ≤ z := Real.log_nonneg hR
  have hL : 0 < L5 := Real.log_pos (by norm_num)
  have hx : 0 ≤ x := by positivity
  have hp : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_max_left 1 (Nat.ceil x))
  have hxp : x ≤ (p : ℝ) := (Nat.le_ceil x).trans (by
    exact_mod_cast (le_max_right 1 (Nat.ceil x)))
  have hpx : (p : ℝ) ≤ x + 1 := by
    by_cases hc : Nat.ceil x ≤ 1
    · have he : p = 1 := max_eq_left hc
      rw [he]
      norm_num
      exact hx
    · have he : p = Nat.ceil x := max_eq_right (by omega)
      rw [he]
      exact (Nat.ceil_lt_add_one hx).le
  have hs : Real.sqrt (z / L5) * L5 = Real.sqrt (z * L5) := by
    calc
      _ = Real.sqrt (z / L5) * Real.sqrt (L5 ^ 2) := by rw [Real.sqrt_sq hL.le]
      _ = Real.sqrt (z / L5 * L5 ^ 2) :=
        (Real.sqrt_mul (div_nonneg hz hL.le) _).symm
      _ = _ := by congr 1; field_simp
  have hzprod : z = Real.sqrt (z / L5) * Real.sqrt (z * L5) := by
    rw [← hs, ← mul_assoc, ← pow_two, Real.sq_sqrt (div_nonneg hz hL.le)]
    field_simp
  have hfirst : (2 * (p : ℝ)) * L5 ≤ Real.sqrt (z * L5) + 2 * L5 := by
    have h := mul_le_mul_of_nonneg_right hpx hL.le
    dsimp [x] at h
    nlinarith only [h, hs]
  have hsecond : z / (2 * (p : ℝ)) ≤ Real.sqrt (z * L5) := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (p : ℝ))).2
    have hsle : Real.sqrt (z / L5) ≤ 2 * (p : ℝ) := by
      dsimp [x] at hxp
      linarith
    calc
      z = Real.sqrt (z / L5) * Real.sqrt (z * L5) := hzprod
      _ ≤ (2 * (p : ℝ)) * Real.sqrt (z * L5) :=
        mul_le_mul_of_nonneg_right hsle (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hpow : (5 : ℝ) ^ (2 * p) = Real.exp ((2 * (p : ℝ)) * L5) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    dsimp [L5]
    ring
  have hRpow : R ^ (1 / (2 * (p : ℝ))) = Real.exp (z / (2 * (p : ℝ))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    dsimp [z]
    ring
  have h25 : Real.exp (2 * L5) = 25 := by
    rw [show 2 * L5 = L5 + L5 by ring, Real.exp_add, Real.exp_log (by norm_num)]
    norm_num
  rw [hpow, hRpow, ← Real.exp_add]
  calc
    _ ≤ Real.exp (2 * L5 + 2 * Real.sqrt (z * L5)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, h25]

private lemma qho_termCount_le {p : ℕ} (hp : 1 ≤ p) {m' t ε : ℝ}
    (hm' : 0 ≤ m') (ht : 0 ≤ t) (hε : 0 < ε) :
    sourceNumTerms p 3 1 m' t ε ≤
      540 * ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
        t ^ (1 + 1 / (2 * (p : ℝ)))) + sourceMacroCount 3 p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h3 : (3 : ℝ) ^ (2 + 1 / (p : ℝ)) ≤ 27 := by
    have he : 2 + 1 / (p : ℝ) ≤ 3 := by
      have := (div_le_one₀ (by linarith : (0 : ℝ) < (p : ℝ))).2 hp1
      linarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he
    have h3r : (3 : ℝ) ^ (3 : ℝ) = 27 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h3r] at h
    exact h
  have heq : eq5Bound p 3 1 m' t ε =
      ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
        t ^ (1 + 1 / (2 * (p : ℝ)))) * (3 : ℝ) ^ (2 + 1 / (p : ℝ)) := by
    unfold eq5Bound
    rw [Real.div_rpow hm' hε.le]
    ring
  have hA : 0 ≤ 20 * ((5 : ℝ) ^ (2 * p) *
      (m' / ε) ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ)))) := by
    exact mul_nonneg (by norm_num) (mul_nonneg
      (mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg hm' hε.le) _))
      (Real.rpow_nonneg ht _))
  have hbound := sourceNumTerms_le_eq5 hp (L := 3) (β := 1) (y := m')
    (by norm_num) (by norm_num) hm' ht hε
  rw [heq] at hbound
  nlinarith only [hbound, mul_le_mul_of_nonneg_left h3 hA]

/-- **Eq. (15) (arXiv:1512.03416v1, p. 4)**: for the QHO (`L = 3`, `β = 1`,
`y = m′`) and `p ≥ 1`, the number of terms is
`N ≤ 540 · 5^{2p} (m′/ε)^{1/(2p)} t^{1+1/(2p)} + N_p`, with explicit constant
`540 = 20 · 27` from `3^{2+1/p} ≤ 3³`. -/
theorem qho_termCount_eq15 {p : ℕ} (hp : 1 ≤ p) {m' t ε : ℝ}
    (hm' : 1 ≤ m') (ht : 0 ≤ t) (hε : 0 < ε) :
    sourceNumTerms p 3 1 m' t ε ≤
      540 * ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
        t ^ (1 + 1 / (2 * (p : ℝ)))) + sourceMacroCount 3 p := by
  exact qho_termCount_le hp (by linarith) ht hε

private lemma qho_optimal_order_bound {m' t ε : ℝ}
    (hm' : 0 < m') (ht : 0 ≤ t) (hε : 0 < ε) (hmt : 1 ≤ m' * t / ε) :
    sourceNumTerms (qhoOptimalOrder m' t ε) 3 1 m' t ε ≤
      13500 * (t * Real.exp (2 * Real.sqrt (Real.log (m' * t / ε) * Real.log 5))) +
        sourceMacroCount 3 (qhoOptimalOrder m' t ε) := by
  let p := qhoOptimalOrder m' t ε
  have hp : 1 ≤ p := le_max_left _ _
  have htpos : 0 < t := by
    have hprod := (le_div_iff₀ hε).1 hmt
    nlinarith
  have hsplit : (m' / ε) ^ (1 / (2 * (p : ℝ))) *
      t ^ (1 + 1 / (2 * (p : ℝ))) =
      t * (m' * t / ε) ^ (1 / (2 * (p : ℝ))) := by
    rw [Real.rpow_add htpos, Real.rpow_one,
      show m' * t / ε = m' / ε * t by ring,
      Real.mul_rpow (div_nonneg hm'.le hε.le) ht]
    ring
  have hfactor := optimal_order_factor_le hmt
  change (5 : ℝ) ^ (2 * p) * (m' * t / ε) ^ (1 / (2 * (p : ℝ))) ≤ _ at hfactor
  calc
    _ ≤ 540 * ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
        t ^ (1 + 1 / (2 * (p : ℝ)))) + sourceMacroCount 3 p :=
      qho_termCount_le hp hm'.le ht hε
    _ = (540 * t) * ((5 : ℝ) ^ (2 * p) *
        (m' * t / ε) ^ (1 / (2 * (p : ℝ)))) + sourceMacroCount 3 p := by
      rw [mul_assoc ((5 : ℝ) ^ (2 * p)), hsplit]
      ring
    _ ≤ (540 * t) * (25 * Real.exp
        (2 * Real.sqrt (Real.log (m' * t / ε) * Real.log 5))) + sourceMacroCount 3 p :=
      add_le_add (mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 540) ht)) le_rfl
    _ = _ := by ring

/-- **Optimal order for the QHO (arXiv:1512.03416v1, p. 4)**: choosing the
order `p` that minimises the Eq. (15) bound gives
`N ≤ C · t · exp(2√(log(m′t/ε)·log 5)) + N_p`. -/
theorem qho_optimal_order {m' t ε : ℝ} (hm' : 0 < m') (ht : 0 ≤ t) (hε : 0 < ε)
    (hmt : 1 ≤ m' * t / ε) :
    ∃ C : ℝ, 0 < C ∧
      sourceNumTerms (qhoOptimalOrder m' t ε) 3 1 m' t ε ≤
        C * (t * Real.exp (2 * Real.sqrt (Real.log (m' * t / ε) * Real.log 5))) +
          sourceMacroCount 3 (qhoOptimalOrder m' t ε) := by
  exact ⟨13500, by norm_num, qho_optimal_order_bound hm' ht hε hmt⟩

/-- **Subpolynomiality in `m′` (arXiv:1512.03416v1, p. 4)**: at the optimal order,
`N / (m′)^α → 0` as `m′ → ∞` for every `α > 0`. -/
theorem qho_subpolynomial {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto
      (fun m' : ℝ => sourceNumTerms (qhoOptimalOrder m' 1 1) 3 1 m' 1 1 / m' ^ α)
      Filter.atTop (nhds 0) := by
  let K := 13650 * Real.exp ((2 * Real.log 5) / α)
  have hdecay : Filter.Tendsto
      (fun m' : ℝ => K * Real.exp (-(α / 2) * Real.log m')) Filter.atTop (nhds 0) := by
    have hlog := Real.tendsto_log_atTop.const_mul_atTop_of_neg
      (by linarith : -(α / 2) < 0)
    simpa using (Real.tendsto_exp_atBot.comp hlog).const_mul K
  have hnonneg : ∀ᶠ m' : ℝ in Filter.atTop,
      0 ≤ sourceNumTerms (qhoOptimalOrder m' 1 1) 3 1 m' 1 1 / m' ^ α := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m' hm'
    unfold sourceNumTerms sourceMacroCount
    positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay hnonneg ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m' hm'
  have hmpos : 0 < m' := by linarith
  let p := qhoOptimalOrder m' 1 1
  have hp : 1 ≤ p := le_max_left _ _
  have hmain : sourceNumTerms p 3 1 m' 1 1 ≤
      13500 * Real.exp (2 * Real.sqrt (Real.log m' * Real.log 5)) +
        sourceMacroCount 3 p := by
    simpa [p] using qho_optimal_order_bound hmpos (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1) (by simpa using hm')
  have hfactor : (5 : ℝ) ^ (2 * p) * m' ^ (1 / (2 * (p : ℝ))) ≤
      25 * Real.exp (2 * Real.sqrt (Real.log m' * Real.log 5)) := by
    simpa [p, qhoOptimalOrder] using optimal_order_factor_le hm'
  have hpowers : (5 : ℝ) ^ (p - 1) ≤ (5 : ℝ) ^ (2 * p) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hmPow : 1 ≤ m' ^ (1 / (2 * (p : ℝ))) :=
    Real.one_le_rpow hm' (by positivity)
  have hmacro : sourceMacroCount 3 p ≤
      150 * Real.exp (2 * Real.sqrt (Real.log m' * Real.log 5)) := by
    have hpow : (5 : ℝ) ^ (2 * p) ≤
        (5 : ℝ) ^ (2 * p) * m' ^ (1 / (2 * (p : ℝ))) := by
      simpa using mul_le_mul_of_nonneg_left hmPow (by positivity : (0 : ℝ) ≤ 5 ^ (2 * p))
    unfold sourceMacroCount
    nlinarith only [hpowers.trans (hpow.trans hfactor)]
  have hnum : sourceNumTerms p 3 1 m' 1 1 ≤
      13650 * Real.exp (2 * Real.sqrt (Real.log m' * Real.log 5)) := by
    linarith
  let u := Real.log m'
  have hu : 0 ≤ u := Real.log_nonneg hm'
  have hL : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hA : 0 ≤ (α / 2) * u := mul_nonneg (by positivity) hu
  have hB : 0 ≤ (2 * Real.log 5) / α := by positivity
  have hcross : Real.sqrt ((α / 2) * u) * Real.sqrt ((2 * Real.log 5) / α) =
      Real.sqrt (u * Real.log 5) := by
    rw [← Real.sqrt_mul hA]
    congr 1
    field_simp
  have hexponent : 2 * Real.sqrt (u * Real.log 5) ≤
      (2 * Real.log 5) / α + (α / 2) * u := by
    nlinarith only [sq_nonneg (Real.sqrt ((α / 2) * u) -
      Real.sqrt ((2 * Real.log 5) / α)), Real.sq_sqrt hA, Real.sq_sqrt hB, hcross]
  have hexp := Real.exp_le_exp.mpr hexponent
  have hden : 0 ≤ m' ^ α := (Real.rpow_pos_of_pos hmpos _).le
  calc
    _ ≤ (13650 * Real.exp (2 * Real.sqrt (Real.log m' * Real.log 5))) / m' ^ α :=
      div_le_div_of_nonneg_right hnum hden
    _ ≤ (13650 * Real.exp ((2 * Real.log 5) / α + (α / 2) * u)) / m' ^ α :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hden
    _ = K * Real.exp (-(α / 2) * Real.log m') := by
      rw [Real.rpow_def_of_pos hmpos, mul_div_assoc, ← Real.exp_sub]
      rw [show (2 * Real.log 5) / α + (α / 2) * u - Real.log m' * α =
        (2 * Real.log 5) / α + (-(α / 2) * Real.log m') by dsimp [u]; ring,
        Real.exp_add]
      dsimp [K]
      ring

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount
