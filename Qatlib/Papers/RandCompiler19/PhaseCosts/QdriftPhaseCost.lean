/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Phase-estimation gate count of controlled qDRIFT (source Appendix E.2)

Fixed source: E. Campbell, *A random compiler for fast Hamiltonian simulation*,
arXiv:1811.08017v2 (PDF SHA256 `291fcf6f1c4fb2c487026c6c124a936a03fdc48b85d3ff9738b48a786f891b9f`),
Appendix E, Eqs. `(E4)`–`(E14)`.

The source turns the qDRIFT step budget into a phase-estimation gate count in five
steps, each of which is formalised here.

* `E4` — the total failure probability is `P_f = p_f + 2ε_tot`, with `p_f` the
  single-run failure probability and `ε_tot` the summed Trotter error.
* `E5` — query `j` needs `N(j) = 2·2λ_A²t_j²/ε_j = (2^jπ)²/ε_j` controlled
  exponentials; `λ_A = 1/2` is the strength of the renormalised
  `A = (H/λ+1)/2`, `t_j = π2^j` the query time, and the leading `2` is Fig. 3's
  double rotation.
* `E6` — the error shares minimising `Σ_j N(j)` subject to `Σ_j ε_j = ε_tot` are
  proportional to `2^j`, namely `ε_j = ε_tot·2^j/(2(2^m−1))`.
* `E8`/`E11` — at that allocation `N = 4π²(2^m−1)²/ε_tot`, and with the depth
  `2^m = λ(1+p_f)/(2δ_E p_f)` of `E9`/`E10` this is at most `π²λ²/δ_E²·X²` for
  the bracket `X` of `E12`.
* `E13`/`E14` — `X² = 2(1+p_f)²/(p_f²(P_f−p_f))`; at the source's small-`P_f`
  failure fraction `p_f = (2/3)P_f` this is `27(1+2P_f/3)²/(2P_f³)`, so the
  protocol needs at most

      N ≤ (27π²/2)·(1+2P_f/3)²·λ²/(δ_E²P_f³),      27π²/2 = 133.24… .

The last display keeps the `(1+p_f)²` factor of `E11`/`E13`: the source's printed
`X² ≤ 27/(2P_f³)` is the `P_f → 0` form of `E14`, not an identity.  The `133` of
the source's Table I entry is `27π²/2` rounded to three significant figures
(`qdriftPeConstant_three_sigfigs`), and the exact stationary point of the scalar
bracket is `4P_f/(√(9+8P_f)+3)`, whose first-order expansion is the source's
`2P_f/3` (`peExactFailureFraction_spec`, `two_thirds_sub_peExactFailureFraction_le`).
-/

namespace Qatlib.Papers.RandCompiler19.PhaseCosts.QdriftPhaseCost

set_option autoImplicit false

open Finset

/-! ## `E5`: the per-query gate count -/

/-- Source `E5`: the number of controlled exponentials of phase-estimation query
`j` that pays the error share `eps`.  The renormalised strength is `λ_A = 1/2`
and the query time is `t_j = π2^j`, so the count `2·2λ_A²t_j²/ε_j` collapses to
`(2^jπ)²/ε_j`, with the source's Fig. 3 factor already collected. -/
noncomputable def peQueryGates (j : ℕ) (eps : ℝ) : ℝ := ((2 : ℝ) ^ j * Real.pi) ^ 2 / eps

/-- Source `E5` in its stated form `2·2λ_A²t_j²/ε_j` with `λ_A = 1/2` and
`t_j = π2^j`. -/
theorem peQueryGates_eq_source (j : ℕ) (eps : ℝ) :
    peQueryGates j eps =
      2 * (2 * (1 / 2 : ℝ) ^ 2 * (Real.pi * (2 : ℝ) ^ j) ^ 2 / eps) := by
  unfold peQueryGates
  ring

/-! ## `E6`: the proportional error shares -/

/-- Source `E6`, reindexed from the source's `j ∈ {1,…,m}` onto `k ∈ {0,…,m−1}`:
the `k`-th query is the source's query `j = k+1`, whose share is
`ε_tot·2^{k+1}/(2(2^m−1))`. -/
noncomputable def peShare (m : ℕ) (epsTotal : ℝ) (k : ℕ) : ℝ :=
  epsTotal * (2 : ℝ) ^ (k + 1) / (2 * ((2 : ℝ) ^ m - 1))

/-- The geometric sum of powers of two. -/
theorem sum_range_pow_two (m : ℕ) : ∑ k ∈ range m, (2 : ℝ) ^ k = (2 : ℝ) ^ m - 1 := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- The shifted geometric sum `Σ_{k<m} 2^{k+1} = 2(2^m−1)` of the source's
query times. -/
theorem sum_range_pow_two_succ (m : ℕ) :
    ∑ k ∈ range m, (2 : ℝ) ^ (k + 1) = 2 * ((2 : ℝ) ^ m - 1) := by
  have h : ∀ k : ℕ, (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := fun k => by
    rw [pow_succ]; ring
  simp only [h]
  rw [← mul_sum, sum_range_pow_two]

/-- For `m ≥ 1` the depth scale `2^m` exceeds one. -/
theorem one_lt_pow_two {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) < (2 : ℝ) ^ m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]
  have hn1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hn : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  nlinarith

/-- The source's normalising factor `2(2^m−1)` is positive for `m ≥ 1`. -/
theorem two_mul_pow_sub_one_pos {m : ℕ} (hm : 1 ≤ m) : (0 : ℝ) < 2 * ((2 : ℝ) ^ m - 1) := by
  have := one_lt_pow_two hm
  linarith

/-- Source `E6` supplies a genuine allocation: the proportional shares sum to
the total Trotter budget `ε_tot`. -/
theorem peShare_sum {m : ℕ} (hm : 1 ≤ m) (epsTotal : ℝ) :
    ∑ k ∈ range m, peShare m epsTotal k = epsTotal := by
  have hden : (0 : ℝ) < 2 * ((2 : ℝ) ^ m - 1) := two_mul_pow_sub_one_pos hm
  unfold peShare
  rw [← sum_div, ← mul_sum, sum_range_pow_two_succ]
  exact mul_div_cancel_right₀ epsTotal (ne_of_gt hden)

/-- Every proportional share is positive at a positive budget. -/
theorem peShare_pos {m : ℕ} (hm : 1 ≤ m) {epsTotal : ℝ} (hE : 0 < epsTotal) (k : ℕ) :
    0 < peShare m epsTotal k := by
  have hden : (0 : ℝ) < 2 * ((2 : ℝ) ^ m - 1) := two_mul_pow_sub_one_pos hm
  unfold peShare
  exact div_pos (mul_pos hE (pow_pos (by norm_num) _)) hden

/-! ## `E8`: the count at the proportional allocation -/

/-- Source `E8`: at the proportional allocation the total gate count of the
whole chain is `4π²(2^m−1)²/ε_tot`. -/
theorem peChainGates_at_share {m : ℕ} (hm : 1 ≤ m) {epsTotal : ℝ} (hE : 0 < epsTotal) :
    ∑ k ∈ range m, peQueryGates (k + 1) (peShare m epsTotal k) =
      4 * Real.pi ^ 2 * ((2 : ℝ) ^ m - 1) ^ 2 / epsTotal := by
  have hden : (0 : ℝ) < 2 * ((2 : ℝ) ^ m - 1) := two_mul_pow_sub_one_pos hm
  have hterm : ∀ k : ℕ,
      peQueryGates (k + 1) (peShare m epsTotal k) =
        (2 * Real.pi ^ 2 * ((2 : ℝ) ^ m - 1)) * (2 : ℝ) ^ (k + 1) / epsTotal := by
    intro k
    have hp : (2 : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hden' : (2 * ((2 : ℝ) ^ m - 1)) ≠ 0 := ne_of_gt hden
    have hE' : epsTotal ≠ 0 := ne_of_gt hE
    unfold peQueryGates peShare
    field_simp
  rw [sum_congr rfl fun k _ => hterm k, ← sum_div, ← mul_sum, sum_range_pow_two_succ]
  have hden : (2 * ((2 : ℝ) ^ m - 1)) ≠ 0 := ne_of_gt (two_mul_pow_sub_one_pos hm)
  have hE' : epsTotal ≠ 0 := ne_of_gt hE
  field_simp
  ring

/-! ## `E6` optimality: no allocation beats the proportional one -/

/-- Source `E6` is optimal: for every positive allocation `eps` of the same
total Trotter error, the summed per-query count is at least the proportional
allocation's `4π²(2^m−1)²/ε_tot`.  The proof is Cauchy–Schwarz applied to
`c_k/√ε_k` and `√ε_k`. -/
theorem peChainGates_le_of_allocation {m : ℕ} (hm : 1 ≤ m) {epsTotal : ℝ}
    (eps : ℕ → ℝ) (hpos : ∀ k ∈ range m, 0 < eps k)
    (hsum : ∑ k ∈ range m, eps k = epsTotal) :
    4 * Real.pi ^ 2 * ((2 : ℝ) ^ m - 1) ^ 2 / epsTotal ≤
      ∑ k ∈ range m, peQueryGates (k + 1) (eps k) := by
  have hE : 0 < epsTotal := by
    rw [← hsum]
    refine sum_pos (fun k hk => hpos k hk) ?_
    exact ⟨0, mem_range.2 (by omega)⟩
  set c : ℕ → ℝ := fun k => Real.pi * (2 : ℝ) ^ (k + 1) with hc
  have hcs := sum_mul_sq_le_sq_mul_sq (range m)
    (fun k => c k / Real.sqrt (eps k)) (fun k => Real.sqrt (eps k))
  have hleft : ∑ k ∈ range m, c k / Real.sqrt (eps k) * Real.sqrt (eps k)
      = ∑ k ∈ range m, c k := by
    refine sum_congr rfl fun k hk => ?_
    have hkpos : 0 < eps k := hpos k hk
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 hkpos))]
  have hf : ∑ k ∈ range m, (c k / Real.sqrt (eps k)) ^ 2
      = ∑ k ∈ range m, c k ^ 2 / eps k := by
    refine sum_congr rfl fun k hk => ?_
    have hkpos : 0 < eps k := hpos k hk
    rw [div_pow, Real.sq_sqrt hkpos.le]
  have hg : ∑ k ∈ range m, (Real.sqrt (eps k)) ^ 2 = ∑ k ∈ range m, eps k := by
    refine sum_congr rfl fun k hk => ?_
    exact Real.sq_sqrt (hpos k hk).le
  rw [hleft, hf, hg, hsum] at hcs
  have hcsum : ∑ k ∈ range m, c k = Real.pi * (2 * ((2 : ℝ) ^ m - 1)) := by
    simp only [hc]
    rw [← mul_sum, sum_range_pow_two_succ]
  have hdiv : (∑ k ∈ range m, c k) ^ 2 / epsTotal ≤ ∑ k ∈ range m, c k ^ 2 / eps k := by
    rw [div_le_iff₀ hE]
    exact hcs
  have hnum : (∑ k ∈ range m, c k) ^ 2 / epsTotal
      = 4 * Real.pi ^ 2 * ((2 : ℝ) ^ m - 1) ^ 2 / epsTotal := by
    rw [hcsum]
    field_simp
    ring
  have hrhs : ∑ k ∈ range m, c k ^ 2 / eps k
      = ∑ k ∈ range m, peQueryGates (k + 1) (eps k) := by
    refine sum_congr rfl fun k _ => ?_
    simp only [hc, peQueryGates]
    ring
  rw [hnum, hrhs] at hdiv
  exact hdiv

/-! ## `E9`/`E10`: the depth scale in terms of `λ`, `δ_E` and `p_f` -/

/-- Source `E9`/`E10`: the depth scale `2^m = λ(1+p_f)/(2δ_E p_f)`. -/
noncomputable def pePowerScale (lam deltaE pf : ℝ) : ℝ := lam * (1 + pf) / (2 * deltaE * pf)

/-- Source `E9`/`E10` from the source's own depth `m = n + log₂(1/(2p_f)+1/2)`
with `n = log₂(δ⁻¹) − 1` and the renormalisation `δ_E = 2λδ`: the closed form
`2^m = (δ⁻¹/2)·(1/(2p_f)+1/2)` is exactly `λ(1+p_f)/(2δ_E p_f)`. -/
theorem pePowerScale_eq_of_depth {m : ℕ} {deltaE pf lam : ℝ}
    (hlam : lam ≠ 0) (hpf : pf ≠ 0) (hdelta : deltaE ≠ 0)
    (hpow : (2 : ℝ) ^ m = 1 / (2 * (deltaE / (2 * lam))) * (1 / (2 * pf) + 1 / 2)) :
    (2 : ℝ) ^ m = pePowerScale lam deltaE pf := by
  have hL : (1 : ℝ) / (2 * (deltaE / (2 * lam))) = lam / deltaE := by
    field_simp
  have hR : (1 : ℝ) / (2 * pf) + 1 / 2 = (1 + pf) / (2 * pf) := by
    field_simp
  rw [hL, hR] at hpow
  rw [hpow]
  unfold pePowerScale
  field_simp

/-! ## `E11`/`E12`: the bracket `X` -/

/-- Source `E12`: the bracket `X = (1+p_f)/(p_f√ε_tot)`. -/
noncomputable def peX (pf epsTotal : ℝ) : ℝ := (1 + pf) / (pf * Real.sqrt epsTotal)

/-- The square of the `E12` bracket in rational form. -/
theorem peX_sq {pf epsTotal : ℝ} (hpf : 0 < pf) (hE : 0 < epsTotal) :
    peX pf epsTotal ^ 2 = (1 + pf) ^ 2 / (pf ^ 2 * epsTotal) := by
  unfold peX
  have hs : Real.sqrt epsTotal ^ 2 = epsTotal := Real.sq_sqrt hE.le
  have hsp : Real.sqrt epsTotal ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hE)
  have hpf' : pf ≠ 0 := ne_of_gt hpf
  have hE' : epsTotal ≠ 0 := ne_of_gt hE
  field_simp
  nlinarith [hs]

/-- Source `E11`: with the closed-form depth of `E10` and `(2^m−1)² ≤ (2^m)²`,
the summed count is at most `π²λ²/δ_E²·X²`. -/
theorem peChainGates_le_X_sq {m : ℕ} (hm : 1 ≤ m) {lam deltaE pf epsTotal : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < deltaE) (hpf : 0 < pf) (hE : 0 < epsTotal)
    (hpow : (2 : ℝ) ^ m = pePowerScale lam deltaE pf) :
    4 * Real.pi ^ 2 * ((2 : ℝ) ^ m - 1) ^ 2 / epsTotal ≤
      Real.pi ^ 2 * lam ^ 2 / deltaE ^ 2 * peX pf epsTotal ^ 2 := by
  have hscale : (1 : ℝ) < (2 : ℝ) ^ m := one_lt_pow_two hm
  have hsq : ((2 : ℝ) ^ m - 1) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by nlinarith
  have hstep : 4 * Real.pi ^ 2 * ((2 : ℝ) ^ m - 1) ^ 2 / epsTotal
      ≤ 4 * Real.pi ^ 2 * ((2 : ℝ) ^ m) ^ 2 / epsTotal := by
    refine div_le_div_of_nonneg_right ?_ hE.le
    have hp2 : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
    nlinarith
  refine hstep.trans (le_of_eq ?_)
  rw [peX_sq hpf hE, hpow]
  unfold pePowerScale
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hdelta' : deltaE ≠ 0 := ne_of_gt hdelta
  have hpf' : pf ≠ 0 := ne_of_gt hpf
  field_simp
  ring

/-! ## `E13`: the bracket in terms of `P_f` -/

/-- Source `E13`: with `ε_tot = (P_f−p_f)/2` (`E4`), the bracket squares to
`2(1+p_f)²/(p_f²(P_f−p_f))`. -/
theorem peX_sq_eq_E13 {pf Pf epsTotal : ℝ} (hpf : 0 < pf) (hlt : pf < Pf)
    (hbudget : epsTotal = (Pf - pf) / 2) :
    peX pf epsTotal ^ 2 = 2 * (1 + pf) ^ 2 / (pf ^ 2 * (Pf - pf)) := by
  have hpos : 0 < Pf - pf := by linarith
  have hE : 0 < epsTotal := by rw [hbudget]; linarith
  rw [peX_sq hpf hE, hbudget]
  field_simp

/-- Source `E14`, exact form: at the source's failure fraction `p_f = (2/3)P_f`
and budget `ε_tot = P_f/6` the bracket contributes `27(1+2P_f/3)²/(2P_f³)`. -/
theorem peX_sq_at_two_thirds {Pf : ℝ} (hPf : 0 < Pf) :
    peX (2 * Pf / 3) (Pf / 6) ^ 2 = 27 * (1 + 2 * Pf / 3) ^ 2 / (2 * Pf ^ 3) := by
  have hpf : (0 : ℝ) < 2 * Pf / 3 := by linarith
  have hE : (0 : ℝ) < Pf / 6 := by linarith
  rw [peX_sq hpf hE]
  field_simp
  ring

/-! ## `E14`: the phase-estimation gate bound -/

/-- **Source `(E14)`.**  At the source's error allocation (`E6`) and its
small-`P_f` failure fraction `p_f = (2/3)P_f`, with the total budget
`ε_tot = P_f/6` of `E4` and the depth `2^m = λ(1+p_f)/(2δ_E p_f)` of `E9`/`E10`,
the controlled-qDRIFT phase-estimation protocol needs at most

`(27π²/2)·(1+2P_f/3)²·λ²/(δ_E²P_f³)`

controlled `exp(iH_j'τ)` exponentials, where `27π²/2 = 133.24…`.  The bound keeps
the `(1+p_f)²` factor of `E11`; the source's printed `X² ≤ 27/(2P_f³)` is its
`P_f → 0` form (`qdriftPeConstant_three_sigfigs`, `qdriftPe_one_percent`). -/
theorem qdriftPhaseEstimation_gateBound {m : ℕ} {lam deltaE Pf : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < deltaE) (hPf : 0 < Pf) (hm : 1 ≤ m)
    (hpow : (2 : ℝ) ^ m = pePowerScale lam deltaE (2 * Pf / 3)) :
    ∑ k ∈ range m, peQueryGates (k + 1) (peShare m (Pf / 6) k) ≤
      (27 * Real.pi ^ 2 / 2) * (1 + 2 * Pf / 3) ^ 2 * lam ^ 2 / (deltaE ^ 2 * Pf ^ 3) := by
  have hE : (0 : ℝ) < Pf / 6 := by linarith
  have hpf : (0 : ℝ) < 2 * Pf / 3 := by linarith
  refine (le_of_eq (peChainGates_at_share hm hE)).trans ?_
  refine (peChainGates_le_X_sq hm hlam hdelta hpf hE hpow).trans (le_of_eq ?_)
  rw [peX_sq_at_two_thirds hPf]
  have hdelta' : deltaE ≠ 0 := ne_of_gt hdelta
  have hPf' : Pf ≠ 0 := ne_of_gt hPf
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  field_simp

/-! ## The `133` of the source's table -/

/-- The exact coefficient `27π²/2 = 133.24…` of `E14` lies strictly between
`133` and `134`, so the source's `133` is its three-significant-figure value. -/
theorem qdriftPeConstant_three_sigfigs :
    (133 : ℝ) < 27 * Real.pi ^ 2 / 2 ∧ 27 * Real.pi ^ 2 / 2 < 134 := by
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  constructor
  · nlinarith [sq_nonneg (Real.pi - 3.141592)]
  · nlinarith [sq_nonneg (Real.pi - 3.141593)]

/-- The source's printed `X² ≤ 27/(2P_f³)` drops the `(1+p_f)²` numerator of
`E11`: already at `P_f = 1/100` the exact coefficient of `E14` is
`(27π²/2)(1+2/300)² > 133`, so `133` is not a bound at moderate `P_f`. -/
theorem qdriftPe_one_percent :
    (133 : ℝ) < (27 * Real.pi ^ 2 / 2) * (1 + 2 * (1 / 100) / 3) ^ 2 := by
  have hlo := Real.pi_gt_d6
  nlinarith [sq_nonneg (Real.pi - 3.141592)]

/-! ## The exact stationary failure fraction behind `2P_f/3` -/

/-- The exact stationary point of the scalar bracket of `E13`,
`4P_f/(√(9+8P_f)+3)`, whose first-order expansion in `P_f` is the source's
`(2/3)P_f`. -/
noncomputable def peExactFailureFraction (Pf : ℝ) : ℝ :=
  4 * Pf / (Real.sqrt (9 + 8 * Pf) + 3)

/-- The exact stationary fraction solves `p² + 3p = 2P_f`, the stationarity
condition of `2(1+p)²/(p²(P_f−p))`. -/
theorem peExactFailureFraction_spec {Pf : ℝ} (hPf : 0 < Pf) :
    peExactFailureFraction Pf ^ 2 + 3 * peExactFailureFraction Pf = 2 * Pf := by
  set s : ℝ := Real.sqrt (9 + 8 * Pf) + 3 with hsdef
  have hs0 : Real.sqrt (9 + 8 * Pf) ^ 2 = 9 + 8 * Pf := Real.sq_sqrt (by linarith)
  have hs : s ^ 2 = 8 * Pf + 6 * s := by
    rw [hsdef]
    nlinarith [hs0]
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hL : peExactFailureFraction Pf ^ 2 + 3 * peExactFailureFraction Pf
      = (16 * Pf ^ 2 + 12 * Pf * s) / s ^ 2 := by
    unfold peExactFailureFraction
    rw [← hsdef]
    field_simp
    ring
  rw [hL, div_eq_iff (pow_ne_zero 2 hsne)]
  nlinarith [hs]

/-- `3 ≤ √(9+8P_f)` for positive `P_f`, the bound behind the two comparisons of
the source's `(2/3)P_f` with the exact stationary fraction. -/
theorem three_le_sqrt_nine_add_eight {Pf : ℝ} (hPf : 0 < Pf) :
    (3 : ℝ) ≤ Real.sqrt (9 + 8 * Pf) := by
  have h9 : (3 : ℝ) ≤ Real.sqrt 9 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  exact h9.trans (Real.sqrt_le_sqrt (by linarith))

/-- The exact stationary fraction never exceeds the source's `(2/3)P_f`. -/
theorem peExactFailureFraction_le_two_thirds {Pf : ℝ} (hPf : 0 < Pf) :
    peExactFailureFraction Pf ≤ 2 * Pf / 3 := by
  have hs : (3 : ℝ) ≤ Real.sqrt (9 + 8 * Pf) := three_le_sqrt_nine_add_eight hPf
  have hs0 : 0 < Real.sqrt (9 + 8 * Pf) := Real.sqrt_pos.2 (by linarith)
  unfold peExactFailureFraction
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The source's `(2/3)P_f` is within `4P_f²/27` of the exact stationary
fraction, which is what "assuming small `P_f`" licenses in `E14`. -/
theorem two_thirds_sub_peExactFailureFraction_le {Pf : ℝ} (hPf : 0 < Pf) :
    2 * Pf / 3 - peExactFailureFraction Pf ≤ 4 * Pf ^ 2 / 27 := by
  have hs2 : Real.sqrt (9 + 8 * Pf) ^ 2 = 9 + 8 * Pf :=
    Real.sq_sqrt (by linarith)
  have hs : (3 : ℝ) ≤ Real.sqrt (9 + 8 * Pf) := three_le_sqrt_nine_add_eight hPf
  have hs0 : 0 < Real.sqrt (9 + 8 * Pf) := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ) < Real.sqrt (9 + 8 * Pf) + 3 := by linarith
  have hnum : Real.sqrt (9 + 8 * Pf) - 3 = 8 * Pf / (Real.sqrt (9 + 8 * Pf) + 3) := by
    rw [eq_div_iff (ne_of_gt hden)]
    nlinarith [hs2]
  have hgap : 2 * Pf / 3 - peExactFailureFraction Pf =
      (2 * Pf / 3) * (Real.sqrt (9 + 8 * Pf) - 3) / (Real.sqrt (9 + 8 * Pf) + 3) := by
    unfold peExactFailureFraction
    field_simp
    ring
  have hb : 8 * Pf / (Real.sqrt (9 + 8 * Pf) + 3) ≤ 8 * Pf / 6 := by
    refine div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  rw [hgap, hnum]
  have hstep : (2 * Pf / 3) * (8 * Pf / (Real.sqrt (9 + 8 * Pf) + 3)) /
      (Real.sqrt (9 + 8 * Pf) + 3) ≤ (2 * Pf / 3) * (8 * Pf / 6) / 6 := by
    have h1 : 8 * Pf / (Real.sqrt (9 + 8 * Pf) + 3) * (1 / (Real.sqrt (9 + 8 * Pf) + 3))
        ≤ (8 * Pf / 6) * (1 / 6) := by
      refine mul_le_mul hb ?_ (by positivity) (by linarith)
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    calc (2 * Pf / 3) * (8 * Pf / (Real.sqrt (9 + 8 * Pf) + 3)) /
          (Real.sqrt (9 + 8 * Pf) + 3)
        = (2 * Pf / 3) * (8 * Pf / (Real.sqrt (9 + 8 * Pf) + 3) *
            (1 / (Real.sqrt (9 + 8 * Pf) + 3))) := by ring
      _ ≤ (2 * Pf / 3) * ((8 * Pf / 6) * (1 / 6)) := by
          refine mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (2 * Pf / 3) * (8 * Pf / 6) / 6 := by ring
  have hfin : (2 * Pf / 3) * (8 * Pf / 6) / 6 = 4 * Pf ^ 2 / 27 := by ring
  linarith [hstep, hfin]

/-! ## The source's `133` form for small `P_f` -/

/-- The source's printed form of `E14` for small `P_f`: once
`P_f ≤ 1/134` the `(1+2P_f/3)²` factor is at most `1.01`, so the exact `E14`
bound is at most `135λ²/(δ_E²P_f³)` — the source's `133λ²/(δ_E²P_f³)` up to the
`(1+p_f)²` correction that `E14` drops. -/
theorem qdriftPhaseEstimation_gateBound_smallPf {m : ℕ} {lam deltaE Pf : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < deltaE) (hPf : 0 < Pf) (hsmall : Pf ≤ 1 / 134)
    (hm : 1 ≤ m) (hpow : (2 : ℝ) ^ m = pePowerScale lam deltaE (2 * Pf / 3)) :
    ∑ k ∈ range m, peQueryGates (k + 1) (peShare m (Pf / 6) k) ≤
      135 * lam ^ 2 / (deltaE ^ 2 * Pf ^ 3) := by
  refine (qdriftPhaseEstimation_gateBound hlam hdelta hPf hm hpow).trans ?_
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcoef : 27 * Real.pi ^ 2 / 2 < 133.25 := by
    nlinarith [sq_nonneg (Real.pi - 3.141593)]
  have hfrac : 2 * Pf / 3 ≤ 1 / 201 := by linarith
  have hfac : (1 + 2 * Pf / 3) ^ 2 ≤ 1.01 := by nlinarith
  have hprod : (27 * Real.pi ^ 2 / 2) * (1 + 2 * Pf / 3) ^ 2 ≤ 133.25 * 1.01 := by
    have h1 : (0 : ℝ) < 27 * Real.pi ^ 2 / 2 := by positivity
    have h2 : (0 : ℝ) < (1 + 2 * Pf / 3) ^ 2 := by
      have : 0 < 1 + 2 * Pf / 3 := by linarith
      positivity
    nlinarith [hcoef, hfac, sq_nonneg Real.pi]
  have hnn : (0 : ℝ) ≤ lam ^ 2 / (deltaE ^ 2 * Pf ^ 3) := by positivity
  have hstep1 : (27 * Real.pi ^ 2 / 2) * (1 + 2 * Pf / 3) ^ 2 * lam ^ 2 /
      (deltaE ^ 2 * Pf ^ 3) ≤ (133.25 * 1.01) * (lam ^ 2 / (deltaE ^ 2 * Pf ^ 3)) := by
    have hgoal : (27 * Real.pi ^ 2 / 2) * (1 + 2 * Pf / 3) ^ 2 * lam ^ 2 /
        (deltaE ^ 2 * Pf ^ 3)
        = ((27 * Real.pi ^ 2 / 2) * (1 + 2 * Pf / 3) ^ 2) *
            (lam ^ 2 / (deltaE ^ 2 * Pf ^ 3)) := by ring
    rw [hgoal]
    exact mul_le_mul_of_nonneg_right hprod hnn
  refine hstep1.trans ?_
  have h135 : (133.25 : ℝ) * 1.01 ≤ 135 := by norm_num
  calc (133.25 * 1.01) * (lam ^ 2 / (deltaE ^ 2 * Pf ^ 3))
      ≤ 135 * (lam ^ 2 / (deltaE ^ 2 * Pf ^ 3)) := mul_le_mul_of_nonneg_right h135 hnn
    _ = 135 * lam ^ 2 / (deltaE ^ 2 * Pf ^ 3) := by ring

end Qatlib.Papers.RandCompiler19.PhaseCosts.QdriftPhaseCost
