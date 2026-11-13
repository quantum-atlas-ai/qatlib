/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.SourceTermCountModel

/-!
# Anharmonic Oscillator Trotter-Suzuki Term Count Bound

This module formalizes the exponent scaling and segment-count bound for simulating the
one-dimensional anharmonic oscillator $H = (\hat{p}^2 + \hat{x}^q)/2$ ($2 \le q \le 6$) via
order-$2p$ Trotter-Suzuki product formulas, establishing the sublinear ($q \le 5$) and
subquadratic ($q = 6$) dependence of the exponential count $N = r N_p$ on the energy-cutoff
parameter $m'$.

## Main statements

* `anharmonic_exponent_eventually_sublinear`: For $q \le 5$, the $m'$-exponent
  $q/(4p) + q/4 - 1/2$ is eventually strictly below $1$ as $p \to \infty$.
* `anharmonic_exponent_eventually_subquadratic`: For $q \le 6$, the $m'$-exponent
  $q/(4p) + q/4 - 1/2$ is eventually strictly below $2$ as $p \to \infty$.
* `anharmonic_termCount_eq17`: Explicit segment count $r \ge 1$ satisfying both the
  anharmonic series error bound $r \, \varepsilon_{2p}(t/r) \le \varepsilon$ and the
  total exponential bound $r N_p \le C \cdot \mathrm{eq17Bound}(p, q, m', t, \varepsilon) + N_p$.

## References

* [Somma, 2016][Somma2016]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

/-- For `q ≤ 5`, the `m'`-exponent `q / (4p) + q / 4 - 1 / 2` is eventually strictly below `1`
as `p → ∞` [Somma2016]. -/
theorem anharmonic_exponent_eventually_sublinear {q : ℕ} (hq : q ≤ 5) :
    ∀ᶠ p : ℕ in Filter.atTop,
      (q : ℝ) / (4 * (p : ℝ)) + (q : ℝ) / 4 - 1 / 2 < 1 := by
  rw [Filter.eventually_atTop]
  refine ⟨6, fun p hp => ?_⟩
  have hp0 : (0 : ℝ) < 4 * (p : ℝ) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    linarith
  have hq' : (q : ℝ) ≤ 5 := by exact_mod_cast hq
  have h1 : (q : ℝ) / (4 * (p : ℝ)) ≤ 5 / (4 * (p : ℝ)) :=
    div_le_div_of_nonneg_right hq' hp0.le
  have h2 : (5 : ℝ) / (4 * (p : ℝ)) < 1 / 4 := by
    rw [div_lt_iff₀ hp0]
    have hp6 : (6 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h3 : (q : ℝ) / 4 ≤ 5 / 4 :=
    div_le_div_of_nonneg_right hq' (by norm_num)
  linarith

/-- For `q ≤ 6`, the `m'`-exponent `q / (4p) + q / 4 - 1 / 2` is eventually strictly below `2`
as `p → ∞` [Somma2016]. -/
theorem anharmonic_exponent_eventually_subquadratic {q : ℕ} (hq : q ≤ 6) :
    ∀ᶠ p : ℕ in Filter.atTop,
      (q : ℝ) / (4 * (p : ℝ)) + (q : ℝ) / 4 - 1 / 2 < 2 := by
  rw [Filter.eventually_atTop]
  refine ⟨2, fun p hp => ?_⟩
  have hp0 : (0 : ℝ) < 4 * (p : ℝ) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    linarith
  have hq' : (q : ℝ) ≤ 6 := by exact_mod_cast hq
  have h1 : (q : ℝ) / (4 * (p : ℝ)) ≤ 6 / (4 * (p : ℝ)) :=
    div_le_div_of_nonneg_right hq' hp0.le
  have h2 : (6 : ℝ) / (4 * (p : ℝ)) < 1 := by
    rw [div_lt_iff₀ hp0]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h3 : (q : ℝ) / 4 ≤ 6 / 4 :=
    div_le_div_of_nonneg_right hq' (by norm_num)
  linarith

private lemma anharmonic_series_le {p q : ℕ} {c lam Np m : ℝ}
    (hm : 0 < m) (hx : 0 ≤ c * lam * Np ^ 2)
    (hρ : c * lam * Np ^ 2 * m ^ (((q : ℝ) - 2) / 4) ≤ 1 / 2) :
    anharmonicErrorBound p q c lam Np m ≤
      2 * ((c * lam * Np ^ 2) ^ (2 * p + 1) *
        m ^ (((2 * p : ℕ) : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2)) := by
  let x := c * lam * Np ^ 2
  let ρ := x * m ^ (((q : ℝ) - 2) / 4)
  let A := x ^ (2 * p + 1) *
    m ^ (((2 * p : ℕ) : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2)
  let f := fun j : ℕ => if j < 2 * p then (0 : ℝ)
    else x ^ (j + 1) * m ^ ((j : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2)
  have hρ0 : 0 ≤ ρ := mul_nonneg hx (Real.rpow_nonneg hm.le _)
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ (by norm_num)
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg hx _) (Real.rpow_nonneg hm.le _)
  have hterm (k : ℕ) : f (k + 2 * p) = A * ρ ^ k := by
    have hk : ¬ k + 2 * p < 2 * p := by omega
    dsimp [f, A, ρ, x]
    rw [ite_eq_right hk]
    have he : ((k + 2 * p : ℕ) : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2 =
        (((2 * p : ℕ) : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2) +
          (((q : ℝ) - 2) / 4) * (k : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_add hm, Real.rpow_mul_natCast hm.le, mul_pow]
    rw [show k + 2 * p + 1 = (2 * p + 1) + k by omega, pow_add]
    ring
  have hsum : Summable (fun k => f (k + 2 * p)) := by
    simpa only [hterm] using (summable_geometric_of_lt_one hρ0 hρ1).mul_left A
  have hzero : ∑ j ∈ Finset.range (2 * p), f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_left (Finset.mem_range.mp hj)
  have heq : anharmonicErrorBound p q c lam Np m = A * (1 - ρ)⁻¹ := by
    change (∑' j, f j) = _
    rw [← hsum.sum_add_tsum_nat_add', hzero, zero_add]
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
  have hinv : (1 - ρ)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ρ)).2
    linarith
  change anharmonicErrorBound p q c lam Np m ≤ 2 * A
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hinv hA]

/-- **Eq. (17)** [Somma2016]: for `2 ≤ q ≤ 6`, `p ≥ 1`, and `c > 1`, there exists `C > 0`
such that whenever `1 ≤ m'`, `0 ≤ t`, `0 < ε`, and `1 ≤ m' * t / ε`, there is a segment count
`r ≥ 1` satisfying `r * anharmonicErrorBound p q c (t / r) N_p m' ≤ ε` and
`r * N_p ≤ C * eq17Bound p q m' t ε + N_p`. -/
theorem anharmonic_termCount_eq17 (p q : ℕ) (hp : 1 ≤ p) (hq : 2 ≤ q) (_hq6 : q ≤ 6)
    {c : ℝ} (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m' t ε : ℝ), 1 ≤ m' → 0 ≤ t → 0 < ε → 1 ≤ m' * t / ε →
        ∃ r : ℕ, 1 ≤ r ∧
          (r : ℝ) *
              anharmonicErrorBound p q c (t / (r : ℝ)) (sourceMacroCount 2 p) m' ≤ ε ∧
            (r : ℝ) * sourceMacroCount 2 p ≤
              C * eq17Bound p q m' t ε + sourceMacroCount 2 p := by
  let n : ℕ := 2 * p
  let Np := sourceMacroCount 2 p
  let x := c * Np ^ 2
  -- This constant controls both the geometric ratio and the leading error coefficient.
  let K := 1 + 2 * x + 2 * x ^ (n + 1)
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hNp : 0 < Np := by dsimp [Np, sourceMacroCount]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hK1 : 1 ≤ K := by
    dsimp [K]
    nlinarith [pow_nonneg hx.le (n + 1)]
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) hK1
  have hKx : 2 * x ≤ K := by
    dsimp [K]
    nlinarith [pow_nonneg hx.le (n + 1)]
  have hKpow : 2 * x ^ (n + 1) ≤ K ^ n := by
    calc
      _ ≤ K := by dsimp [K]; linarith
      _ ≤ K ^ n := le_self_pow₀ hK1 hn
  refine ⟨K * Np / (5 : ℝ) ^ (3 * p), by positivity, ?_⟩
  intro m t ε hm ht hε hreg
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := le_antisymm (le_of_not_gt h) ht
    norm_num [htzero] at hreg
  have hεmt : ε ≤ m * t := by
    simpa only [one_mul] using (le_div_iff₀ hε).mp hreg
  let s : ℝ := 1 / (n : ℝ)
  let d : ℝ := ((q : ℝ) - 2) / 4
  let a : ℝ := (q : ℝ) / (4 * (p : ℝ)) + (q : ℝ) / 4 - 1 / 2
  let b : ℝ := (n : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsN : s * (n : ℝ) = 1 := by dsimp [s]; field_simp
  have haN : a * (n : ℝ) = b := by
    dsimp [a, b, n]
    push_cast
    field_simp
    ring
  have hsa : d + s ≤ a := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have he : a - (d + s) = ((q : ℝ) - 2) / (4 * (p : ℝ)) := by
      dsimp [a, d, s, n]
      push_cast
      field_simp
      ring
    have : 0 ≤ a - (d + s) := by rw [he]; positivity
    linarith
  let R := K * m ^ a * t ^ (1 + s) / ε ^ s
  have hR : 0 < R := by dsimp [R]; positivity
  let r : ℕ := Nat.ceil R
  have hRr : R ≤ (r : ℝ) := Nat.le_ceil R
  have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le hR hRr
  have hr : 1 ≤ r := by exact_mod_cast (show 0 < r by exact_mod_cast hrpos)
  have hrceil : (r : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have hεpow : ε ^ s ≤ m ^ s * t ^ s := by
    rw [← Real.mul_rpow hmpos.le ht]
    exact Real.rpow_le_rpow hε.le hεmt hs
  have hmpow : m ^ (d + s) ≤ m ^ a := Real.rpow_le_rpow_of_exponent_le hm hsa
  have htadd : t ^ (1 + s) = t * t ^ s := by
    rw [Real.rpow_add htpos, Real.rpow_one]
  -- The regime ε ≤ m * t makes the geometric ratio at most one half.
  have hRlarge : 2 * x * t * m ^ d ≤ R := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hε s)).2
    calc
      (2 * x * t * m ^ d) * ε ^ s ≤
          (2 * x * t * m ^ d) * (m ^ s * t ^ s) := by
        exact mul_le_mul_of_nonneg_left hεpow (by positivity)
      _ = (2 * x) * m ^ (d + s) * t ^ (1 + s) := by
        rw [Real.rpow_add hmpos, htadd]
        ring
      _ ≤ K * m ^ a * t ^ (1 + s) := by
        gcongr
  let ρ := c * (t / (r : ℝ)) * Np ^ 2 * m ^ d
  have hρ : ρ ≤ 1 / 2 := by
    have hh : 2 * x * t * m ^ d ≤ (r : ℝ) := hRlarge.trans hRr
    dsimp [ρ]
    rw [show c * (t / (r : ℝ)) * Np ^ 2 * m ^ d =
      (x * t * m ^ d) / (r : ℝ) by dsimp [x]; ring]
    apply (div_le_iff₀ hrpos).2
    linarith
  let A := (c * (t / (r : ℝ)) * Np ^ 2) ^ (n + 1) * m ^ b
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have herr : anharmonicErrorBound p q c (t / (r : ℝ)) Np m ≤ 2 * A :=
    anharmonic_series_le hmpos (by positivity) hρ
  -- Raising the real segment count to order 2p cancels all fractional exponents.
  have hRpow : R ^ n * ε = K ^ n * m ^ b * t ^ (n + 1) := by
    have hmN : (m ^ a) ^ n = m ^ b := by
      rw [← Real.rpow_mul_natCast hmpos.le, haN]
    have htN : (t ^ (1 + s)) ^ n = t ^ (n + 1) := by
      rw [← Real.rpow_mul_natCast ht]
      rw [show (1 + s) * (n : ℝ) = ((n + 1 : ℕ) : ℝ) by
        push_cast
        nlinarith [hsN]]
      exact Real.rpow_natCast t (n + 1)
    have hεN : (ε ^ s) ^ n = ε := by
      rw [← Real.rpow_mul_natCast hε.le, hsN, Real.rpow_one]
    dsimp [R]
    rw [div_pow, mul_pow, mul_pow, hmN, htN, hεN]
    exact div_mul_cancel₀ _ hε.ne'
  have hApow : ((r : ℝ) * (2 * A)) * (r : ℝ) ^ n =
      2 * x ^ (n + 1) * m ^ b * t ^ (n + 1) := by
    dsimp [A]
    rw [show c * (t / (r : ℝ)) * Np ^ 2 = x * t / (r : ℝ) by
      dsimp [x]
      ring]
    rw [div_pow, mul_pow, pow_succ]
    field_simp
    ring
  have herror : (r : ℝ) * (2 * A) ≤ ε := by
    apply (mul_le_mul_iff_left₀ (pow_pos hrpos n)).mp
    calc
      ((r : ℝ) * (2 * A)) * (r : ℝ) ^ n =
          2 * x ^ (n + 1) * m ^ b * t ^ (n + 1) := hApow
      _ ≤ K ^ n * m ^ b * t ^ (n + 1) := by gcongr
      _ = R ^ n * ε := hRpow.symm
      _ ≤ (r : ℝ) ^ n * ε := by gcongr
      _ = ε * (r : ℝ) ^ n := mul_comm _ _
  refine ⟨r, hr, (mul_le_mul_of_nonneg_left herr hrpos.le).trans herror, ?_⟩
  calc
    (r : ℝ) * Np ≤ (R + 1) * Np :=
      mul_le_mul_of_nonneg_right hrceil.le hNp.le
    _ = (K * Np / (5 : ℝ) ^ (3 * p)) * eq17Bound p q m t ε + Np := by
      dsimp [R, a, s, n, eq17Bound]
      push_cast
      field_simp

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount
