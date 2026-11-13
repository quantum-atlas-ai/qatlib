/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumMetro05.MainResults.Source

/-!
# Separable metrology precision

This module constructs independent probe distributions with `productLaw` and proves expectation
factorization and variance additivity. These identities give the separable error bound, with the
maximal variance realized by independent balanced two point laws. See
[GiovannettiLloydMaccone2006].

## Main statements

* `separables_variance_additive`: Under the independent product law, the variance of the sum of
  coordinate observables equals the sum of their marginal variances.
* `cc_cq_error_bound`: For bounded generator values and positive probe and repetition counts,
  the stated Cramér–Rao hypothesis gives error at least `1 / (√(ν * N) * (b - a))`.
* `eq3_max_variance`: For independent balanced two point probes at values `a` and `b`, the
  variance of their sum is `N * spectralSpread a b ^ 2`.

## References

* [Giovannetti et al., 2006][GiovannettiLloydMaccone2006]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.ClassicalBound

open Qatlib.Papers.QuantumMetro05.MainResults.Source

/-- The independent product of the finite probe distributions `q j`. -/
def productLaw {N d : ℕ} (q : Fin N → FinDist (Fin d)) : FinDist (Fin N → Fin d) where
  prob ω := ∏ j, (q j).prob (ω j)
  nonneg ω := Finset.prod_nonneg fun j _ => (q j).nonneg (ω j)
  sum_one := by
    have hswap : (∑ ω : Fin N → Fin d, ∏ j, (q j).prob (ω j))
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => (Finset.univ : Finset (Fin d))),
            ∏ j, (q j).prob (ω j) :=
      Finset.sum_congr rfl (fun ω _ => rfl)
    rw [hswap, ← Finset.prod_univ_sum]
    refine Finset.prod_eq_one fun j _ => ?_
    simpa using (q j).sum_one

/-- The probability of a product outcome equals the product of its coordinate probabilities. -/
@[simp] theorem productLaw_prob {N d : ℕ} (q : Fin N → FinDist (Fin d))
    (ω : Fin N → Fin d) : (productLaw q).prob ω = ∏ j, (q j).prob (ω j) := rfl

/-- The expectation of a product of coordinate functions under `productLaw` factors into the
product of the coordinate expectations. -/
theorem productLaw_expect_prod {N d : ℕ} (q : Fin N → FinDist (Fin d))
    (g : Fin N → Fin d → ℝ) :
    ∑ ω : Fin N → Fin d, (productLaw q).prob ω * ∏ k, g k (ω k)
      = ∏ k, (∑ x, (q k).prob x * g k x) := by
  have habs : ∀ ω : Fin N → Fin d,
      (productLaw q).prob ω * ∏ k, g k (ω k)
        = ∏ k, ((q k).prob (ω k) * g k (ω k)) := by
    intro ω
    simp only [productLaw]
    rw [← Finset.prod_mul_distrib]
  calc ∑ ω : Fin N → Fin d, (productLaw q).prob ω * ∏ k, g k (ω k)
      = ∑ ω : Fin N → Fin d, ∏ k, ((q k).prob (ω k) * g k (ω k)) :=
        Finset.sum_congr rfl fun ω _ => habs ω
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : Fin N => (Finset.univ : Finset (Fin d))),
          ∏ k, ((q k).prob (ω k) * g k (ω k)) :=
        Finset.sum_congr rfl fun ω _ => rfl
    _ = ∏ k, (∑ x ∈ (Finset.univ : Finset (Fin d)), (q k).prob x * g k x) :=
        (Finset.prod_univ_sum (t := fun _ : Fin N => (Finset.univ : Finset (Fin d)))
          (f := fun k x => (q k).prob x * g k x)).symm
    _ = ∏ k, (∑ x, (q k).prob x * g k x) := by simp

/-- A coordinate observable has the same expectation under `productLaw` as under its
corresponding marginal distribution. -/
theorem productLaw_expect_coord {N d : ℕ} (q : Fin N → FinDist (Fin d))
    (k : Fin N) (h : Fin d → ℝ) :
    ∑ ω : Fin N → Fin d, (productLaw q).prob ω * h (ω k) = ∑ x, (q k).prob x * h x := by
  have hsplit : ∀ ω : Fin N → Fin d,
      h (ω k) = ∏ j, (if j = k then h (ω j) else 1) := by
    intro ω
    rw [Finset.prod_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hjk; simp [hjk]
    · intro hcon; exact absurd (Finset.mem_univ k) hcon
  have hex := productLaw_expect_prod q (fun j x => if j = k then h x else 1)
  calc ∑ ω : Fin N → Fin d, (productLaw q).prob ω * h (ω k)
      = ∑ ω : Fin N → Fin d, (productLaw q).prob ω * ∏ j, (if j = k then h (ω j) else 1) :=
        Finset.sum_congr rfl fun ω _ => by rw [hsplit ω]
    _ = ∏ j, (∑ x, (q j).prob x * (if j = k then h x else 1)) := hex
    _ = ∑ x, (q k).prob x * h x := by
        rw [Finset.prod_eq_single k]
        · simp
        · intro j _ hjk
          simp only [hjk, if_false, mul_one]
          simpa using (q j).sum_one
        · intro hcon; exact absurd (Finset.mem_univ k) hcon

/-- The expectation of a sum of coordinate observables is the sum of their marginal
expectations. -/
theorem productLaw_expect_sum {N d : ℕ} (q : Fin N → FinDist (Fin d))
    (H : Fin N → Fin d → ℝ) :
    ∑ ω : Fin N → Fin d, (productLaw q).prob ω * (∑ j, H j (ω j))
      = ∑ j, ∑ x, (q j).prob x * H j x := by
  calc ∑ ω : Fin N → Fin d, (productLaw q).prob ω * (∑ j, H j (ω j))
      = ∑ ω : Fin N → Fin d, ∑ j, (productLaw q).prob ω * H j (ω j) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ ω : Fin N → Fin d, (productLaw q).prob ω * H j (ω j) := Finset.sum_comm
    _ = ∑ j, ∑ x, (q j).prob x * H j x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact productLaw_expect_coord q j (H j)

/-- Under the independent product law, the variance of the sum of coordinate observables equals
the sum of their marginal variances. See [GiovannettiLloydMaccone2006]. -/
theorem separables_variance_additive {N d : ℕ} (q : Fin N → FinDist (Fin d))
    (H : Fin N → Fin d → ℝ) :
    (productLaw q).variance (fun ω => ∑ j, H j (ω j))
      = ∑ j, (q j).variance (H j) := by
  have hmean : (productLaw q).expect (fun ω => ∑ j, H j (ω j))
      = ∑ j, (q j).expect (H j) := by
    simpa only [FinDist.expect] using productLaw_expect_sum q H

  have hterm : ∀ j k : Fin N,
      ∑ ω : Fin N → Fin d,
          (productLaw q).prob ω
            * ((H j (ω j) - (q j).expect (H j)) * (H k (ω k) - (q k).expect (H k)))
        = if j = k then (q j).variance (H j) else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have hg : (q j).variance (H j)
          = ∑ x, (q j).prob x * (H j x - (q j).expect (H j)) ^ 2 := rfl
      rw [hg]
      rw [← productLaw_expect_coord q j
        (fun x => (H j x - (q j).expect (H j)) ^ 2)]
      refine Finset.sum_congr rfl fun ω _ => ?_
      beta_reduce
      ring
    · rw [if_neg hjk]
      have hprod := productLaw_expect_prod q
        (fun m x => if m = j then (H j x - (q j).expect (H j))
                    else if m = k then (H k x - (q k).expect (H k)) else 1)
      have hcollapse : ∀ ω : Fin N → Fin d,
          ∏ m, (if m = j then (H j (ω m) - (q j).expect (H j))
                  else if m = k then (H k (ω m) - (q k).expect (H k)) else 1)
            = (H j (ω j) - (q j).expect (H j)) * (H k (ω k) - (q k).expect (H k)) := by
        intro ω
        have hpf : ∀ m : Fin N,
            (if m = j then (H j (ω m) - (q j).expect (H j))
              else if m = k then (H k (ω m) - (q k).expect (H k)) else 1)
            = (if m = j then (H j (ω m) - (q j).expect (H j)) else 1)
              * (if m = k then (H k (ω m) - (q k).expect (H k)) else 1) := by
          intro m
          by_cases hmj : m = j <;> by_cases hmk : m = k <;>
            simp [hmj, hmk, hjk, Ne.symm hjk]
        calc ∏ m, (if m = j then (H j (ω m) - (q j).expect (H j))
                    else if m = k then (H k (ω m) - (q k).expect (H k)) else 1)
            = ∏ m, ((if m = j then (H j (ω m) - (q j).expect (H j)) else 1)
                * (if m = k then (H k (ω m) - (q k).expect (H k)) else 1)) := by
              simp only [hpf]
          _ = (∏ m, (if m = j then (H j (ω m) - (q j).expect (H j)) else 1))
                * (∏ m, (if m = k then (H k (ω m) - (q k).expect (H k)) else 1)) :=
              Finset.prod_mul_distrib
          _ = (H j (ω j) - (q j).expect (H j)) * (H k (ω k) - (q k).expect (H k)) := by
              simp [Finset.prod_ite_eq']
      calc ∑ ω : Fin N → Fin d,
              (productLaw q).prob ω
                * ((H j (ω j) - (q j).expect (H j)) * (H k (ω k) - (q k).expect (H k)))
          = ∑ ω : Fin N → Fin d, (productLaw q).prob ω
              * ∏ m, (if m = j then (H j (ω m) - (q j).expect (H j))
                      else if m = k then (H k (ω m) - (q k).expect (H k)) else 1) := by
              refine Finset.sum_congr rfl fun ω _ => ?_
              rw [← hcollapse ω]
        _ = ∏ m, (∑ x, (q m).prob x
              * (if m = j then (H j x - (q j).expect (H j))
                  else if m = k then (H k x - (q k).expect (H k)) else 1)) := hprod
        _ = 0 := by
              refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
              simpa using FinDist.sum_sub_mean (q j) (H j)
  rw [FinDist.variance]
  rw [hmean]
  simp only [FinDist.expect]
  calc ∑ ω : Fin N → Fin d, (productLaw q).prob ω
          * ((∑ j, H j (ω j)) - (∑ j, (q j).expect (H j))) ^ 2
      = ∑ ω : Fin N → Fin d, (productLaw q).prob ω
          * (∑ j, (H j (ω j) - (q j).expect (H j))) ^ 2 := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ ω : Fin N → Fin d, ∑ j, ∑ k, (productLaw q).prob ω
          * ((H j (ω j) - (q j).expect (H j)) * (H k (ω k) - (q k).expect (H k))) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ k, ∑ ω : Fin N → Fin d, (productLaw q).prob ω
          * ((H j (ω j) - (q j).expect (H j)) * (H k (ω k) - (q k).expect (H k))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, (if j = k then (q j).variance (H j) else 0) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hterm j k
    _ = ∑ j, (q j).variance (H j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp

/-- For bounded generator values and positive probe and repetition counts, the stated Cramér–Rao
hypothesis gives error at least `1 / (√(ν * N) * (b - a))`. See
[GiovannettiLloydMaccone2006]. -/
theorem cc_cq_error_bound {N d : ℕ} (hN : 0 < N) (q : Fin N → FinDist (Fin d))
    (H : Fin d → ℝ) {a b ν δφ : ℝ} (hν : 0 < ν) (hab : a < b)
    (ha : ∀ x, a ≤ H x) (hb : ∀ x, H x ≤ b)
    (hcr : δφ * Real.sqrt ((productLaw q).variance (fun ω => ∑ j, H (ω j)))
            ≥ 1 / (2 * Real.sqrt ν)) :
    1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)) ≤ δφ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hspread : 0 < spectralSpread a b := by rw [spectralSpread_def]; linarith

  have hvarle : (productLaw q).variance (fun ω => ∑ j, H (ω j))
      ≤ (Real.sqrt (N : ℝ) * spectralSpread a b) ^ 2 := by
    rw [separables_variance_additive q (fun _ x => H x)]
    calc ∑ j : Fin N, (q j).variance ((fun _ x => H x) j)
        ≤ ∑ _j : Fin N, spectralSpread a b ^ 2 :=
          Finset.sum_le_sum fun j _ => variance_le_spread_sq (q j) H ha hb
      _ = (N : ℝ) * spectralSpread a b ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (Real.sqrt (N : ℝ) * spectralSpread a b) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
  have hΔhle : Real.sqrt ((productLaw q).variance (fun ω => ∑ j, H (ω j)))
      ≤ Real.sqrt (N : ℝ) * spectralSpread a b := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hvarle⟩
  have hΔhpos : 0 < Real.sqrt ((productLaw q).variance (fun ω => ∑ j, H (ω j))) := by
    by_contra hle
    have hzero : Real.sqrt ((productLaw q).variance (fun ω => ∑ j, H (ω j))) = 0 :=
      le_antisymm (not_lt.mp hle) (Real.sqrt_nonneg _)
    rw [hzero, mul_zero] at hcr
    have : 0 < 1 / (2 * Real.sqrt ν) := by positivity
    linarith
  have hmain := error_ge_of_variance_bound (δφ := δφ)
    (Δh := Real.sqrt ((productLaw q).variance (fun ω => ∑ j, H (ω j))))
    (R := Real.sqrt (N : ℝ) * spectralSpread a b) hν hΔhpos (by positivity) hΔhle hcr
  have hden2 : 2 * Real.sqrt ν * (Real.sqrt (N : ℝ) * spectralSpread a b)
      = Real.sqrt (ν * (N : ℝ)) * (b - a) := by
    rw [spectralSpread_def, Real.sqrt_mul (le_of_lt hν)]
    ring
  have hden : 1 / (2 * Real.sqrt ν * (Real.sqrt (N : ℝ) * spectralSpread a b))
      = 1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)) := by
    rw [hden2]
  rwa [hden] at hmain

/-- For independent balanced two point probes at values `a` and `b`, the variance of their sum
is `N * spectralSpread a b ^ 2`. See [GiovannettiLloydMaccone2006]. -/
theorem eq3_max_variance {N : ℕ} (a b : ℝ) :
    (productLaw (fun _ : Fin N => twoPointLaw)).variance
        (fun ω : Fin N → Fin 2 => ∑ _j : Fin N, twoPointValue a b (ω _j))
      = (N : ℝ) * spectralSpread a b ^ 2 := by
  rw [separables_variance_additive]
  simp only [twoPointLaw_variance]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Saturation of the Cramér–Rao expression at spread `√N * spectralSpread a b` gives error
exactly `1 / (√(ν * N) * (b - a))`. See [GiovannettiLloydMaccone2006]. -/
theorem eq3_attains_error_bound {N : ℕ} (hN : 0 < N) {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b)
    (hcr : δφ * (Real.sqrt (N : ℝ) * spectralSpread a b) = 1 / (2 * Real.sqrt ν)) :
    δφ = 1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hspread : spectralSpread a b ≠ 0 := by rw [spectralSpread_def]; linarith
  have hN0 : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  have hden : Real.sqrt (N : ℝ) * spectralSpread a b ≠ 0 := mul_ne_zero hN0 hspread
  have hstep : δφ = (1 / (2 * Real.sqrt ν)) / (Real.sqrt (N : ℝ) * spectralSpread a b) := by
    rw [eq_div_iff hden]
    exact hcr
  rw [hstep, div_div]
  have hden2 : 2 * Real.sqrt ν * (Real.sqrt (N : ℝ) * spectralSpread a b)
      = Real.sqrt (ν * (N : ℝ)) * (b - a) := by
    rw [spectralSpread_def, Real.sqrt_mul (le_of_lt hν)]
    ring
  rw [hden2]

end Qatlib.Papers.QuantumMetro05.MainResults.ClassicalBound
