/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JeronimoShad26.MainResults.SourceModel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Binomial Central Absolute Moment Bounds

This module formalizes Appendix A (Lemmas A.1 and A.2) of Jeronimo and Shad
bounding the `q`-th absolute central moment `E_x |K / n - x|^q` of a binomial
random variable `K ~ Bin(n, x)` (`0 ≤ x ≤ 1`, `n ≥ 1`, `q ≥ 2`) in terms of the
Gaussian-tail integral constant `binomCoeff q` and `(q / (2 n))^{q / 2}`.

## Main statements

* `lemma_A_1`: Lemma A.1, `binomMoment q n x ≤ binomCoeff q * n^{-q / 2}`.
* `lemma_A_2`: Lemma A.2 (constant bound), `binomCoeff q ≤ (q / 2)^{q / 2}`.
* `lemma_A_2_consequence`: Lemma A.2, `binomMoment q n x ≤ (q / (2 n))^{q / 2}`.

## References

* [Jeronimo and Shad, 2026][JeronimoShad2026Shadow], Appendix A, Lemmas A.1 and
  A.2, pp. 32--33.
-/

set_option autoImplicit false

namespace Qatlib.Papers.JeronimoShad26.MainResults.AppABinomial

open Qatlib.Papers.JeronimoShad26.MainResults.SourceModel
open scoped BigOperators Interval

/-- The binomial probability mass function `C(n, k) x^k (1 - x)^{n - k}`. -/
noncomputable def binomPMF (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)

/-- The `q`-th absolute central moment `E_x |K / n - x|^q` for `K ~ Bin(n, x)`. -/
noncomputable def binomMoment (q n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), binomPMF n x k * |(k : ℝ) / (n : ℝ) - x| ^ q

/-- The moment prefactor `b_q`: `1 / 4` for `q = 2` and
`2 q ∫_{0}^{∞} t^{q - 1} exp(-2 t^2) dt` for `q ≠ 2`. -/
noncomputable def binomCoeff (q : ℕ) : ℝ :=
  if q = 2 then 1 / 4
  else 2 * (q : ℝ) * ∫ t in Set.Ioi (0 : ℝ), t ^ (q - 1) * Real.exp (-(2 * t ^ 2))

open MeasureTheory

private lemma pmf_nonneg (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    0 ≤ binomPMF n x k := by
  unfold binomPMF
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

private lemma bernoulli_mgf (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.exp (s * (1 - p)) + (1 - p) * Real.exp (-s * p) ≤
      Real.exp (s ^ 2 / 8) := by
  let prob : Set.Icc (0 : ℝ) 1 := ⟨p, hp0, hp1⟩
  have hb : ∀ᵐ z ∂ProbabilityTheory.bernoulliMeasure (1 - p) (-p) prob,
      z ∈ Set.Icc (-p) (1 - p) := by
    rw [ProbabilityTheory.bernoulliMeasure_def, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      simp only [ae_dirac_eq, Filter.eventually_pure, Set.mem_Icc]
      constructor <;> linarith
    · apply Measure.ae_smul_measure
      simp only [ae_dirac_eq, Filter.eventually_pure, Set.mem_Icc]
      constructor <;> linarith
  have hc : (∫ z, id z ∂ProbabilityTheory.bernoulliMeasure (1 - p) (-p) prob) = 0 := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    simp only [id_eq, smul_eq_mul, prob]
    ring
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    measurable_id.aemeasurable hb hc).mgf_le s
  simp only [ProbabilityTheory.mgf, ProbabilityTheory.integral_bernoulliMeasure,
    id_eq, smul_eq_mul, prob, show 1 - p - -p = 1 by ring, nnnorm_one,
    NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
  convert h using 1 <;> ring_nf

private lemma binomial_mgf (n : ℕ) (x s : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ Finset.range (n + 1), binomPMF n x k *
      Real.exp (s * ((k : ℝ) - n * x))) ≤ Real.exp ((n : ℝ) * s ^ 2 / 8) := by
  have he : (∑ k ∈ Finset.range (n + 1), binomPMF n x k *
      Real.exp (s * ((k : ℝ) - n * x))) =
      (x * Real.exp (s * (1 - x)) + (1 - x) * Real.exp (-s * x)) ^ n := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simpa using hk
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    unfold binomPMF
    rw [Nat.cast_sub hk']
    have hexp : s * ((k : ℝ) - n * x) =
        (k : ℝ) * (s * (1 - x)) + ((n : ℝ) - k) * (-s * x) := by ring
    rw [hexp, Real.exp_add]
    ring
  rw [he, show (n : ℝ) * s ^ 2 / 8 = (n : ℝ) * (s ^ 2 / 8) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity) (bernoulli_mgf x s hx0 hx1) n

private lemma moment_two (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    binomMoment 2 n x = x * (1 - x) / n := by
  have hv := bernstein.variance (n := n) (by omega) (⟨x, hx0, hx1⟩ : Set.Icc (0 : ℝ) 1)
  rw [binomMoment, ← Fin.sum_univ_eq_sum_range]
  convert hv using 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [bernstein_apply, bernstein.z, binomPMF, sq_abs]
  ring

private lemma binomial_tail (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (t : ℝ) (ht : 0 < t) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => t ≤ |(k : ℝ) / n - x|),
      binomPMF n x k) ≤ 2 * Real.exp (-2 * (n : ℝ) * t ^ 2) := by
  classical
  have hn0 : (0 : ℝ) < n := by positivity
  have hp := binomial_mgf n x (4 * t) hx0 hx1
  have hm := binomial_mgf n x (-4 * t) hx0 hx1
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (-4 * (n : ℝ) * t ^ 2) *
        (binomPMF n x k * Real.exp (4 * t * ((k : ℝ) - n * x)) +
          binomPMF n x k * Real.exp (-4 * t * ((k : ℝ) - n * x))) := by
      apply Finset.sum_le_sum
      intro k _
      have hw := pmf_nonneg n x hx0 hx1 k
      split_ifs with hk
      · have hc : (n : ℝ) * t ≤ |(k : ℝ) - n * x| := by
          calc
            _ ≤ (n : ℝ) * |(k : ℝ) / n - x| := mul_le_mul_of_nonneg_left hk hn0.le
            _ = |(n : ℝ)| * |(k : ℝ) / n - x| := by rw [abs_of_pos hn0]
            _ = |(n : ℝ) * ((k : ℝ) / n - x)| := (abs_mul _ _).symm
            _ = |(k : ℝ) - n * x| := by
              congr 1
              field_simp
        have he : 1 ≤ Real.exp (-4 * (n : ℝ) * t ^ 2) *
            (Real.exp (4 * t * ((k : ℝ) - n * x)) +
              Real.exp (-4 * t * ((k : ℝ) - n * x))) := by
          rcases le_abs.mp hc with h | h
          · calc
              _ ≤ Real.exp (-4 * (n : ℝ) * t ^ 2 + 4 * t * ((k : ℝ) - n * x)) := by
                apply Real.one_le_exp_iff.mpr
                nlinarith [mul_nonneg ht.le (sub_nonneg.mpr h)]
              _ ≤ _ := by
                rw [Real.exp_add]
                gcongr
                exact le_add_of_nonneg_right (Real.exp_nonneg _)
          · calc
              _ ≤ Real.exp (-4 * (n : ℝ) * t ^ 2 + -4 * t * ((k : ℝ) - n * x)) := by
                apply Real.one_le_exp_iff.mpr
                nlinarith [mul_nonneg ht.le (sub_nonneg.mpr h)]
              _ ≤ _ := by
                rw [Real.exp_add]
                gcongr
                exact le_add_of_nonneg_left (Real.exp_nonneg _)
        calc
          _ = binomPMF n x k * 1 := by ring
          _ ≤ binomPMF n x k * (Real.exp (-4 * (n : ℝ) * t ^ 2) *
              (Real.exp (4 * t * ((k : ℝ) - n * x)) +
                Real.exp (-4 * t * ((k : ℝ) - n * x)))) :=
            mul_le_mul_of_nonneg_left he hw
          _ = _ := by ring
      · positivity
    _ = Real.exp (-4 * (n : ℝ) * t ^ 2) *
        ((∑ k ∈ Finset.range (n + 1), binomPMF n x k *
          Real.exp (4 * t * ((k : ℝ) - n * x))) +
        ∑ k ∈ Finset.range (n + 1), binomPMF n x k *
          Real.exp (-4 * t * ((k : ℝ) - n * x))) := by
      rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ Real.exp (-4 * (n : ℝ) * t ^ 2) *
        (Real.exp ((n : ℝ) * (4 * t) ^ 2 / 8) +
          Real.exp ((n : ℝ) * (-4 * t) ^ 2 / 8)) := by gcongr
    _ = _ := by
      rw [show (n : ℝ) * (4 * t) ^ 2 / 8 = 2 * n * t ^ 2 by ring,
        show (n : ℝ) * (-4 * t) ^ 2 / 8 = 2 * n * t ^ 2 by ring,
        ← two_mul, mul_left_comm, ← Real.exp_add]
      congr 2
      ring

private lemma cutoff_integrable (r : ℕ) (a : ℝ) :
    IntegrableOn (fun t : ℝ => if t ≤ a then t ^ r else 0) (Set.Ioi 0) := by
  have hi : Integrable (Set.Ioc (0 : ℝ) a |>.indicator (fun t => t ^ r)) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (continuous_pow r).integrableOn_Ioc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [Set.indicator, Set.mem_Ioc, Set.mem_Ioi.mp ht, true_and]

private lemma cutoff_integral (q : ℕ) (hq : 1 ≤ q) (a : ℝ) (ha : 0 ≤ a) :
    (q : ℝ) * (∫ t in Set.Ioi (0 : ℝ), if t ≤ a then t ^ (q - 1) else 0) = a ^ q := by
  have he : (∫ t in Set.Ioi (0 : ℝ), if t ≤ a then t ^ (q - 1) else 0) =
      ∫ t in (0 : ℝ)..a, t ^ (q - 1) := by
    change (∫ t in Set.Ioi (0 : ℝ),
      (Set.Iic a).indicator (fun t : ℝ => t ^ (q - 1)) t) = _
    rw [setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
      intervalIntegral.integral_of_le ha]
  rw [he, integral_pow, Nat.sub_add_cancel hq]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hq
  rw [hcast]
  simp only [zero_pow (by omega : q ≠ 0), sub_zero]
  field_simp

private lemma gaussian_integral (q : ℕ) (hq : 1 ≤ q) (b : ℝ) (hb : 0 < b) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (q - 1) * Real.exp (-(b * t ^ 2))) =
      b ^ (-(q : ℝ) / 2) * (1 / 2) * Real.Gamma ((q : ℝ) / 2) := by
  have he : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hq
  simpa only [Real.rpow_natCast, Real.rpow_two, he, neg_mul] using
    (integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((q - 1 : ℕ) : ℝ))
      (b := b) (by norm_num)
      (by linarith [show (0 : ℝ) ≤ (q - 1 : ℕ) by positivity]) hb)

private lemma gamma_bound (q : ℕ) (hq : 3 ≤ q) :
    2 * Real.Gamma ((q : ℝ) / 2 + 1) ≤ (q : ℝ) ^ ((q : ℝ) / 2) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases h3 : q = 3
    · subst q
      have hg : Real.Gamma ((3 : ℝ) / 2 + 1) = (3 / 2) * (1 / 2) *
          Real.sqrt Real.pi := by
        rw [show (3 : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 by norm_num,
          Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
          Real.Gamma_one_half_eq]
        ring
      have hs : Real.sqrt Real.pi ≤ 2 :=
        (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
      calc
        _ ≤ 3 := by
          change 2 * Real.Gamma ((3 : ℝ) / 2 + 1) ≤ 3
          rw [hg]
          nlinarith
        _ = (3 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    by_cases h4 : q = 4
    · subst q
      norm_num [Real.rpow_two]
    have hk : 3 ≤ q - 2 := by omega
    have hrec := ih (q - 2) (by omega) hk
    have he : (q : ℝ) / 2 + 1 = ((q - 2 : ℕ) : ℝ) / 2 + 1 + 1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ q)]; norm_num; ring
    have hq0 : (0 : ℝ) < q := by positivity
    calc
      _ = ((q : ℝ) / 2) * (2 * Real.Gamma (((q - 2 : ℕ) : ℝ) / 2 + 1)) := by
        rw [he, Real.Gamma_add_one (by positivity)]
        rw [Nat.cast_sub (by omega : 2 ≤ q)]
        push_cast
        ring
      _ ≤ ((q : ℝ) / 2) * ((q - 2 : ℕ) : ℝ) ^ (((q - 2 : ℕ) : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hrec (by positivity)
      _ ≤ ((q : ℝ) / 2) * (q : ℝ) ^ (((q - 2 : ℕ) : ℝ) / 2) := by
        gcongr
        exact_mod_cast Nat.sub_le q 2
      _ = (1 / 2) * (q : ℝ) ^ ((q : ℝ) / 2) := by
        conv_rhs => rw [show (q : ℝ) / 2 = ((q - 2 : ℕ) : ℝ) / 2 + 1 by
          rw [Nat.cast_sub (by omega : 2 ≤ q)]; push_cast; ring,
          Real.rpow_add hq0, Real.rpow_one]
        ring
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hq0.le ((q : ℝ) / 2)]

/-- Lemma A.1: for `2 ≤ q`, `1 ≤ n`, and `0 ≤ x ≤ 1`,
`binomMoment q n x ≤ binomCoeff q * n^{-q / 2}`. -/
theorem lemma_A_1 (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      binomMoment q n x ≤ binomCoeff q * (n : ℝ) ^ (-(q : ℝ) / 2) := by
  intro x hx0 hx1
  classical
  have hn0 : (0 : ℝ) < n := by positivity
  by_cases h2 : q = 2
  · subst q
    rw [moment_two n hn x hx0 hx1]
    norm_num only [binomCoeff, Nat.cast_ofNat, ite_true, neg_div,
      div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_neg_one]
    have hx : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hx hn0.le
  have hi (k : ℕ) : IntegrableOn (fun t : ℝ => binomPMF n x k *
      (if t ≤ |(k : ℝ) / n - x| then t ^ (q - 1) else 0)) (Set.Ioi 0) :=
    (cutoff_integrable (q - 1) |(k : ℝ) / n - x|).const_mul _
  have hlayer : binomMoment q n x = (q : ℝ) *
      ∫ t in Set.Ioi (0 : ℝ), ∑ k ∈ Finset.range (n + 1), binomPMF n x k *
        (if t ≤ |(k : ℝ) / n - x| then t ^ (q - 1) else 0) := by
    rw [integral_finsetSum _ (fun k _ => hi k), Finset.mul_sum, binomMoment]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    calc
      _ = binomPMF n x k * ((q : ℝ) *
          ∫ t in Set.Ioi (0 : ℝ),
            if t ≤ |(k : ℝ) / n - x| then t ^ (q - 1) else 0) := by
        rw [cutoff_integral q (by omega) _ (abs_nonneg _)]
      _ = _ := by ring
  have hgauss : IntegrableOn (fun t : ℝ =>
      t ^ (q - 1) * Real.exp (-(2 * (n : ℝ) * t ^ 2))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * (n : ℝ)) (by positivity)
        (s := ((q - 1 : ℕ) : ℝ))
        (by linarith [show (0 : ℝ) ≤ (q - 1 : ℕ) by positivity]))
  calc
    _ = (q : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
        ∑ k ∈ Finset.range (n + 1), binomPMF n x k *
          (if t ≤ |(k : ℝ) / n - x| then t ^ (q - 1) else 0) := hlayer
    _ ≤ (q : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
        2 * (t ^ (q - 1) * Real.exp (-(2 * (n : ℝ) * t ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      apply setIntegral_mono_on (integrable_finsetSum _ (fun k _ => hi k))
        (hgauss.const_mul 2) measurableSet_Ioi
      intro t ht
      have he : (∑ k ∈ Finset.range (n + 1), binomPMF n x k *
          (if t ≤ |(k : ℝ) / n - x| then t ^ (q - 1) else 0)) =
          t ^ (q - 1) * ∑ k ∈ (Finset.range (n + 1)).filter
            (fun k : ℕ => t ≤ |(k : ℝ) / n - x|), binomPMF n x k := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      rw [he]
      have hb := mul_le_mul_of_nonneg_left (binomial_tail n hn x hx0 hx1 t ht)
        (pow_nonneg ht.le (q - 1))
      convert hb using 1
      ring_nf
    _ = 2 * (q : ℝ) * (∫ t in Set.Ioi (0 : ℝ),
        t ^ (q - 1) * Real.exp (-(2 * (n : ℝ) * t ^ 2))) := by
      rw [integral_const_mul]; ring
    _ = binomCoeff q * (n : ℝ) ^ (-(q : ℝ) / 2) := by
      simp only [binomCoeff, h2, ite_false]
      rw [gaussian_integral q (by omega) _ (by positivity),
        gaussian_integral q (by omega) 2 (by norm_num),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le]
      ring

/-- Lemma A.2 (constant bound): for `2 ≤ q`, `binomCoeff q ≤ (q / 2)^{q / 2}`. -/
theorem lemma_A_2 (q : ℕ) (hq : 2 ≤ q) :
    binomCoeff q ≤ ((q : ℝ) / 2) ^ ((q : ℝ) / 2) := by
  by_cases h2 : q = 2
  · subst q
    norm_num [binomCoeff]
  have hq0 : (0 : ℝ) < q := by positivity
  have hg := gamma_bound q (by omega)
  simp only [binomCoeff, h2, ite_false]
  rw [gaussian_integral q (by omega) 2 (by norm_num)]
  calc
    _ = (2 : ℝ) ^ (-(q : ℝ) / 2) *
        (2 * Real.Gamma ((q : ℝ) / 2 + 1)) := by
      rw [Real.Gamma_add_one (by positivity)]
      ring
    _ ≤ (2 : ℝ) ^ (-(q : ℝ) / 2) * (q : ℝ) ^ ((q : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by
      rw [Real.div_rpow hq0.le (by norm_num : (0 : ℝ) ≤ 2), show -(q : ℝ) / 2 = -((q : ℝ) / 2) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- Lemma A.2: for `2 ≤ q`, `1 ≤ n`, and `0 ≤ x ≤ 1`,
`binomMoment q n x ≤ (q / (2 n))^{q / 2}`. -/
theorem lemma_A_2_consequence (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      binomMoment q n x ≤ ((q : ℝ) / (2 * (n : ℝ))) ^ ((q : ℝ) / 2) := by
  intro x hx0 hx1
  have hn0 : (0 : ℝ) < n := by positivity
  calc
    _ ≤ binomCoeff q * (n : ℝ) ^ (-(q : ℝ) / 2) := lemma_A_1 q n hq hn x hx0 hx1
    _ ≤ ((q : ℝ) / 2) ^ ((q : ℝ) / 2) * (n : ℝ) ^ (-(q : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (lemma_A_2 q hq) (by positivity)
    _ = _ := by
      rw [show -(q : ℝ) / 2 = -((q : ℝ) / 2) by ring, Real.rpow_neg hn0.le,
        ← div_eq_mul_inv, ← Real.div_rpow (by positivity : (0 : ℝ) ≤ (q : ℝ) / 2) hn0.le]
      congr 1
      ring

end Qatlib.Papers.JeronimoShad26.MainResults.AppABinomial
