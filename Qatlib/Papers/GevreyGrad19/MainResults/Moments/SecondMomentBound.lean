/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option backward.isDefEq.respectTransparency false

/-!
# Even-Moment Interpolation Bound for Sums of Bounded Mean-Zero Coordinates

This module proves Lemma 3.9: if `μ` is a probability measure supported on
`[-1/2, 1/2]` with zero mean, then for independent coordinates `x_1, ..., x_d ~ μ`,
every `k : ℕ`, and every interpolation exponent `q ∈ [0, 1]`, the `2k`-th moment of
`∑_j x_j` is bounded by `[2 (d / 2)^k k!]^q · [(d / 2)^{2k}]^{1 - q}`.

## Main statements

* `secondMomentBound`: `q`-interpolated `2k`-th moment bound under `Measure.pi (fun _ => μ)`.

## References

* [Cornelissen, 2019][Cornelissen2019], Lemma 3.9, pp. 28--32.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace Qatlib.Papers.GevreyGrad19.MainResults.Moments

open Qatlib.Papers.GevreyGrad19.MainResults

private lemma subgaussian_sq_tail {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Ω → ℝ} {c : NNReal}
    (hX : ProbabilityTheory.HasSubgaussianMGF X c ν) {u : ℝ} (hu : 0 ≤ u) :
    ν.real {x | u ≤ X x ^ 2} ≤ 2 * Real.exp (-u / (2 * (c : ℝ))) := by
  have hp := hX.measure_ge_le (Real.sqrt_nonneg u)
  have hn := hX.neg.measure_ge_le (Real.sqrt_nonneg u)
  rw [Real.sq_sqrt hu] at hp hn
  have hs : {x | u ≤ X x ^ 2} ⊆
      {x | Real.sqrt u ≤ X x} ∪ {x | Real.sqrt u ≤ -X x} := by
    intro x hx
    have ha : Real.sqrt u ≤ |X x| := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hx
    exact le_abs.mp ha
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by
    simpa only [Pi.neg_apply, two_mul] using add_le_add hp hn))

private lemma subgaussian_even_moment {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Ω → ℝ} {c : NNReal}
    (hX : ProbabilityTheory.HasSubgaussianMGF X c ν) (hc : 0 < (c : ℝ))
    (k : ℕ) (hi : Integrable (fun x => X x ^ (2 * (k + 1))) ν) :
    ∫ x, X x ^ (2 * (k + 1)) ∂ν ≤
      2 * (2 * (c : ℝ)) ^ (k + 1) * ((k + 1).factorial : ℝ) := by
  let r : ℝ := (2 * (c : ℝ))⁻¹
  have hr : 0 < r := by positivity
  have hg : IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-(r * u))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := 1) (by linarith [Nat.cast_nonneg (α := ℝ) k])
        (by norm_num) hr)
  have heval : (∫ u : ℝ in Set.Ioi 0, u ^ k * Real.exp (-(r * u))) =
      (2 * (c : ℝ)) ^ (k + 1) * (k.factorial : ℝ) := by
    have he := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := ((k + 1 : ℕ) : ℝ)) (by positivity) hr
    rw [Real.rpow_natCast] at he
    simpa [r, Nat.cast_add, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using he
  -- Layer cake for the square reduces the moment to an exponential Gamma integral.
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul ν
    (f := fun x => X x ^ 2) (Filter.Eventually.of_forall fun x => sq_nonneg (X x))
    (hX.aemeasurable.pow_const 2) (p := ((k + 1 : ℕ) : ℝ)) (by positivity)
  simp only [Real.rpow_natCast, ← pow_mul] at hlayer
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast] at hlayer
  have hnn : 0 ≤ᵐ[ν] fun x => X x ^ (2 * (k + 1)) :=
    Filter.Eventually.of_forall fun x => by
      change 0 ≤ X x ^ (2 * (k + 1))
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg (X x)) (k + 1)
  have hbound : ENNReal.ofReal (∫ x, X x ^ (2 * (k + 1)) ∂ν) ≤
      ENNReal.ofReal (((k : ℝ) + 1) *
        (2 * ((2 * (c : ℝ)) ^ (k + 1) * (k.factorial : ℝ)))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi hnn, hlayer]
    calc
      _ ≤ ENNReal.ofReal ((k : ℝ) + 1) *
          ∫⁻ u : ℝ in Set.Ioi 0,
            ENNReal.ofReal (2 * Real.exp (-(r * u))) * ENNReal.ofReal (u ^ k) := by
        apply mul_le_mul_right
        apply setLIntegral_mono' measurableSet_Ioi
        intro u hu
        apply mul_le_mul_left
        rw [← ofReal_measureReal]
        apply ENNReal.ofReal_le_ofReal
        simpa [r, div_eq_mul_inv, mul_comm, neg_mul] using subgaussian_sq_tail hX hu.le
      _ = ENNReal.ofReal (((k : ℝ) + 1) *
          (2 * ((2 * (c : ℝ)) ^ (k + 1) * (k.factorial : ℝ)))) := by
        have heq : (fun u : ℝ => ENNReal.ofReal (2 * Real.exp (-(r * u))) *
            ENNReal.ofReal (u ^ k)) =
            (fun u : ℝ => ENNReal.ofReal (2 * (u ^ k * Real.exp (-(r * u))))) := by
          funext u
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hg.const_mul 2)]
        · rw [integral_const_mul, heval, ← ENNReal.ofReal_mul (by positivity)]
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
          exact mul_nonneg (by norm_num)
            (mul_nonneg (pow_nonneg hu.le _) (Real.exp_pos _).le)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  simpa only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    (show (∫ x, X x ^ (2 * (k + 1)) ∂ν) ≤
      2 * (2 * (c : ℝ)) ^ (k + 1) * (((k : ℝ) + 1) * (k.factorial : ℝ)) by
      nlinarith [hreal])

/-- **Lemma 3.9**: if `μ` is a probability measure with `μ(Set.Icc (-1/2) (1/2)) = 1`
and `∫ x, x ∂μ = 0`, then for all `k : ℕ` and `q ∈ [0, 1]`,
`∫ x, (∑ j, x j)^{2k} ∂(Measure.pi (fun _ : Fin d => μ)) ≤ [2 (d/2)^k k!]^q · [(d/2)^{2k}]^{1-q}`. -/
theorem secondMomentBound {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Icc (-1 / 2) (1 / 2)) = 1)
    (hmean : ∫ x, x ∂μ = 0) (k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ x : Fin d → ℝ, (∑ j, x j) ^ (2 * k)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin d => μ)) ≤
      (2 * ((d : ℝ) / 2) ^ k * (k.factorial : ℝ)) ^ q *
        (((d : ℝ) / 2) ^ (2 * k)) ^ (1 - q) := by
  classical
  let ν := Measure.pi (fun _ : Fin d => μ)
  let S : (Fin d → ℝ) → ℝ := fun x => ∑ j, x j
  change (∫ x, S x ^ (2 * k) ∂ν) ≤ _
  rcases k with _ | k
  · simpa using Real.one_le_rpow (x := (2 : ℝ)) (by norm_num) hq0
  by_cases hd : d = 0
  · subst d
    simp only [S, Finset.univ_eq_empty, Finset.sum_empty]
    rw [zero_pow (by omega), integral_zero]
    positivity
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hS : Continuous S := by fun_prop
  have hsupport : ∀ᵐ y ∂μ, y ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr hμ
  have hcoords : ∀ᵐ x ∂ν, ∀ j, x j ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval (fun _ : Fin d => μ) j).quasiMeasurePreserving.ae hsupport
  -- The support gives integrability and the deterministic endpoint.
  have hsum : ∀ᵐ x ∂ν, |S x| ≤ (d : ℝ) / 2 := by
    filter_upwards [hcoords] with x hx
    calc
      |S x| ≤ ∑ j, |x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, (1 / 2 : ℝ) :=
        Finset.sum_le_sum fun j _ => abs_le.mpr ⟨by linarith [(hx j).1], (hx j).2⟩
      _ = (d : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hpow : ∀ᵐ x ∂ν, S x ^ (2 * (k + 1)) ≤ ((d : ℝ) / 2) ^ (2 * (k + 1)) := by
    filter_upwards [hsum] with x hx
    calc
      S x ^ (2 * (k + 1)) ≤ |S x ^ (2 * (k + 1))| := le_abs_self _
      _ = |S x| ^ (2 * (k + 1)) := abs_pow _ _
      _ ≤ ((d : ℝ) / 2) ^ (2 * (k + 1)) := pow_le_pow_left₀ (abs_nonneg _) hx _
  have hnonneg : 0 ≤ᵐ[ν] fun x => S x ^ (2 * (k + 1)) :=
    Filter.Eventually.of_forall fun x => by
      change 0 ≤ S x ^ (2 * (k + 1))
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg (S x)) (k + 1)
  have hint : Integrable (fun x => S x ^ (2 * (k + 1))) ν :=
    (integrable_const (((d : ℝ) / 2) ^ (2 * (k + 1)))).mono_nonneg
      (hS.pow _).aestronglyMeasurable hnonneg hpow
  have hB₀ : (∫ x, S x ^ (2 * (k + 1)) ∂ν) ≤ ((d : ℝ) / 2) ^ (2 * (k + 1)) := by
    simpa using integral_mono_ae hint (integrable_const _) hpow
  have hM : 0 ≤ ∫ x, S x ^ (2 * (k + 1)) ∂ν := integral_nonneg_of_ae hnonneg
  -- Hoeffding's lemma and independence give the sub-Gaussian parameter d / 4.
  have hsub : ProbabilityTheory.HasSubgaussianMGF S ((d : NNReal) / 4) ν := by
    have hcoord (j : Fin d) :
        ProbabilityTheory.HasSubgaussianMGF (fun x : Fin d → ℝ => x j) (1 / 4) ν := by
      have hm : (∫ x : Fin d → ℝ, x j ∂ν) = 0 := by
        have heq := integral_map (μ := ν) (measurable_pi_apply j).aemeasurable
          (f := fun y : ℝ => y) (by fun_prop)
        rw [(measurePreserving_eval (fun _ : Fin d => μ) j).map_eq] at heq
        rw [← heq]
        exact hmean
      have hb : ∀ᵐ x ∂ν, x j ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) :=
        hcoords.mono fun _ hx => hx j
      convert ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (measurable_pi_apply j).aemeasurable hb hm using 1
      norm_num
    have hi := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
      (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin d => μ)
        (X := fun _ => id) (fun _ => aemeasurable_id))
      (s := Finset.univ) (fun j _ => hcoord j)
    simpa [S, div_eq_mul_inv] using hi
  have hB₁ : (∫ x, S x ^ (2 * (k + 1)) ∂ν) ≤
      2 * ((d : ℝ) / 2) ^ (k + 1) * ((k + 1).factorial : ℝ) := by
    have hv := subgaussian_even_moment hsub (by positivity) k hint
    simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat,
      show 2 * ((d : ℝ) / 4) = (d : ℝ) / 2 by ring] using hv
  rcases eq_or_lt_of_le hM with hzero | hpos
  · rw [← hzero]
    positivity
  calc
    _ = (∫ x, S x ^ (2 * (k + 1)) ∂ν) ^ q *
        (∫ x, S x ^ (2 * (k + 1)) ∂ν) ^ (1 - q) := by
      rw [← Real.rpow_add hpos, add_sub_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hM hB₁ hq0)
      (Real.rpow_le_rpow hM hB₀ (by linarith))
      (Real.rpow_nonneg hM _) (Real.rpow_nonneg (by positivity) _)

end Qatlib.Papers.GevreyGrad19.MainResults.Moments
