/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.ContinuousAdv
import Qatlib.Papers.LocAdiabSrch01.MainResults.Optimality.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.LocAdiabSrch01.MainResults.Optimality

open Qatlib.Concepts.QueryComplexity.ContinuousAdv

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem overlap_deriv_value
    (Hm Hm' HD : V → V)
    (hHm : ∀ x y, inner ℂ (Hm x) y = inner ℂ x (Hm y))
    (hHm' : ∀ x y, inner ℂ (Hm' x) y = inner ℂ x (Hm' y))
    (hHD : ∀ x y, inner ℂ (HD x) y = inner ℂ x (HD y))
    (u v : V) :
    inner ℂ ((-Complex.I) • (Hm u + HD u)) v +
        inner ℂ u ((-Complex.I) • (Hm' v + HD v))
      = Complex.I * inner ℂ u (Hm v - Hm' v) := by
  have hconj : (starRingEnd ℂ) (-Complex.I) = Complex.I := by simp
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    hHm u v, hHD u v, inner_sub_right, hconj]
  ring

theorem overlap_hasDerivAt
    (Hm Hm' HD : ℝ → V → V)
    (hHm : ∀ t x y, inner ℂ (Hm t x) y = inner ℂ x (Hm t y))
    (hHm' : ∀ t x y, inner ℂ (Hm' t x) y = inner ℂ x (Hm' t y))
    (hHD : ∀ t x y, inner ℂ (HD t x) y = inner ℂ x (HD t y))
    (u v : ℝ → V)
    (hu : ∀ t, HasDerivAt u ((-Complex.I) • (Hm t (u t) + HD t (u t))) t)
    (hv : ∀ t, HasDerivAt v ((-Complex.I) • (Hm' t (v t) + HD t (v t))) t)
    (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (u s) (v s))
      (Complex.I * inner ℂ (u t) (Hm t (v t) - Hm' t (v t))) t := by
  have h := (hu t).inner ℂ (hv t)
  convert! h using 1
  have := overlap_deriv_value (Hm t) (Hm' t) (HD t) (hHm t) (hHm' t) (hHD t) (u t) (v t)
  rw [add_comm]
  exact this.symm

theorem neg_re_I_mul (z : ℂ) : -(Complex.I * z).re = z.im := by
  simp [Complex.mul_re]

theorem overlap_functional_hasDerivAt
    (Hm Hm' HD : ℝ → V → V)
    (hHm : ∀ t x y, inner ℂ (Hm t x) y = inner ℂ x (Hm t y))
    (hHm' : ∀ t x y, inner ℂ (Hm' t x) y = inner ℂ x (Hm' t y))
    (hHD : ∀ t x y, inner ℂ (HD t x) y = inner ℂ x (HD t y))
    (u v : ℝ → V)
    (hu : ∀ t, HasDerivAt u ((-Complex.I) • (Hm t (u t) + HD t (u t))) t)
    (hv : ∀ t, HasDerivAt v ((-Complex.I) • (Hm' t (v t) + HD t (v t))) t)
    (t : ℝ) :
    HasDerivAt (fun s => 1 - ‖inner ℂ (u s) (v s)‖ ^ 2)
      (2 * (inner ℂ (u t) (Hm t (v t) - Hm' t (v t)) * star (inner ℂ (u t) (v t))).im) t := by
  let p : ℝ → ℂ := fun s => inner ℂ (u s) (v s)
  let q : ℂ := inner ℂ (u t) (Hm t (v t) - Hm' t (v t))
  have hp : HasDerivAt p (Complex.I * q) t :=
    overlap_hasDerivAt Hm Hm' HD hHm hHm' hHD u v hu hv t
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  letI : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal
  have hnorm := hp.norm_sq
  rw [real_inner_eq_re_inner] at hnorm
  rw [RCLike.inner_apply] at hnorm
  have hfinal : HasDerivAt (fun s => 1 - ‖p s‖ ^ 2)
      (-(2 * ((Complex.I * q) * star (p t)).re)) t := by
    simpa using! hconst.sub hnorm
  have hval : -(2 * ((Complex.I * q) * star (p t)).re)
      = 2 * (q * star (p t)).im := by
    have hre : ((Complex.I * q) * star (p t)).re
        = -(q * star (p t)).im := by
      rw [show (Complex.I * q) * star (p t)
            = Complex.I * (q * star (p t)) by ring]
      linarith [neg_re_I_mul (q * star (p t))]
    rw [hre]
    ring
  rw [hval] at hfinal
  simpa only [p, q] using hfinal

theorem overlap_deriv_abs_le
    (Hm Hm' : V → V) (u v : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |(2 * (inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im)| ≤
      2 * (‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖) := by
  have hp : ‖inner ℂ u v‖ ≤ 1 := by
    calc ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hu, hv, mul_one]
  have hq : ‖inner ℂ u (Hm v - Hm' v)‖ ≤
      ‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖ := by
    calc ‖inner ℂ u (Hm v - Hm' v)‖ = ‖inner ℂ u (Hm v) - inner ℂ u (Hm' v)‖ := by
          rw [inner_sub_right]
      _ ≤ ‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖ := norm_sub_le _ _
  have hz : |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im| ≤
      ‖inner ℂ u (Hm v - Hm' v)‖ * ‖inner ℂ u v‖ := by
    calc |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im|
          ≤ ‖inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)‖ :=
            Complex.abs_im_le_norm _
      _ = ‖inner ℂ u (Hm v - Hm' v)‖ * ‖star (inner ℂ u v)‖ := norm_mul _ _
      _ = ‖inner ℂ u (Hm v - Hm' v)‖ * ‖inner ℂ u v‖ := by rw [norm_star]
  have hstep : |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im| ≤
      (‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖) * ‖inner ℂ u v‖ :=
    le_trans hz (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
  calc |(2 * (inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im)|
      = 2 * |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im| := by
        rw [abs_mul, abs_two]
    _ ≤ 2 * ((‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖) * ‖inner ℂ u v‖) := by
        exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 2 * ((‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖) * 1) := by
        have hnn : 0 ≤ ‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖ := by positivity
        nlinarith [hp, hnn]
    _ = 2 * (‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖) := by ring

theorem overlap_deriv_abs_le_swap
    (Hm Hm' : V → V)
    (hHm : ∀ x y, inner ℂ (Hm x) y = inner ℂ x (Hm y))
    (hHm' : ∀ x y, inner ℂ (Hm' x) y = inner ℂ x (Hm' y))
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |(2 * (inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im)| ≤
      2 * (‖Hm v‖ + ‖Hm' u‖) := by
  have hp : ‖inner ℂ u v‖ ≤ 1 := by
    calc ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hu, hv, mul_one]
  have h1 : ‖inner ℂ u (Hm v)‖ ≤ ‖Hm v‖ := by
    calc ‖inner ℂ u (Hm v)‖ ≤ ‖u‖ * ‖Hm v‖ := norm_inner_le_norm _ _
      _ = ‖Hm v‖ := by rw [hu, one_mul]
  have h2 : ‖inner ℂ u (Hm' v)‖ ≤ ‖Hm' u‖ := by
    rw [← hHm' u v]
    calc ‖inner ℂ (Hm' u) v‖ ≤ ‖Hm' u‖ * ‖v‖ := norm_inner_le_norm _ _
      _ = ‖Hm' u‖ := by rw [hv, mul_one]
  have hq : ‖inner ℂ u (Hm v - Hm' v)‖ ≤ ‖Hm v‖ + ‖Hm' u‖ := by
    calc ‖inner ℂ u (Hm v - Hm' v)‖
          = ‖inner ℂ u (Hm v) - inner ℂ u (Hm' v)‖ := by rw [inner_sub_right]
      _ ≤ ‖inner ℂ u (Hm v)‖ + ‖inner ℂ u (Hm' v)‖ := norm_sub_le _ _
      _ ≤ ‖Hm v‖ + ‖Hm' u‖ := add_le_add h1 h2
  have hz : |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im| ≤
      ‖inner ℂ u (Hm v - Hm' v)‖ * ‖inner ℂ u v‖ := by
    calc |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im|
          ≤ ‖inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)‖ := Complex.abs_im_le_norm _
      _ = ‖inner ℂ u (Hm v - Hm' v)‖ * ‖star (inner ℂ u v)‖ := norm_mul _ _
      _ = ‖inner ℂ u (Hm v - Hm' v)‖ * ‖inner ℂ u v‖ := by rw [norm_star]
  have hstep : |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im| ≤
      (‖Hm v‖ + ‖Hm' u‖) * ‖inner ℂ u v‖ :=
    le_trans hz (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
  calc |(2 * (inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im)|
      = 2 * |(inner ℂ u (Hm v - Hm' v) * star (inner ℂ u v)).im| := by
        rw [abs_mul, abs_two]
    _ ≤ 2 * ((‖Hm v‖ + ‖Hm' u‖) * ‖inner ℂ u v‖) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 2 * ((‖Hm v‖ + ‖Hm' u‖) * 1) := by
        have hnn : 0 ≤ ‖Hm v‖ + ‖Hm' u‖ := by positivity
        nlinarith [hp, hnn]
    _ = 2 * (‖Hm v‖ + ‖Hm' u‖) := by ring

theorem sum_rankOneAction_norm_le (b : OrthonormalBasis ι ℂ V) (E : ℝ) (hE : 0 ≤ E)
    (ψ : V) (hψ : ‖ψ‖ = 1) :
    (∑ m, ‖rankOneAction b E m ψ‖) ≤ E * Real.sqrt (Fintype.card ι) := by
  have hnorm : ∀ m, ‖rankOneAction b E m ψ‖ = E * ‖inner ℂ (b m) ψ‖ :=
    fun m => norm_rankOneAction b E m ψ hE
  simp only [hnorm]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_norm_inner_le_sqrt_card b ψ hψ) hE

def overlapFunctional (ψ : ι → ℝ → V) : ℝ → ℝ :=
  fun t => ∑ m, ∑ m', (1 - ‖inner ℂ (ψ m t) (ψ m' t)‖ ^ 2)

def overlapDeriv (b : OrthonormalBasis ι ℂ V) (s : ℝ → ℝ) (ψ : ι → ℝ → V) : ℝ → ℝ :=
  fun t => ∑ m, ∑ m',
    2 * (inner ℂ (ψ m t)
          (rankOneAction b (s t) m (ψ m' t) - rankOneAction b (s t) m' (ψ m' t))
          * star (inner ℂ (ψ m t) (ψ m' t))).im

theorem overlap_functional_hasDerivAt_sum
    (b : OrthonormalBasis ι ℂ V) (s : ℝ → ℝ) (HD : ℝ → V → V)
    (hHD : ∀ t x y, inner ℂ (HD t x) y = inner ℂ x (HD t y))
    (ψ : ι → ℝ → V)
    (hψ : ∀ m t, HasDerivAt (ψ m)
      ((-Complex.I) • (rankOneAction b (s t) m (ψ m t) + HD t (ψ m t))) t) :
    ∀ t, HasDerivAt (overlapFunctional ψ) (overlapDeriv b s ψ t) t := by
  intro t
  have hinner : ∀ m, HasDerivAt
      (fun t => ∑ m', (1 - ‖inner ℂ (ψ m t) (ψ m' t)‖ ^ 2))
      (∑ m', 2 * (inner ℂ (ψ m t)
        (rankOneAction b (s t) m (ψ m' t) - rankOneAction b (s t) m' (ψ m' t))
        * star (inner ℂ (ψ m t) (ψ m' t))).im) t := by
    intro m
    have h := HasDerivAt.sum (u := Finset.univ) (fun m' _ =>
      overlap_functional_hasDerivAt
        (fun t x => rankOneAction b (s t) m x) (fun t x => rankOneAction b (s t) m' x) HD
        (fun t x y => rankOneAction_inner_comm b (s t) m x y)
        (fun t x y => rankOneAction_inner_comm b (s t) m' x y) hHD
        (ψ m) (ψ m') (hψ m) (hψ m') t)
    simpa only [Finset.sum_fn] using h
  have h := HasDerivAt.sum (u := Finset.univ) (fun m _ => hinner m)
  simpa only [overlapFunctional, overlapDeriv, Finset.sum_fn] using! h

theorem overlap_deriv_sum_le
    (b : OrthonormalBasis ι ℂ V) (s : ℝ → ℝ) (ψ : ι → ℝ → V)
    (hs : ∀ t, 0 ≤ s t) (hψ_norm : ∀ m t, ‖ψ m t‖ = 1) (t : ℝ) :
    overlapDeriv b s ψ t ≤
      4 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) * s t := by
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  set r : ℝ := Real.sqrt (Fintype.card ι) with hr
  have hterm : ∀ m m', (2 * (inner ℂ (ψ m t)
        (rankOneAction b (s t) m (ψ m' t) - rankOneAction b (s t) m' (ψ m' t))
        * star (inner ℂ (ψ m t) (ψ m' t))).im)
      ≤ 2 * (‖rankOneAction b (s t) m (ψ m' t)‖ + ‖rankOneAction b (s t) m' (ψ m t)‖) := by
    intro m m'
    exact le_trans (le_abs_self _)
      (overlap_deriv_abs_le_swap (rankOneAction b (s t) m) (rankOneAction b (s t) m')
        (fun x y => rankOneAction_inner_comm b (s t) m x y)
        (fun x y => rankOneAction_inner_comm b (s t) m' x y)
        (ψ m t) (ψ m' t) (hψ_norm m t) (hψ_norm m' t))
  have hsum : overlapDeriv b s ψ t ≤
      ∑ m, ∑ m', 2 * (‖rankOneAction b (s t) m (ψ m' t)‖
        + ‖rankOneAction b (s t) m' (ψ m t)‖) := by
    simp only [overlapDeriv]
    apply Finset.sum_le_sum; intro m _
    apply Finset.sum_le_sum; intro m' _
    exact hterm m m'
  have hS1 : (∑ m, ∑ m', ‖rankOneAction b (s t) m (ψ m' t)‖) ≤ c * (s t * r) := by
    rw [Finset.sum_comm]
    have hb : ∀ m', (∑ m, ‖rankOneAction b (s t) m (ψ m' t)‖) ≤ s t * r := by
      intro m'
      have := sum_rankOneAction_norm_le b (s t) (hs t) (ψ m' t) (hψ_norm m' t)
      simpa [r] using this
    calc (∑ m', ∑ m, ‖rankOneAction b (s t) m (ψ m' t)‖)
        ≤ ∑ m', s t * r := Finset.sum_le_sum (fun m' _ => hb m')
      _ = c * (s t * r) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hS2 : (∑ m, ∑ m', ‖rankOneAction b (s t) m' (ψ m t)‖) ≤ c * (s t * r) := by
    have hb : ∀ m, (∑ m', ‖rankOneAction b (s t) m' (ψ m t)‖) ≤ s t * r := by
      intro m
      have := sum_rankOneAction_norm_le b (s t) (hs t) (ψ m t) (hψ_norm m t)
      simpa [r] using this
    calc (∑ m, ∑ m', ‖rankOneAction b (s t) m' (ψ m t)‖)
        ≤ ∑ m, s t * r := Finset.sum_le_sum (fun m _ => hb m)
      _ = c * (s t * r) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : (∑ m, ∑ m', 2 * (‖rankOneAction b (s t) m (ψ m' t)‖
        + ‖rankOneAction b (s t) m' (ψ m t)‖))
      = 2 * (∑ m, ∑ m', ‖rankOneAction b (s t) m (ψ m' t)‖)
        + 2 * (∑ m, ∑ m', ‖rankOneAction b (s t) m' (ψ m t)‖) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hsr : 0 ≤ s t * r := mul_nonneg (hs t) (Real.sqrt_nonneg _)
  calc overlapDeriv b s ψ t
      ≤ ∑ m, ∑ m', 2 * (‖rankOneAction b (s t) m (ψ m' t)‖
          + ‖rankOneAction b (s t) m' (ψ m t)‖) := hsum
    _ = 2 * (∑ m, ∑ m', ‖rankOneAction b (s t) m (ψ m' t)‖)
        + 2 * (∑ m, ∑ m', ‖rankOneAction b (s t) m' (ψ m t)‖) := hsplit
    _ ≤ 2 * (c * (s t * r)) + 2 * (c * (s t * r)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hS1 (by norm_num))
          (mul_le_mul_of_nonneg_left hS2 (by norm_num))
    _ = 4 * c * r * s t := by ring

theorem overlap_growth_le
    [Nonempty ι]
    (b : OrthonormalBasis ι ℂ V) (s : ℝ → ℝ) (HD : ℝ → V → V)
    (hHD : ∀ t x y, inner ℂ (HD t x) y = inner ℂ x (HD t y))
    (ψ : ι → ℝ → V) (ψ0 : V)
    (hψ : ∀ m t, HasDerivAt (ψ m)
      ((-Complex.I) • (rankOneAction b (s t) m (ψ m t) + HD t (ψ m t))) t)
    (hψ_norm : ∀ m t, ‖ψ m t‖ = 1)
    (hs : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hinit : ∀ m, ψ m 0 = ψ0)
    {T : ℝ} (hT : 0 ≤ T) :
    overlapFunctional ψ T ≤ 4 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) * T := by
  set C : ℝ := 4 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) with hC
  have hFderiv : ∀ t, HasDerivAt (overlapFunctional ψ) (overlapDeriv b s ψ t) t :=
    overlap_functional_hasDerivAt_sum b s HD hHD ψ hψ
  have hFcont : ContinuousOn (overlapFunctional ψ) (Set.Icc 0 T) :=
    fun x _ => (hFderiv x).continuousAt.continuousWithinAt
  have hCnonneg : 0 ≤ C := by
    rw [hC]; positivity
  have hd : ∀ t ∈ Set.Ico 0 T, overlapDeriv b s ψ t ≤ C := by
    intro t _
    have h := overlap_deriv_sum_le b s ψ hs hψ_norm t
    calc overlapDeriv b s ψ t
        ≤ 4 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) * s t := h
      _ ≤ 4 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) * 1 :=
          mul_le_mul_of_nonneg_left (hs1 t) hCnonneg
      _ = C := by rw [hC, mul_one]
  have hψ0norm : ‖ψ0‖ = 1 := by
    have := hψ_norm (Classical.arbitrary ι) 0
    rwa [hinit (Classical.arbitrary ι)] at this
  have hF0 : overlapFunctional ψ 0 ≤ C * 0 := by
    have hzero : overlapFunctional ψ 0 = 0 := by
      simp only [overlapFunctional]
      apply Finset.sum_eq_zero
      intro m _
      apply Finset.sum_eq_zero
      intro m' _
      rw [hinit m, hinit m']
      have hsq : ‖inner ℂ ψ0 ψ0‖ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hψ0norm]
        norm_num
      rw [hsq]; norm_num
    rw [hzero, mul_zero]
  have hBcont : ContinuousOn (fun t => C * t) (Set.Icc 0 T) := by fun_prop
  have hBderiv : ∀ x ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun t => C * t) C (Set.Ici x) x := by
    intro x _
    simpa using ((hasDerivAt_id x).const_mul C).hasDerivWithinAt
  have hmain : overlapFunctional ψ T ≤ C * T :=
    image_le_of_deriv_right_le_deriv_boundary hFcont
      (fun x _ => (hFderiv x).hasDerivWithinAt) hF0 hBcont hBderiv hd
      (show T ∈ Set.Icc 0 T from ⟨hT, le_rfl⟩)
  simpa [hC] using hmain

theorem optimality_lower_bound_of_overlap
    [Nonempty ι]
    (b : OrthonormalBasis ι ℂ V) (s : ℝ → ℝ) (HD : ℝ → V → V)
    (hHD : ∀ t x y, inner ℂ (HD t x) y = inner ℂ x (HD t y))
    (ψ : ι → ℝ → V) (ψ0 : V)
    (hψ : ∀ m t, HasDerivAt (ψ m)
      ((-Complex.I) • (rankOneAction b (s t) m (ψ m t) + HD t (ψ m t))) t)
    (hψ_norm : ∀ m t, ‖ψ m t‖ = 1)
    (hs : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hinit : ∀ m, ψ m 0 = ψ0)
    {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (hdist : ε * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))
      ≤ overlapFunctional ψ T) :
    T ≥ ε * ((Fintype.card ι : ℝ) - 1) / (4 * Real.sqrt (Fintype.card ι)) := by
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  set r : ℝ := Real.sqrt (Fintype.card ι) with hr
  have hcpos : 0 < c := by
    rw [hc]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hrpos : 0 < r := by
    rw [hr]
    exact Real.sqrt_pos.mpr hcpos
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hgrowth := overlap_growth_le b s HD hHD ψ ψ0 hψ hψ_norm hs hs1 hinit hT
  rw [show 4 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) = 4 * c * r from by rw [hc, hr]] at hgrowth

  have hA : ε * c * (c - 1) ≤ 4 * c * r * T := by
    have h1 : ε * (c * (c - 1)) ≤ overlapFunctional ψ T := by
      simpa [hc] using hdist
    nlinarith [h1, hgrowth]

  have hB : ε * (c - 1) ≤ 4 * r * T := by
    have := mul_le_mul_of_nonneg_left hA (le_of_lt hcpos)

    have hcA : ε * c * (c - 1) = c * (ε * (c - 1)) := by ring
    have hcB : 4 * c * r * T = c * (4 * r * T) := by ring
    rw [hcA, hcB] at hA
    exact (mul_le_mul_iff_of_pos_left hcpos).mp hA

  have h4r : 0 < 4 * r := by positivity
  rw [ge_iff_le, div_le_iff₀ h4r]
  nlinarith [hB]

end Qatlib.Papers.LocAdiabSrch01.MainResults.Optimality
