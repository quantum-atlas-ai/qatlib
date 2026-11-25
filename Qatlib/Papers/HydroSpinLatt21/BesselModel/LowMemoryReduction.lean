/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Low-memory reduction of the wave-mediated coupling force

[Saenz2021HydroSpinLattices], Methods equations (13)-(15), models the wave
field of the `j`-th droplet by a memory kernel: the coupling force on
droplet `i` at time `t` is an exponentially weighted history integral of a
`J₁`-kernel along the trajectory of droplet `j`, with memory time `T_M`. In
the low-memory regime `T_M ≪ 2π/ω₀` the paper replaces the history integral
by the instantaneous value times `T_M`, which is equation (15). See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This file proves the quantitative content of that step for a general scalar
lag kernel `κ` (in the application, `κ` is the azimuthal projection of the
`J₁`-kernel of equation (14) along a circular neighbour orbit). The main
theorem bounds the deviation of the truncated memory integral
`∫₀^R κ(u) e^{-u/T} du` from the memory-free value
`κ(0) · T · (1 - e^{-R/T})` by `Λ T² (1 - (1 + R/T) e^{-R/T}) ≤ Λ T²`,
where `Λ` is a Lipschitz constant of the lag kernel in the lag variable.
The overall normalization `1/T_F` of equation (14) and the physical
identification of the interaction coefficient `ℱ` are absorbed into the
kernel and are not asserted here; no Bessel function enters this file.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Real intervalIntegral
open Filter MeasureTheory
open scoped Topology

/-! ## The memory kernel estimate -/

/-- The exponential memory weight is continuous in the lag. -/
theorem exp_weight_cont (T : ℝ) : Continuous (fun u => Real.exp (-(u / T))) := by
  have h1 : Continuous (fun u => u / T) := continuous_id.div_const T
  exact continuous_exp.comp h1.neg

/-- The exponential moment identity behind the memory estimate: the
truncated integral of the lag-weight `u e^{-u/T}` equals
`T² (1 - (1 + R/T) e^{-R/T})`. -/
theorem lag_exp_integral (T R : ℝ) (hT : 0 < T) (_hR : 0 ≤ R) :
    ∫ u in (0:ℝ)..R, u * Real.exp (-(u / T))
      = T ^ 2 * (1 - (1 + R / T) * Real.exp (-(R / T))) := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) R,
      HasDerivAt (fun v => -(T * (T + v) * Real.exp (-(v / T))))
        (u * Real.exp (-(u / T))) u := by
    intro u _
    have h := (hasDerivAt_id u).div_const T
    have hd : HasDerivAt (fun v => -(v / T)) (-(1 / T)) u :=
      h.neg.congr_deriv (by field_simp [hT.ne'])
    have hexpd : HasDerivAt (fun v => Real.exp (-(v / T)))
        (Real.exp (-(u / T)) * (-(1 / T))) u :=
      (hasDerivAt_exp _).comp u hd
    have hplus : HasDerivAt (fun v => T + v) 1 u :=
      (hasDerivAt_id u).const_add T
    have hinner : HasDerivAt (fun v => T * (T + v) * Real.exp (-(v / T)))
        (T * 1 * Real.exp (-(u / T))
          + T * (T + u) * (Real.exp (-(u / T)) * (-(1 / T)))) u :=
      HasDerivAt.mul (HasDerivAt.const_mul T hplus) hexpd
    have hfull := hinner.neg
    refine hfull.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun u => u * Real.exp (-(u / T)))
      MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable (continuous_id.mul (exp_weight_cont T)) (0:ℝ) R
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show -((0:ℝ) / T) = 0 from by simp, exp_zero]
  field_simp [hT.ne']
  ring

/-- The memory-free truncation of the pure exponential kernel. -/
theorem exp_integral (T R : ℝ) (hT : 0 < T) :
    ∫ u in (0:ℝ)..R, Real.exp (-(u / T))
      = T * (1 - Real.exp (-(R / T))) := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) R,
      HasDerivAt (fun v => -(T * Real.exp (-(v / T)))) (Real.exp (-(u / T))) u := by
    intro u _
    have h := (hasDerivAt_id u).div_const T
    have hd : HasDerivAt (fun v => -(v / T)) (-(1 / T)) u :=
      h.neg.congr_deriv (by field_simp [hT.ne'])
    have hexpd : HasDerivAt (fun v => Real.exp (-(v / T)))
        (Real.exp (-(u / T)) * (-(1 / T))) u :=
      (hasDerivAt_exp _).comp u hd
    have hfull := (HasDerivAt.const_mul T hexpd).neg
    refine hfull.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun u => Real.exp (-(u / T)))
      MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable (exp_weight_cont T) (0:ℝ) R
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show -((0:ℝ) / T) = 0 from by simp, exp_zero]
  ring

/-- Quantitative low-memory reduction, the content of the step from
equation (14) to equation (15): if the lag kernel `κ` is Lipschitz in the
lag with constant `Λ` on `[0, R]`, then the truncated memory integral of
`κ` against the exponential memory weight deviates from the memory-free
value `κ(0) T (1 - e^{-R/T})` by at most
`Λ T² (1 - (1 + R/T) e^{-R/T})`, which is bounded by `Λ T²`. -/
theorem memory_integral_bound (T R Λ : ℝ) (hT : 0 < T) (hR : 0 ≤ R) (κ : ℝ → ℝ)
    (_hΛ : 0 ≤ Λ) (hc : Continuous κ)
    (hlip : ∀ u ∈ Set.Icc (0:ℝ) R, |κ u - κ 0| ≤ Λ * u) :
    |(∫ u in (0:ℝ)..R, κ u * Real.exp (-(u / T)))
        - κ 0 * (T * (1 - Real.exp (-(R / T))))|
      ≤ Λ * T ^ 2 * (1 - (1 + R / T) * Real.exp (-(R / T))) := by
  have hintκ : IntervalIntegrable (fun u => κ u * Real.exp (-(u / T)))
      MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable (hc.mul (exp_weight_cont T)) (0:ℝ) R
  have hintκ0 : IntervalIntegrable (fun u => κ 0 * Real.exp (-(u / T)))
      MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable (continuous_const.mul (exp_weight_cont T)) (0:ℝ) R
  have hintD : IntervalIntegrable
      (fun u => (κ u - κ 0) * Real.exp (-(u / T))) MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable ((hc.sub continuous_const).mul (exp_weight_cont T))
      (0:ℝ) R
  have hintL : IntervalIntegrable
      (fun u => Λ * u * Real.exp (-(u / T))) MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable
      ((continuous_const.mul continuous_id).mul (exp_weight_cont T)) (0:ℝ) R
  have hintneg : IntervalIntegrable
      (fun u => -(Λ * u * Real.exp (-(u / T)))) MeasureTheory.volume (0:ℝ) R :=
    Continuous.intervalIntegrable
      (((continuous_const.mul continuous_id).mul (exp_weight_cont T)).neg) (0:ℝ) R
  have hsplit : ∫ u in (0:ℝ)..R, κ u * Real.exp (-(u / T))
      = (∫ u in (0:ℝ)..R, κ 0 * Real.exp (-(u / T)))
        + (∫ u in (0:ℝ)..R, (κ u - κ 0) * Real.exp (-(u / T))) := by
    have h1 := integral_add (a := (0:ℝ)) (b := R) hintκ0 hintD
    rw [← h1]
    exact integral_congr (fun u _ => by ring)
  have hlow : ∀ u ∈ Set.Icc (0:ℝ) R,
      -(Λ * u * Real.exp (-(u / T))) ≤ (κ u - κ 0) * Real.exp (-(u / T)) := by
    intro u hu
    have h1 := (abs_le.1 (hlip u hu)).1
    have h2 : (0:ℝ) ≤ Real.exp (-(u / T)) := (exp_pos _).le
    have hleft : -(Λ * u) * Real.exp (-(u / T)) ≤ (κ u - κ 0) * Real.exp (-(u / T)) :=
      mul_le_mul_of_nonneg_right h1 h2
    have hconv : -(Λ * u * Real.exp (-(u / T))) = -(Λ * u) * Real.exp (-(u / T)) := by ring
    rwa [hconv]
  have hup : ∀ u ∈ Set.Icc (0:ℝ) R,
      (κ u - κ 0) * Real.exp (-(u / T)) ≤ Λ * u * Real.exp (-(u / T)) := by
    intro u hu
    have h1 := (abs_le.1 (hlip u hu)).2
    have h2 : (0:ℝ) ≤ Real.exp (-(u / T)) := (exp_pos _).le
    exact mul_le_mul_of_nonneg_right h1 h2
  have m1 := integral_mono_on hR hintneg hintD hlow
  have m2 := integral_mono_on hR hintD hintL hup
  have hnegint : ∫ u in (0:ℝ)..R, -(Λ * u * Real.exp (-(u / T)))
      = -(∫ u in (0:ℝ)..R, Λ * u * Real.exp (-(u / T))) := integral_neg ..
  have hLval := lag_exp_integral T R hT hR
  have habs : |∫ u in (0:ℝ)..R, (κ u - κ 0) * Real.exp (-(u / T))|
      ≤ Λ * T ^ 2 * (1 - (1 + R / T) * Real.exp (-(R / T))) := by
    rw [hnegint] at m1
    have hΛint : ∫ u in (0:ℝ)..R, Λ * u * Real.exp (-(u / T))
        = Λ * ∫ u in (0:ℝ)..R, u * Real.exp (-(u / T)) := by
      rw [← intervalIntegral.integral_const_mul Λ (fun u => u * Real.exp (-(u / T)))]
      exact integral_congr (fun u _ => by ring)
    have hfin : ∫ u in (0:ℝ)..R, Λ * u * Real.exp (-(u / T))
        ≤ Λ * T ^ 2 * (1 - (1 + R / T) * Real.exp (-(R / T))) := by
      rw [hΛint, hLval]
      exact le_of_eq (by ring)
    exact le_trans (abs_le.2 ⟨m1, m2⟩) hfin
  have hconst : ∫ u in (0:ℝ)..R, κ 0 * Real.exp (-(u / T))
      = κ 0 * (T * (1 - Real.exp (-(R / T)))) := by
    rw [intervalIntegral.integral_const_mul (κ 0) (fun u => Real.exp (-(u / T))),
      exp_integral T R hT]
  have hkey : (∫ u in (0:ℝ)..R, κ u * Real.exp (-(u / T)))
      - κ 0 * (T * (1 - Real.exp (-(R / T))))
      = ∫ u in (0:ℝ)..R, (κ u - κ 0) * Real.exp (-(u / T)) := by
    rw [hsplit, hconst]
    ring
  rw [hkey]
  exact habs

/-- A continuous function nonnegative on the nonnegative ray has a finite
integral there if its integrals over the finite initial intervals converge. -/
private theorem integrableOn_Ioi_of_nonneg_interval_limit {f : ℝ → ℝ} {I : ℝ}
    (hc : Continuous f) (hn : ∀ u ≥ 0, 0 ≤ f u)
    (ht : Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..R, f u) atTop (𝓝 I)) :
    IntegrableOn f (Set.Ioi 0) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto I 0
    (fun R : ℝ => (hc.intervalIntegrable 0 R).1) tendsto_id ?_
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hR] at hu
  exact (Real.norm_of_nonneg (hn u hu.1)).symm

/-- The exponential memory weight has total mass `T` on the entire lag
half-line. -/
theorem exp_weight_Ioi (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun u => Real.exp (-(u / T))) (Set.Ioi 0) ∧
      (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u / T))) = T := by
  have hscale : Tendsto (fun R : ℝ => R / T) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hT).2 tendsto_id
  have htail := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have ht : Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..R, Real.exp (-(u / T))) atTop (𝓝 T) := by
    simp only [exp_integral T _ hT]
    simpa using (htail.const_sub 1).const_mul T
  have hi := integrableOn_Ioi_of_nonneg_interval_limit (exp_weight_cont T)
    (fun u _ => (Real.exp_pos (-(u / T))).le) ht
  exact ⟨hi, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id) ht⟩

/-- The first lag moment of the full exponential memory weight is `T²`. -/
theorem lag_exp_Ioi (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun u => u * Real.exp (-(u / T))) (Set.Ioi 0) ∧
      (∫ u in Set.Ioi (0 : ℝ), u * Real.exp (-(u / T))) = T ^ 2 := by
  have hscale : Tendsto (fun R : ℝ => R / T) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hT).2 tendsto_id
  have htail := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hmoment := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hsum : Tendsto (fun R : ℝ => (1 + R / T) * Real.exp (-(R / T))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, ← one_add_mul, zero_add]
      using htail.add hmoment
  have ht : Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..R, u * Real.exp (-(u / T))) atTop
      (𝓝 (T ^ 2)) := by
    have h : Tendsto (fun R : ℝ => T ^ 2 * (1 - (1 + R / T) * Real.exp (-(R / T))))
        atTop (𝓝 (T ^ 2)) := by
      simpa using (hsum.const_sub 1).const_mul (T ^ 2)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (lag_exp_integral T R hT hR).symm
  have hi := integrableOn_Ioi_of_nonneg_interval_limit (continuous_id.mul (exp_weight_cont T))
    (fun u hu => mul_nonneg hu (Real.exp_pos (-(u / T))).le) ht
  exact ⟨hi, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id) ht⟩

/-- The full past-history integral exists and differs from the instantaneous
term `T κ(0)` by at most `Λ T²` when the lag kernel changes from its
instantaneous value at a rate bounded by `Λ`. This controls the absolute
error without a finite-history cutoff. -/
theorem full_memory_integral_bound_of_measurable (T Λ : ℝ) (hT : 0 < T) (κ : ℝ → ℝ)
    (hc : Measurable κ) (hlip : ∀ u ≥ 0, |κ u - κ 0| ≤ Λ * u) :
    IntegrableOn (fun u => κ u * Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), κ u * Real.exp (-(u / T))) - κ 0 * T| ≤ Λ * T ^ 2 := by
  obtain ⟨hweight, hweight_val⟩ := exp_weight_Ioi T hT
  obtain ⟨hlag, hlag_val⟩ := lag_exp_Ioi T hT
  have hdiff : IntegrableOn (fun u => (κ u - κ 0) * Real.exp (-(u / T))) (Set.Ioi 0) := by
    refine (hlag.const_mul Λ).mono'
      (((hc.sub measurable_const).mul (exp_weight_cont T).measurable).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hlip u (le_of_lt hu)) (Real.exp_pos _).le
  have hconst := hweight.const_mul (κ 0)
  have hk : IntegrableOn (fun u => κ u * Real.exp (-(u / T))) (Set.Ioi 0) := by
    refine (hdiff.add hconst).congr (Filter.Eventually.of_forall fun u => ?_)
    change (κ u - κ 0) * Real.exp (-(u / T)) + κ 0 * Real.exp (-(u / T)) =
      κ u * Real.exp (-(u / T))
    ring
  refine ⟨hk, ?_⟩
  have hsubtract :
      (∫ u in Set.Ioi (0 : ℝ), (κ u - κ 0) * Real.exp (-(u / T))) =
        (∫ u in Set.Ioi (0 : ℝ), κ u * Real.exp (-(u / T))) - κ 0 * T := by
    simp_rw [sub_mul]
    rw [MeasureTheory.integral_sub hk hconst, MeasureTheory.integral_const_mul, hweight_val]
  rw [← hsubtract]
  apply MeasureTheory.abs_integral_le_integral_abs.trans
  have hmono :
      (∫ u in Set.Ioi (0 : ℝ), |(κ u - κ 0) * Real.exp (-(u / T))|) ≤
        ∫ u in Set.Ioi (0 : ℝ), Λ * (u * Real.exp (-(u / T))) := by
    apply integral_mono_ae hdiff.abs (hlag.const_mul Λ)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hlip u (le_of_lt hu)) (Real.exp_pos _).le
  rwa [MeasureTheory.integral_const_mul, hlag_val] at hmono

/-- The full memory integral estimate for a continuous lag profile. -/
theorem full_memory_integral_bound (T Λ : ℝ) (hT : 0 < T) (κ : ℝ → ℝ)
    (hc : Continuous κ) (hlip : ∀ u ≥ 0, |κ u - κ 0| ≤ Λ * u) :
    IntegrableOn (fun u => κ u * Real.exp (-(u / T))) (Set.Ioi 0) ∧
      |(∫ u in Set.Ioi (0 : ℝ), κ u * Real.exp (-(u / T))) - κ 0 * T| ≤ Λ * T ^ 2 :=
  full_memory_integral_bound_of_measurable T Λ hT κ hc.measurable hlip

/-- Per unit memory mass, the history average differs from the instantaneous
lag value by at most `Λ T`. -/
theorem memory_average_error_of_measurable (T Λ : ℝ) (hT : 0 < T) (κ : ℝ → ℝ)
    (hc : Measurable κ) (hlip : ∀ u ≥ 0, |κ u - κ 0| ≤ Λ * u) :
    |(∫ u in Set.Ioi (0 : ℝ), κ u * Real.exp (-(u / T))) / T - κ 0| ≤ Λ * T := by
  let I := ∫ u in Set.Ioi (0 : ℝ), κ u * Real.exp (-(u / T))
  have h := (full_memory_integral_bound_of_measurable T Λ hT κ hc hlip).2
  change |I - κ 0 * T| ≤ Λ * T ^ 2 at h
  change |I / T - κ 0| ≤ Λ * T
  have hquot : I / T - κ 0 = (I - κ 0 * T) / T := by
    rw [sub_div, mul_div_cancel_right₀ _ hT.ne']
  calc
    |I / T - κ 0| = |I - κ 0 * T| / T := by
      rw [hquot, abs_div, abs_of_pos hT]
    _ ≤ Λ * T ^ 2 / T := div_le_div_of_nonneg_right h hT.le
    _ = Λ * T := by field_simp

/-- The normalized memory estimate for a continuous lag profile. -/
theorem memory_average_error (T Λ : ℝ) (hT : 0 < T) (κ : ℝ → ℝ)
    (hc : Continuous κ) (hlip : ∀ u ≥ 0, |κ u - κ 0| ≤ Λ * u) :
    |(∫ u in Set.Ioi (0 : ℝ), κ u * Real.exp (-(u / T))) / T - κ 0| ≤ Λ * T :=
  memory_average_error_of_measurable T Λ hT κ hc.measurable hlip

end Qatlib.Papers.HydroSpinLatt21.BesselModel

end
