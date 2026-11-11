/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.MatrixODE

/-!
# Wave and Bessel propagator equations

This module defines `wavePropagator` and `besselPropagator` by entire power series in a complete
complex normed algebra. It differentiates their time series to establish the wave and order-zero
Bessel equations and the initial conditions used in the matrix dynamics of [WangEtAl2026].

## Main statements

* `wavePropagator_ode`: the complex wave equation.
* `besselPropagator_real_ode`: the real Bessel equation away from zero.
* `matrix_bessel_initial_value_problem`: matrix initial conditions and regularity.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section
namespace CBMD
open Complex Metric Set Filter
open scoped Topology

section VectorSeries
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The formal multilinear series associated with a sequence of vector coefficients. -/
private def vectorSeries (c : ℕ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)

omit [CompleteSpace E] in
/-- The coefficient of `vectorSeries c` at degree `n` is `c n`. -/
private theorem vectorSeries_coeff (c : ℕ → E) (n : ℕ) :
    (vectorSeries c).coeff n = c n := by
  simp [vectorSeries, FormalMultilinearSeries.coeff]

/-- A vector power series summable at every complex argument represents its sum on the ball of
infinite radius about zero. -/
private theorem vectorSeries_entire (c : ℕ → E)
    (hc : ∀ z : ℂ, Summable (fun n => z ^ n • c n)) :
    HasFPowerSeriesOnBall (fun z : ℂ => ∑' n, z ^ n • c n)
      (vectorSeries c) 0 ⊤ := by
  have hr : (vectorSeries c).radius = ⊤ := by
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    apply FormalMultilinearSeries.le_radius_of_tendsto (vectorSeries c) (l := 0)
    have ht := (hc (r : ℂ)).tendsto_atTop_zero.norm
    simpa [vectorSeries, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg r.coe_nonneg, mul_comm] using ht
  have hh := (vectorSeries c).hasFPowerSeriesOnBall (by rw [hr]; exact ENNReal.zero_lt_top)
  rw [hr] at hh
  convert! hh using 1
  ext z
  simp [FormalMultilinearSeries.sum, vectorSeries_coeff]

/-- The formal series obtained by differentiating a one-variable multilinear power series. -/
private def univDerivSeries (p : FormalMultilinearSeries ℂ ℂ E) :
    FormalMultilinearSeries ℂ ℂ E :=
  (ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries p.derivSeries

omit [CompleteSpace E] in
/-- The degree `n` coefficient of the derivative series is `(n + 1) • p.coeff (n + 1)`. -/
private theorem univDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ E) (n : ℕ) :
    (univDerivSeries p).coeff n = (n + 1) • p.coeff (n + 1) := by
  change p.derivSeries.coeff n 1 = _
  exact p.derivSeries_coeff_one n

/-- Differentiating an entire power series yields the entire power series `univDerivSeries p`. -/
private theorem hasPowerSeries_deriv {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E}
    (h : HasFPowerSeriesOnBall f p 0 ⊤) :
    HasFPowerSeriesOnBall (deriv f) (univDerivSeries p) 0 ⊤ := by
  exact (ContinuousLinearMap.apply ℂ E (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv

/-- The twice differentiated vector power series sums to the second derivative, with coefficient
`(n + 1) • ((n + 2) • c (n + 2))`. -/
private theorem vectorSeries_hasSum_second_deriv (c : ℕ → E)
    (hc : ∀ z : ℂ, Summable (fun n => z ^ n • c n)) (z : ℂ) :
    HasSum (fun n => z ^ n • ((n + 1) • ((n + 2) • c (n + 2))))
      (deriv (deriv (fun w : ℂ => ∑' n, w ^ n • c n)) z) := by
  have h := hasPowerSeries_deriv (hasPowerSeries_deriv (vectorSeries_entire c hc))
  have hs := h.hasSum (y := z) (by exact edist_lt_top _ _)
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    univDerivSeries_coeff, vectorSeries_coeff, Nat.add_assoc] using hs

omit [CompleteSpace E] in
/-- A complex derivative at a real point also gives the derivative of the restriction to real
arguments. -/
theorem vector_hasDerivAt_comp_ofReal [NormedSpace ℝ E] {f : ℂ → E} {f' : E} {t : ℝ}
    (h : HasDerivAt f f' (t : ℂ)) :
    HasDerivAt (fun x : ℝ => f (x : ℂ)) f' t := by
  simpa using! ((h.hasFDerivAt.restrictScalars ℝ).comp t
    Complex.ofRealCLM.hasFDerivAt).hasDerivAt

end VectorSeries

section Wave
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- The wave propagator defined by the entire series with terms `((2 * n)! : ℂ)⁻¹ • (-(t²) •
A)^n`. -/
def wavePropagator (A : E) (t : ℂ) : E :=
  ∑' n : ℕ, (((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n

/-- The coefficient of the wave propagator's time series, with vanishing odd coefficients. -/
private def waveTimeCoefficient (A : E) (n : ℕ) : E :=
  if n % 2 = 0 then (n.factorial : ℂ)⁻¹ • (-A) ^ (n / 2) else 0

omit [CompleteSpace E] in

/-- The even wave coefficient is the reciprocal factorial multiple of `(-A)^n`. -/
private theorem waveTimeCoefficient_mul (A : E) (n : ℕ) :
    waveTimeCoefficient A (2 * n) = (((2 * n).factorial : ℂ)⁻¹) • (-A) ^ n := by
  simp [waveTimeCoefficient]

omit [CompleteSpace E] in

/-- Rewrites an even time-series term as the corresponding term in the defining wave series. -/
private theorem wave_time_term (A : E) (t : ℂ) (n : ℕ) :
    t ^ (2 * n) • waveTimeCoefficient A (2 * n) =
      (((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n := by
  rw [waveTimeCoefficient_mul,
    show -(t ^ 2) • A = t ^ 2 • (-A) by simp,
    smul_pow, ← pow_mul, smul_comm]

/-- The time power series with coefficients `waveTimeCoefficient A` sums to `wavePropagator A
t`. -/
private theorem wave_time_hasSum (A : E) (t : ℂ) :
    HasSum (fun n => t ^ n • waveTimeCoefficient A n) (wavePropagator A t) := by
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    change 2 * a = 2 * b at h
    omega
  apply (hi.hasSum_iff ?_).mp
  · change HasSum (fun n => t ^ (2 * n) • waveTimeCoefficient A (2 * n)) _
    simpa only [wave_time_term] using! (wave_series_summable A t).hasSum
  · intro n hn
    have hm : n % 2 ≠ 0 := by
      intro h
      apply hn
      exact ⟨n / 2, by change 2 * (n / 2) = n; omega⟩
    simp [waveTimeCoefficient, hm]

/-- The wave propagator is the sum of its time power series. -/
private theorem wavePropagator_timeSeries (A : E) :
    wavePropagator A = fun t => ∑' n, t ^ n • waveTimeCoefficient A n := by
  funext t
  exact (wave_time_hasSum A t).tsum_eq.symm

omit [CompleteSpace E] in

/-- The wave time coefficients satisfy the recurrence corresponding to the equation `G'' + A * G
= 0`. -/
private theorem waveTimeCoefficient_step (A : E) (n : ℕ) :
    (n + 1) • ((n + 2) • waveTimeCoefficient A (n + 2)) =
      -A * waveTimeCoefficient A n := by
  by_cases hm : n % 2 = 0
  · have hm' : (n + 2) % 2 = 0 := by omega
    simp only [waveTimeCoefficient, hm, hm', if_true,
      show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ',
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_smul_comm]
    congr 1
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have h0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have h2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 + 1 ≠ 0)
    field_simp
  · simp [waveTimeCoefficient, hm]

/-- The wave propagator is analytic at every complex time. -/
theorem wavePropagator_analytic (A : E) (t : ℂ) : AnalyticAt ℂ (wavePropagator A) t := by
  rw [wavePropagator_timeSeries]
  exact (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_entire (waveTimeCoefficient A)
    (fun z => (wave_time_hasSum A z).summable)).analyticAt_of_mem (edist_lt_top _ _)

omit [CompleteSpace E] in

/-- The wave propagator at time zero is the multiplicative identity. -/
@[simp] theorem wavePropagator_zero (A : E) : wavePropagator A 0 = 1 := by
  simp [wavePropagator, ← FormalMultilinearSeries.ofScalars_sum_eq]

/-- The wave propagator has derivative zero at time zero. -/
theorem wavePropagator_hasDerivAt_zero (A : E) : HasDerivAt (wavePropagator A) 0 0 := by
  rw [wavePropagator_timeSeries]
  have h := (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_entire (waveTimeCoefficient A)
    (fun z => (wave_time_hasSum A z).summable)).hasFPowerSeriesAt.hasDerivAt
  simpa [Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_coeff, waveTimeCoefficient] using h

/-- The derivative of the wave propagator vanishes at zero. -/
@[simp] theorem wavePropagator_deriv_zero (A : E) : deriv (wavePropagator A) 0 = 0 :=
  (wavePropagator_hasDerivAt_zero A).deriv

/-- The wave propagator satisfies the complex differential equation `G'' + A * G = 0`. -/
theorem wavePropagator_ode (A : E) (t : ℂ) :
    deriv (deriv (wavePropagator A)) t + A * wavePropagator A t = 0 := by
  have hs := Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_hasSum_second_deriv (waveTimeCoefficient A)
    (fun z => (wave_time_hasSum A z).summable) t
  rw [← wavePropagator_timeSeries] at hs
  have ht := (wave_time_hasSum A t).mul_left (-A)
  have hterm : (fun n => t ^ n • ((n + 1) • ((n + 2) • waveTimeCoefficient A (n + 2)))) =
      (fun n => -A * (t ^ n • waveTimeCoefficient A n)) := by
    funext n
    rw [waveTimeCoefficient_step, mul_smul_comm]
  rw [hterm] at hs
  rw [hs.unique ht]
  simp

/-- The derivative of the wave propagator has derivative `-(A * wavePropagator A t)`. -/
theorem wavePropagator_hasDerivAt_deriv (A : E) (t : ℂ) :
    HasDerivAt (deriv (wavePropagator A)) (-(A * wavePropagator A t)) t := by
  have h := (wavePropagator_analytic A t).deriv.differentiableAt.hasDerivAt
  convert! h using 1
  exact (eq_neg_of_add_eq_zero_left (wavePropagator_ode A t)).symm

section RealTime
variable [NormedSpace ℝ E]

/-- The derivative of the wave propagator restricted to real times equals its complex
derivative. -/
theorem wavePropagator_real_deriv_eq (A : E) (t : ℝ) :
    deriv (fun x : ℝ => wavePropagator A (x : ℂ)) t =
      deriv (wavePropagator A) (t : ℂ) :=
  (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
    (wavePropagator_analytic A (t : ℂ)).differentiableAt.hasDerivAt).deriv

/-- The wave propagator restricted to real times has derivative zero at zero. -/
theorem wavePropagator_real_hasDerivAt_zero (A : E) :
    HasDerivAt (fun x : ℝ => wavePropagator A (x : ℂ)) 0 0 := by
  exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
      (by simpa using wavePropagator_hasDerivAt_zero A)

/-- The real-time derivative of the wave propagator has derivative `-(A * wavePropagator A (t :
ℂ))`. -/
theorem wavePropagator_real_hasDerivAt_deriv (A : E) (t : ℝ) :
    HasDerivAt (deriv (fun x : ℝ => wavePropagator A (x : ℂ)))
      (-(A * wavePropagator A (t : ℂ))) t := by
  have he : deriv (fun x : ℝ => wavePropagator A (x : ℂ)) =
      fun x : ℝ => deriv (wavePropagator A) (x : ℂ) :=
    funext (wavePropagator_real_deriv_eq A)
  rw [he]
  exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
      (wavePropagator_hasDerivAt_deriv A (t : ℂ))

/-- The real-time wave propagator satisfies `G'' + A * G = 0`. -/
theorem wavePropagator_real_ode (A : E) (t : ℝ) :
    deriv (deriv (fun x : ℝ => wavePropagator A (x : ℂ))) t +
      A * wavePropagator A (t : ℂ) = 0 := by
  rw [(wavePropagator_real_hasDerivAt_deriv A t).deriv]
  exact neg_add_cancel _

end RealTime
end Wave
section Bessel
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- The Bessel propagator defined by the entire series with terms `(n! : ℂ)⁻² • ((-(t²) / 4) •
A)^n`. -/
def besselPropagator (A : E) (t : ℂ) : E :=
  ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) ^ 2 • ((-(t ^ 2) / 4) • A) ^ n

/-- The coefficient of the Bessel propagator's time series, with vanishing odd coefficients. -/
private def besselTimeCoefficient (A : E) (n : ℕ) : E :=
  if n % 2 = 0 then ((((n / 2).factorial : ℂ)⁻¹) ^ 2) •
    ((-1 / 4 : ℂ) • A) ^ (n / 2) else 0

omit [CompleteSpace E] in

/-- The even Bessel coefficient is `(n! : ℂ)⁻² • ((-1 / 4 : ℂ) • A)^n`. -/
private theorem besselTimeCoefficient_mul (A : E) (n : ℕ) :
    besselTimeCoefficient A (2 * n) = ((n.factorial : ℂ)⁻¹) ^ 2 •
      ((-1 / 4 : ℂ) • A) ^ n := by
  simp [besselTimeCoefficient]

omit [CompleteSpace E] in

/-- Rewrites an even time-series term as the corresponding term in the defining Bessel series. -/
private theorem bessel_time_term (A : E) (t : ℂ) (n : ℕ) :
    t ^ (2 * n) • besselTimeCoefficient A (2 * n) =
      ((n.factorial : ℂ)⁻¹) ^ 2 • ((-(t ^ 2) / 4) • A) ^ n := by
  rw [besselTimeCoefficient_mul,
    show (-(t ^ 2) / 4) • A = t ^ 2 • ((-1 / 4 : ℂ) • A) by
      rw [smul_smul]; congr 1; ring,
    smul_pow (t ^ 2) ((-1 / 4 : ℂ) • A) n, ← pow_mul, smul_comm]

/-- The time power series with coefficients `besselTimeCoefficient A` sums to `besselPropagator
A t`. -/
private theorem bessel_time_hasSum (A : E) (t : ℂ) :
    HasSum (fun n => t ^ n • besselTimeCoefficient A n) (besselPropagator A t) := by
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    change 2 * a = 2 * b at h
    omega
  apply (hi.hasSum_iff ?_).mp
  · change HasSum (fun n => t ^ (2 * n) • besselTimeCoefficient A (2 * n)) _
    simpa only [bessel_time_term] using! (bessel_series_summable A t).hasSum
  · intro n hn
    have hm : n % 2 ≠ 0 := by
      intro h
      apply hn
      exact ⟨n / 2, by change 2 * (n / 2) = n; omega⟩
    simp [besselTimeCoefficient, hm]

/-- The Bessel propagator is the sum of its time power series. -/
private theorem besselPropagator_timeSeries (A : E) :
    besselPropagator A = fun t => ∑' n, t ^ n • besselTimeCoefficient A n := by
  funext t
  exact (bessel_time_hasSum A t).tsum_eq.symm

omit [CompleteSpace E] in

/-- The Bessel time coefficients satisfy the recurrence corresponding to the order-zero Bessel
equation. -/
private theorem besselTimeCoefficient_step (A : E) (n : ℕ) :
    (n + 2) • ((n + 2) • besselTimeCoefficient A (n + 2)) =
      -A * besselTimeCoefficient A n := by
  by_cases hm : n % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [show 2 * k + 2 = 2 * (k + 1) by omega,
      besselTimeCoefficient_mul, besselTimeCoefficient_mul,
      pow_succ' ((-1 / 4 : ℂ) • A) k]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_mul_assoc, smul_smul,
      mul_smul_comm, neg_mul, smul_neg, ← neg_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    have h0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
    field_simp
    ring
  · simp [besselTimeCoefficient, hm]

/-- The Bessel propagator is analytic at every complex time. -/
theorem besselPropagator_analytic (A : E) (t : ℂ) : AnalyticAt ℂ (besselPropagator A) t := by
  rw [besselPropagator_timeSeries]
  exact (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_entire (besselTimeCoefficient A)
    (fun z => (bessel_time_hasSum A z).summable)).analyticAt_of_mem (edist_lt_top _ _)

omit [CompleteSpace E] in

/-- The Bessel propagator at time zero is the multiplicative identity. -/
@[simp] theorem besselPropagator_zero (A : E) : besselPropagator A 0 = 1 := by
  simp [besselPropagator, ← FormalMultilinearSeries.ofScalars_sum_eq]

/-- The Bessel propagator has derivative zero at time zero. -/
theorem besselPropagator_hasDerivAt_zero (A : E) : HasDerivAt (besselPropagator A) 0 0 := by
  rw [besselPropagator_timeSeries]
  have h := (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_entire (besselTimeCoefficient A)
    (fun z => (bessel_time_hasSum A z).summable)).hasFPowerSeriesAt.hasDerivAt
  simpa [Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_coeff, besselTimeCoefficient] using
      h

/-- The derivative of the Bessel propagator vanishes at zero. -/
@[simp] theorem besselPropagator_deriv_zero (A : E) : deriv (besselPropagator A) 0 = 0 :=
  (besselPropagator_hasDerivAt_zero A).deriv

/-- The differentiated Bessel time series sums to the derivative of the Bessel propagator. -/
private theorem bessel_deriv_hasSum (A : E) (t : ℂ) :
    HasSum (fun n => t ^ n • ((n + 1) • besselTimeCoefficient A (n + 1)))
      (deriv (besselPropagator A) t) := by
  have h := Qatlib.Foundations.CbmdAnalysis.Core.CBMD.hasPowerSeries_deriv (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_entire (besselTimeCoefficient A)
    (fun z => (bessel_time_hasSum A z).summable))
  have hs := h.hasSum (y := t) (by exact edist_lt_top _ _)
  rw [← besselPropagator_timeSeries] at hs
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    Qatlib.Foundations.CbmdAnalysis.Core.CBMD.univDerivSeries_coeff, Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_coeff] using hs

/-- At nonzero complex time, the Bessel propagator satisfies `G'' + t⁻¹ • G' + A * G = 0`. -/
theorem besselPropagator_ode (A : E) (t : ℂ) (ht : t ≠ 0) :
    deriv (deriv (besselPropagator A)) t + t⁻¹ • deriv (besselPropagator A) t +
      A * besselPropagator A t = 0 := by
  have hs2 := Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vectorSeries_hasSum_second_deriv (besselTimeCoefficient A)
    (fun z => (bessel_time_hasSum A z).summable) t
  rw [← besselPropagator_timeSeries] at hs2
  have hs1 := (hasSum_nat_add_iff'
    (f := fun n => t ^ n • ((n + 1) • besselTimeCoefficient A (n + 1)))
    (g := deriv (besselPropagator A) t) 1).mpr (bessel_deriv_hasSum A t)
  have hzero : besselTimeCoefficient A (0 + 1) = 0 := by simp [besselTimeCoefficient]
  simp only [Finset.sum_range_one, hzero, smul_zero, sub_zero, Nat.add_assoc] at hs1
  have hs1' : HasSum (fun n => t ^ n • ((n + 2) • besselTimeCoefficient A (n + 2)))
      (t⁻¹ • deriv (besselPropagator A) t) := by
    convert! hs1.const_smul t⁻¹ using 1
    funext n
    simp only [pow_succ, smul_smul]
    rw [mul_comm (t ^ n) t, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  have hsum := hs2.add hs1'
  have hterm : (fun n => t ^ n • ((n + 1) • ((n + 2) • besselTimeCoefficient A (n + 2))) +
      t ^ n • ((n + 2) • besselTimeCoefficient A (n + 2))) =
      (fun n => -A * (t ^ n • besselTimeCoefficient A n)) := by
    funext n
    rw [← smul_add]
    rw [← succ_nsmul, show n + 1 + 1 = n + 2 by omega,
      besselTimeCoefficient_step, mul_smul_comm]
  rw [hterm] at hsum
  rw [hsum.unique ((bessel_time_hasSum A t).mul_left (-A))]
  simp

/-- At nonzero complex time, the derivative of the Bessel propagator has derivative `-(t⁻¹ • G'
+ A * G)`. -/
theorem besselPropagator_hasDerivAt_deriv (A : E) (t : ℂ) (ht : t ≠ 0) :
    HasDerivAt (deriv (besselPropagator A))
      (-(t⁻¹ • deriv (besselPropagator A) t + A * besselPropagator A t)) t := by
  have h := (besselPropagator_analytic A t).deriv.differentiableAt.hasDerivAt
  convert! h using 1
  have he := besselPropagator_ode A t ht
  rw [add_assoc] at he
  exact (eq_neg_of_add_eq_zero_left he).symm

section RealTime
variable [NormedSpace ℝ E]

/-- The derivative of the Bessel propagator restricted to real times equals its complex
derivative. -/
theorem besselPropagator_real_deriv_eq (A : E) (t : ℝ) :
    deriv (fun x : ℝ => besselPropagator A (x : ℂ)) t =
      deriv (besselPropagator A) (t : ℂ) :=
  (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
    (besselPropagator_analytic A (t : ℂ)).differentiableAt.hasDerivAt).deriv

/-- The Bessel propagator restricted to real times has derivative zero at zero. -/
theorem besselPropagator_real_hasDerivAt_zero (A : E) :
    HasDerivAt (fun x : ℝ => besselPropagator A (x : ℂ)) 0 0 := by
  exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
      (by simpa using besselPropagator_hasDerivAt_zero A)

/-- The real-time Bessel propagator and its first derivative are differentiable everywhere. -/
theorem besselPropagator_real_twice_differentiable (A : E) :
    Differentiable ℝ (fun x : ℝ => besselPropagator A (x : ℂ)) ∧
      Differentiable ℝ (deriv (fun x : ℝ => besselPropagator A (x : ℂ))) := by
  constructor
  · intro t
    exact (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
      (besselPropagator_analytic A (t : ℂ)).differentiableAt.hasDerivAt).differentiableAt
  · have he : deriv (fun x : ℝ => besselPropagator A (x : ℂ)) =
        fun x : ℝ => deriv (besselPropagator A) (x : ℂ) :=
      funext (besselPropagator_real_deriv_eq A)
    rw [he]
    intro t
    exact (Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
      (besselPropagator_analytic A (t : ℂ)).deriv.differentiableAt.hasDerivAt).differentiableAt

/-- At nonzero real time, the derivative of the Bessel propagator has derivative `-(t⁻¹ • G' + A
* G)`. -/
theorem besselPropagator_real_hasDerivAt_deriv (A : E) (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (deriv (fun x : ℝ => besselPropagator A (x : ℂ)))
      (-(t⁻¹ • deriv (fun x : ℝ => besselPropagator A (x : ℂ)) t +
        A * besselPropagator A (t : ℂ))) t := by
  have he : deriv (fun x : ℝ => besselPropagator A (x : ℂ)) =
      fun x : ℝ => deriv (besselPropagator A) (x : ℂ) :=
    funext (besselPropagator_real_deriv_eq A)
  rw [he]
  simpa [← Complex.ofReal_inv] using Qatlib.Foundations.CbmdAnalysis.Core.CBMD.vector_hasDerivAt_comp_ofReal
    (besselPropagator_hasDerivAt_deriv A (t : ℂ) (Complex.ofReal_ne_zero.mpr ht))

/-- At nonzero real time, the Bessel propagator satisfies `G'' + t⁻¹ • G' + A * G = 0`. -/
theorem besselPropagator_real_ode (A : E) (t : ℝ) (ht : t ≠ 0) :
    deriv (deriv (fun x : ℝ => besselPropagator A (x : ℂ))) t +
      t⁻¹ • deriv (fun x : ℝ => besselPropagator A (x : ℂ)) t +
      A * besselPropagator A (t : ℂ) = 0 := by
  rw [(besselPropagator_real_hasDerivAt_deriv A t ht).deriv]
  abel

end RealTime
end Bessel

section Matrices
open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix wave propagator has initial value `1`, initial derivative zero, and satisfies the
wave equation at every real time. -/
theorem matrix_wave_initial_value_problem (A : Matrix n n ℂ) :
    let G : ℝ → Matrix n n ℂ := fun t => wavePropagator A (t : ℂ)
    G 0 = 1 ∧ HasDerivAt G 0 0 ∧
      ∀ t : ℝ, HasDerivAt (deriv G) (-(A * G t)) t := by
  refine ⟨?_, wavePropagator_real_hasDerivAt_zero A,
    wavePropagator_real_hasDerivAt_deriv A⟩
  simp

/-- The matrix Bessel propagator has initial value `1` and initial derivative zero, is twice
differentiable on the real line, and satisfies the Bessel equation at positive times. -/
theorem matrix_bessel_initial_value_problem (A : Matrix n n ℂ) :
    let G : ℝ → Matrix n n ℂ := fun t => besselPropagator A (t : ℂ)
    G 0 = 1 ∧ HasDerivAt G 0 0 ∧ Differentiable ℝ G ∧ Differentiable ℝ (deriv G) ∧
      ∀ t : ℝ, 0 < t → HasDerivAt (deriv G) (-(t⁻¹ • deriv G t + A * G t)) t := by
  refine ⟨?_, besselPropagator_real_hasDerivAt_zero A,
    (besselPropagator_real_twice_differentiable A).1,
    (besselPropagator_real_twice_differentiable A).2, ?_⟩
  · simp
  · intro t ht
    exact besselPropagator_real_hasDerivAt_deriv A t ht.ne'

end Matrices
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
