/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.RingTheory.Polynomial.Pochhammer
import Qatlib.Foundations.CbmdAnalysis.Core.Contour
import Qatlib.Foundations.CbmdAnalysis.Core.FiniteResidue

/-!
# Entire matrix series and finite contour identities

This module proves analyticity of affine exponentials and of scalar-coefficient power series in
a complex Banach algebra when successive coefficient norm ratios tend to zero. It applies this
criterion to the Bessel, wave, and Airy series, with `airySeriesCoefficient` supplying the Airy
coefficients.

Finite simple-pole circle identities specialize to each analytic family, including matrix
exponentials. These results supply the analytic functional calculus used by contour-based matrix
decomposition [WangEtAl2026].

## Main statements

* `scalarSeries_analytic_of_ratio_zero`: gives an entire power-series criterion.
* `airy_series_affine_analytic`: proves analyticity of the affine Airy family.
* `matrix_propagator_cbmd_circle`: evaluates the two-pole matrix exponential integral.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section

namespace CBMD

open Complex Metric Set
open Filter
open scoped Topology

section BanachAlgebra

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- In a complex Banach algebra, the function `w ↦ exp (s • (L + w • H))` is analytic at every
complex point. -/
theorem exp_affine_analytic (L H : E) (s z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => NormedSpace.exp (s • (L + w • H))) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => L + w • H) z :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) (s • (L + z • H))).comp
    (f := fun w : ℂ => s • (L + w • H))
    (ha.const_smul (c := s))

/-- The affine exponential family is complex differentiable on any set and continuous on its
closure. -/
theorem exp_affine_diffContOnCl (L H : E) (s : ℂ) (S : Set ℂ) :
    DiffContOnCl ℂ (fun w : ℂ => NormedSpace.exp (s • (L + w • H))) S := by
  apply Differentiable.diffContOnCl
  intro z
  exact (exp_affine_analytic L H s z).differentiableAt

/-- For a circle enclosing `i` and zero, the normalized integral of the affine exponential
against `i / ((z - i) z)` equals its value at `i` minus its value at zero [WangEtAl2026]. -/
theorem exp_affine_cbmd_circle (L H : E) (s c : ℂ) (R : ℝ)
    (hi : I ∈ ball c R) (hzero : (0 : ℂ) ∈ ball c R) :
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (I / ((z - I) * z)) •
          NormedSpace.exp (s • (L + z • H))) =
      NormedSpace.exp (s • (L + I • H)) - NormedSpace.exp (s • L) := by
  simpa only [zero_smul, add_zero] using
    cbmd_linear_regulator_circle (exp_affine_diffContOnCl L H s (ball c R)) hi hzero

/-- If scalar coefficients are eventually nonzero and their successive norm ratios tend to zero,
the series `∑ c n • A ^ n` is summable for every element of a complex Banach algebra. -/
theorem scalarSeries_summable_of_ratio_zero (c : ℕ → ℂ)
    (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (hratio : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) (A : E) :
    Summable (fun n : ℕ => c n • A ^ n) := by
  let p := FormalMultilinearSeries.ofScalars E c
  have hr : p.radius = ⊤ :=
    FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto E c hc hratio
  have hm : A ∈ Metric.eball (0 : E) p.radius := by
    rw [hr]
    exact edist_lt_top _ _
  simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq] using
    (p.hasSum hm).summable

/-- If scalar coefficients are eventually nonzero and their successive norm ratios tend to zero,
their algebra-valued power-series sum is analytic at every algebra element. -/
theorem scalarSeries_analytic_of_ratio_zero (c : ℕ → ℂ)
    (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (hratio : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) (A : E) :
    AnalyticAt ℂ (fun B : E => ∑' n : ℕ, c n • B ^ n) A := by
  let p := FormalMultilinearSeries.ofScalars E c
  have hr : p.radius = ⊤ :=
    FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto E c hc hratio
  have hp := p.hasFPowerSeriesOnBall (by rw [hr]; exact ENNReal.zero_lt_top)
  have hm : A ∈ Metric.eball (0 : E) p.radius := by
    rw [hr]
    exact edist_lt_top _ _
  have hh := hp.analyticAt_of_mem hm
  change AnalyticAt ℂ (FormalMultilinearSeries.ofScalarsSum c) A at hh
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum] using hh

/-- Under eventual nonvanishing and a zero limit for successive coefficient norm ratios, the
power series evaluated at `s • (L + w • H)` is analytic in `w` everywhere. -/
theorem scalarSeries_affine_analytic_of_ratio_zero (c : ℕ → ℂ)
    (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (hratio : Tendsto (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0))
    (L H : E) (s z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ∑' n : ℕ, c n • (s • (L + w • H)) ^ n) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => L + w • H) z :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact (scalarSeries_analytic_of_ratio_zero c hc hratio (s • (L + z • H))).comp
    (f := fun w : ℂ => s • (L + w • H)) (ha.const_smul (c := s))

/-- The successive norm ratio of squared reciprocal factorial coefficients equals `((n +
1)⁻¹)²`. -/
private theorem factorial_square_ratio (n : ℕ) :
    ‖(((n + 1).factorial : ℂ)⁻¹) ^ 2‖ / ‖((n.factorial : ℂ)⁻¹) ^ 2‖ =
      (((n : ℝ) + 1)⁻¹) ^ 2 := by
  simp only [norm_pow, norm_inv, Complex.norm_natCast]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The successive norm ratios of squared reciprocal factorial coefficients tend to zero. -/
private theorem factorial_square_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖((n.succ.factorial : ℂ)⁻¹) ^ 2‖ /
      ‖((n.factorial : ℂ)⁻¹) ^ 2‖) atTop (𝓝 0) := by
  simp_rw [Nat.succ_eq_add_one, factorial_square_ratio]
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using ht.pow 2

/-- The Bessel series with coefficients `(n!)⁻²` evaluated at `(-(t²) / 4) • A` is summable. -/
theorem bessel_series_summable (A : E) (t : ℂ) :
    Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) ^ 2 •
      ((-(t ^ 2) / 4) • A) ^ n) := by
  apply scalarSeries_summable_of_ratio_zero
    (fun n : ℕ => ((n.factorial : ℂ)⁻¹) ^ 2) _ factorial_square_ratio_tendsto
  exact Filter.Eventually.of_forall (fun n => pow_ne_zero _
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))))

/-- The Bessel series evaluated at `(-(t²) / 4) • (L + w • H)` is analytic in the affine
parameter at every complex point. -/
theorem bessel_series_affine_analytic (L H : E) (t z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) ^ 2 •
      ((-(t ^ 2) / 4) • (L + w • H)) ^ n) z := by
  apply scalarSeries_affine_analytic_of_ratio_zero
    (fun n : ℕ => ((n.factorial : ℂ)⁻¹) ^ 2) _ factorial_square_ratio_tendsto
  exact Filter.Eventually.of_forall (fun n => pow_ne_zero _
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))))

/-- The successive norm ratio of reciprocal even factorials equals `((2n + 2) * (2n + 1))⁻¹`. -/
private theorem even_factorial_ratio (n : ℕ) :
    ‖(((2 * (n + 1)).factorial : ℂ)⁻¹)‖ / ‖(((2 * n).factorial : ℂ)⁻¹)‖ =
      ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1))⁻¹ := by
  simp only [norm_inv, Complex.norm_natCast]
  have hfact : ((2 * (n + 1)).factorial : ℝ) =
      ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1)) * ((2 * n).factorial : ℝ) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hf : ((2 * n).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
  have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- The successive norm ratios of reciprocal even factorial coefficients tend to zero. -/
private theorem even_factorial_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖(((2 * n.succ).factorial : ℂ)⁻¹)‖ /
      ‖(((2 * n).factorial : ℂ)⁻¹)‖) atTop (𝓝 0) := by
  simp_rw [Nat.succ_eq_add_one, even_factorial_ratio]
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have h1 := tendsto_atTop_add_const_right atTop (1 : ℝ) hm
  have h2 := tendsto_atTop_add_const_right atTop (2 : ℝ) hm
  exact tendsto_inv_atTop_zero.comp (h2.atTop_mul_atTop₀ h1)

/-- The wave series with coefficients `((2n)!)⁻¹` evaluated at `-(t²) • A` is summable. -/
theorem wave_series_summable (A : E) (t : ℂ) :
    Summable (fun n : ℕ => (((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n) := by
  apply scalarSeries_summable_of_ratio_zero
    (fun n : ℕ => (((2 * n).factorial : ℂ)⁻¹)) _ even_factorial_ratio_tendsto
  exact Filter.Eventually.of_forall (fun n =>
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))))

/-- The wave series evaluated at `-(t²) • (L + w • H)` is analytic in the affine parameter at
every complex point. -/
theorem wave_series_affine_analytic (L H : E) (t z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ∑' n : ℕ, (((2 * n).factorial : ℂ)⁻¹) •
      (-(t ^ 2) • (L + w • H)) ^ n) z := by
  apply scalarSeries_affine_analytic_of_ratio_zero
    (fun n : ℕ => (((2 * n).factorial : ℂ)⁻¹)) _ even_factorial_ratio_tendsto
  exact Filter.Eventually.of_forall (fun n =>
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))))

/-- The real Airy series coefficient `(9ⁿ * n! * (2/3)ₙ)⁻¹`, where `(2/3)ₙ` is the ascending
Pochhammer product. -/
def airySeriesCoefficient (n : ℕ) : ℝ :=
  ((9 : ℝ) ^ n * (n.factorial : ℝ) * (ascPochhammer ℝ n).eval (2 / 3))⁻¹

/-- The zeroth Airy series coefficient is one. -/
@[simp] theorem airySeriesCoefficient_zero : airySeriesCoefficient 0 = 1 := by
  simp [airySeriesCoefficient]

/-- Every Airy series coefficient is strictly positive. -/
theorem airySeriesCoefficient_pos (n : ℕ) : 0 < airySeriesCoefficient n := by
  have hp := ascPochhammer_pos n (2 / 3 : ℝ) (by norm_num)
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  unfold airySeriesCoefficient
  positivity

/-- The next Airy series coefficient is the current coefficient divided by `(3n + 3) * (3n +
2)`. -/
theorem airySeriesCoefficient_step (n : ℕ) :
    airySeriesCoefficient (n + 1) =
      airySeriesCoefficient n / ((3 * (n : ℝ) + 3) * (3 * (n : ℝ) + 2)) := by
  unfold airySeriesCoefficient
  rw [pow_succ, Nat.factorial_succ, ascPochhammer_succ_eval,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hp := ne_of_gt (ascPochhammer_pos n (2 / 3 : ℝ) (by norm_num))
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have h1 : 3 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h2 : 3 * (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 2 / 3 + (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The successive norm ratio of the complex-cast Airy coefficients equals `((3n + 3) * (3n +
2))⁻¹`. -/
private theorem airy_coefficient_ratio (n : ℕ) :
    ‖(airySeriesCoefficient (n + 1) : ℂ)‖ / ‖(airySeriesCoefficient n : ℂ)‖ =
      ((3 * (n : ℝ) + 3) * (3 * (n : ℝ) + 2))⁻¹ := by
  rw [Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (airySeriesCoefficient_pos _).le,
    Real.norm_of_nonneg (airySeriesCoefficient_pos _).le, airySeriesCoefficient_step]
  have ha := ne_of_gt (airySeriesCoefficient_pos n)
  have h1 : 3 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h2 : 3 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- The successive norm ratios of the complex-cast Airy coefficients tend to zero. -/
private theorem airy_coefficient_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖(airySeriesCoefficient n.succ : ℂ)‖ /
      ‖(airySeriesCoefficient n : ℂ)‖) atTop (𝓝 0) := by
  simp_rw [Nat.succ_eq_add_one, airy_coefficient_ratio]
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => 3 * (n : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have h3 := tendsto_atTop_add_const_right atTop (3 : ℝ) hm
  have h2 := tendsto_atTop_add_const_right atTop (2 : ℝ) hm
  exact tendsto_inv_atTop_zero.comp (h3.atTop_mul_atTop₀ h2)

/-- The Airy series with coefficients `airySeriesCoefficient n` evaluated at `-(t³) • A` is
summable. -/
theorem airy_series_summable (A : E) (t : ℂ) :
    Summable (fun n : ℕ => (airySeriesCoefficient n : ℂ) • (-(t ^ 3) • A) ^ n) := by
  apply scalarSeries_summable_of_ratio_zero
    (fun n : ℕ => (airySeriesCoefficient n : ℂ)) _ airy_coefficient_ratio_tendsto
  exact Filter.Eventually.of_forall (fun n =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (airySeriesCoefficient_pos n)))

/-- The Airy series evaluated at `-(t³) • (L + w • H)` is analytic in the affine parameter at
every complex point. -/
theorem airy_series_affine_analytic (L H : E) (t z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ∑' n : ℕ, (airySeriesCoefficient n : ℂ) •
      (-(t ^ 3) • (L + w • H)) ^ n) z := by
  apply scalarSeries_affine_analytic_of_ratio_zero
    (fun n : ℕ => (airySeriesCoefficient n : ℂ)) _ airy_coefficient_ratio_tendsto
  exact Filter.Eventually.of_forall (fun n =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (airySeriesCoefficient_pos n)))

/-- For distinct poles enclosed by a circle, the normalized pole-product integral of the affine
exponential equals its value at the distinguished pole plus the explicitly weighted values
at the other poles [WangEtAl2026]. -/
theorem exp_affine_cbmd_finite_circle {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℂ) (hp : Set.InjOn p s) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (L H : E) (u c : ℂ) (R : ℝ) (hinside : ∀ i ∈ s, p i ∈ ball c R) :
    let F : ℂ → E := fun z => NormedSpace.exp (u • (L + z • H))
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (∏ j ∈ s.erase i₀, (p i₀ - p j)) •
          ((∏ i ∈ s, (z - p i))⁻¹ • F z)) =
      F (p i₀) + ∑ i ∈ s.erase i₀,
        ((∏ j ∈ s.erase i₀, (p i₀ - p j)) *
          (∏ j ∈ s.erase i, (p i - p j))⁻¹) • F (p i) := by
  exact cbmd_finite_polynomial_regulator_circle s p hp i₀ hi₀
    (exp_affine_diffContOnCl L H u (ball c R)) hinside

/-- For distinct poles enclosed by a circle, the normalized pole-product integral of the affine
Bessel series equals its value at the distinguished pole plus the explicitly weighted values
at the other poles [WangEtAl2026]. -/
theorem bessel_series_cbmd_finite_circle {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℂ) (hp : Set.InjOn p s) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (L H : E) (t c : ℂ) (R : ℝ) (hinside : ∀ i ∈ s, p i ∈ ball c R) :
    let F : ℂ → E := fun z => ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) ^ 2 •
      ((-(t ^ 2) / 4) • (L + z • H)) ^ n
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (∏ j ∈ s.erase i₀, (p i₀ - p j)) •
          ((∏ i ∈ s, (z - p i))⁻¹ • F z)) =
      F (p i₀) + ∑ i ∈ s.erase i₀,
        ((∏ j ∈ s.erase i₀, (p i₀ - p j)) *
          (∏ j ∈ s.erase i, (p i - p j))⁻¹) • F (p i) := by
  exact cbmd_finite_polynomial_regulator_circle s p hp i₀ hi₀
    (Differentiable.diffContOnCl
      (fun z => (bessel_series_affine_analytic L H t z).differentiableAt)) hinside

/-- For distinct poles enclosed by a circle, the normalized pole-product integral of the affine
wave series equals its value at the distinguished pole plus the explicitly weighted values
at the other poles [WangEtAl2026]. -/
theorem wave_series_cbmd_finite_circle {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℂ) (hp : Set.InjOn p s) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (L H : E) (t c : ℂ) (R : ℝ) (hinside : ∀ i ∈ s, p i ∈ ball c R) :
    let F : ℂ → E := fun z => ∑' n : ℕ, (((2 * n).factorial : ℂ)⁻¹) •
      (-(t ^ 2) • (L + z • H)) ^ n
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (∏ j ∈ s.erase i₀, (p i₀ - p j)) •
          ((∏ i ∈ s, (z - p i))⁻¹ • F z)) =
      F (p i₀) + ∑ i ∈ s.erase i₀,
        ((∏ j ∈ s.erase i₀, (p i₀ - p j)) *
          (∏ j ∈ s.erase i, (p i - p j))⁻¹) • F (p i) := by
  exact cbmd_finite_polynomial_regulator_circle s p hp i₀ hi₀
    (Differentiable.diffContOnCl
      (fun z => (wave_series_affine_analytic L H t z).differentiableAt)) hinside

/-- For distinct poles enclosed by a circle, the normalized pole-product integral of the affine
Airy series equals its value at the distinguished pole plus the explicitly weighted values
at the other poles [WangEtAl2026]. -/
theorem airy_series_cbmd_finite_circle {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℂ) (hp : Set.InjOn p s) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (L H : E) (t c : ℂ) (R : ℝ) (hinside : ∀ i ∈ s, p i ∈ ball c R) :
    let F : ℂ → E := fun z => ∑' n : ℕ, (airySeriesCoefficient n : ℂ) •
      (-(t ^ 3) • (L + z • H)) ^ n
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (∏ j ∈ s.erase i₀, (p i₀ - p j)) •
          ((∏ i ∈ s, (z - p i))⁻¹ • F z)) =
      F (p i₀) + ∑ i ∈ s.erase i₀,
        ((∏ j ∈ s.erase i₀, (p i₀ - p j)) *
          (∏ j ∈ s.erase i, (p i - p j))⁻¹) • F (p i) := by
  exact cbmd_finite_polynomial_regulator_circle s p hp i₀ hi₀
    (Differentiable.diffContOnCl
      (fun z => (airy_series_affine_analytic L H t z).differentiableAt)) hinside

end BanachAlgebra

section Matrices

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix exponential `exp (-t • (L + w • H))` is analytic in the complex parameter at
every point for every real `t`. -/
theorem matrix_propagator_analytic (L H : Matrix n n ℂ) (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ
      (fun w : ℂ => NormedSpace.exp ((-(t : ℂ)) • (L + w • H))) z :=
  exp_affine_analytic L H (-(t : ℂ)) z

/-- For a circle enclosing `i` and zero, the normalized two-pole integral of the matrix
exponential equals `exp (-t • (L + i H)) - exp (-t • L)` [WangEtAl2026]. -/
theorem matrix_propagator_cbmd_circle (L H : Matrix n n ℂ) (t : ℝ) (c : ℂ) (R : ℝ)
    (hi : I ∈ ball c R) (hzero : (0 : ℂ) ∈ ball c R) :
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), (I / ((z - I) * z)) •
          NormedSpace.exp ((-(t : ℂ)) • (L + z • H))) =
      NormedSpace.exp ((-(t : ℂ)) • (L + I • H)) -
        NormedSpace.exp ((-(t : ℂ)) • L) :=
  exp_affine_cbmd_circle L H (-(t : ℂ)) c R hi hzero

end Matrices

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
