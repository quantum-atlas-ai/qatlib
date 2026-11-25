/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.KernelBounds
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.ClosedWrithe
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.NonuniformCL
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Explicit near-diagonal control of the Gauss band

[Kedia2018SuperfluidHelicity], Section V, Eq. (6),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The writhe term of the centerline helicity is the only part of the Gauss assembly whose
integrand is singular, the singularity sitting on the parameter diagonal. This module
quantifies how much of the self Gauss integral is contributed by a near-diagonal band
`|s - t| < δ`: the band has measure at most `2π · 2δ` in the parameter square, and the
near-diagonal kernel bound of `KernelBounds` then bounds the band contribution of any
regular simple `C²` centerline by the explicit constant
`324 · B⁴ M² / (π τ⁶) · 2π · 2δ`, linear in `δ`.

Assembled at the bundle level, the truncated helicity (off-diagonal Gauss pairing plus
banded self terms) differs from the fully geometric centerline helicity by at most the
sum of squared circulations times that linear-in-`δ` constant; after normalization by
the squared total circulation the truncation error is governed by exactly the inverse
effective bundle size of `NonuniformCL` times `δ`. This is the verifiable truncated
convergence rate on the filament side: it says how the regularized object approaches the
singular one, not that either converges to a continuous-vorticity helicity.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open scoped ENNReal Real NNReal

/-- The near-diagonal band of the parameter square excised by `writheBand`. -/
def gaussBand (δ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | |p.1 - p.2| < δ}

/-- The band is measurable: it is the preimage of an open ray under the continuous
function `p ↦ |p.1 - p.2|`. -/
theorem measurableSet_gaussBand (δ : ℝ) : MeasurableSet (gaussBand δ) := by
  have hc : Continuous fun p : ℝ × ℝ => |p.1 - p.2| := by fun_prop
  have hm : Measurable fun p : ℝ × ℝ => |p.1 - p.2| := Continuous.measurable hc
  exact MeasurableSet.preimage (measurableSet_Iio (a := δ)) hm

private theorem gaussMeasure_univ_lt_top : gaussMeasure Set.univ < ∞ := by
  rw [gaussMeasure, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
    sub_zero]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

local instance gaussMeasure_isFinite : IsFiniteMeasure gaussMeasure :=
  ⟨gaussMeasure_univ_lt_top⟩

/-- The band has measure at most `2π · 2δ` in the parameter square: every vertical
slice is an interval of length at most `2δ`, and the square has side `2π`. -/
theorem measure_gaussBand_le (δ : ℝ) :
    gaussMeasure (gaussBand δ) ≤ ENNReal.ofReal (2 * π * (2 * δ)) := by
  have hm := measurableSet_gaussBand δ
  have hslice : ∀ a : ℝ, MeasurableSet {b : ℝ | |a - b| < δ} := by
    intro a
    have hc : Continuous fun b : ℝ => |a - b| := by fun_prop
    have hm : Measurable fun b : ℝ => |a - b| := Continuous.measurable hc
    exact MeasurableSet.preimage (measurableSet_Iio (a := δ)) hm
  rw [gaussMeasure, ← lintegral_indicator_one hm]
  have hprod : ∫⁻ a, (gaussBand δ).indicator 1 a
      ∂((volume.restrict (Set.Icc (0 : ℝ) (2 * π))).prod
        (volume.restrict (Set.Icc (0 : ℝ) (2 * π))))
      = ∫⁻ a, ∫⁻ b, (gaussBand δ).indicator 1 (a, b)
          ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π)))
        ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π))) :=
    lintegral_prod _ ((measurable_const.indicator hm).aemeasurable)
  rw [hprod]
  calc ∫⁻ a, ∫⁻ b, (gaussBand δ).indicator 1 (a, b)
          ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π)))
        ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π)))
      ≤ ∫⁻ a, ENNReal.ofReal (2 * δ)
          ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π))) := by
          refine lintegral_mono fun a => ?_
          calc ∫⁻ b, (gaussBand δ).indicator 1 (a, b)
                ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π)))
              = ∫⁻ b, {b : ℝ | |a - b| < δ}.indicator 1 b
                  ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * π))) :=
                  lintegral_congr fun b => by
                    by_cases hb : |a - b| < δ <;>
                      simp [gaussBand, Set.indicator, hb]
            _ = (volume.restrict (Set.Icc (0 : ℝ) (2 * π))) {b : ℝ | |a - b| < δ} :=
                  lintegral_indicator_one (hslice a)
            _ = volume ({b : ℝ | |a - b| < δ} ∩ Set.Icc (0 : ℝ) (2 * π)) :=
                  Measure.restrict_apply (μ := volume)
                    (s := Set.Icc (0 : ℝ) (2 * π)) (hslice a)
            _ ≤ volume (Set.Ioo (a - δ) (a + δ)) := by
                  refine measure_mono fun b hb => ?_
                  have hbabs : |a - b| < δ := hb.1
                  have hb2 := abs_lt.mp hbabs
                  constructor <;> linarith
            _ = ENNReal.ofReal ((a + δ) - (a - δ)) := Real.volume_Ioo
            _ = ENNReal.ofReal (2 * δ) := by congr 1; ring
    _ = ENNReal.ofReal (2 * δ) *
          (volume.restrict (Set.Icc (0 : ℝ) (2 * π))) Set.univ :=
          lintegral_const _
    _ = ENNReal.ofReal (2 * δ) * ENNReal.ofReal (2 * π) := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Real.volume_Icc, sub_zero]
    _ = ENNReal.ofReal (2 * π * (2 * δ)) := by
          rw [ENNReal.ofReal_mul (by linarith [Real.two_pi_pos] :
            (0 : ℝ) ≤ 2 * π)]
          ring

/-- The real measure of the band is at most `2π · 2δ`. -/
theorem measureReal_gaussBand_le {δ : ℝ} (hδ : 0 ≤ δ) :
    gaussMeasure.real (gaussBand δ) ≤ 2 * π * (2 * δ) := by
  have hle := measure_gaussBand_le δ
  have hfin : gaussMeasure (gaussBand δ) ≠ ⊤ :=
    ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)
  have hreal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal
    (by positivity : (0 : ℝ) ≤ 2 * π * (2 * δ))] at hreal
  exact hreal

/-- Splitting the self Gauss integral into band and complement identifies the difference
between the full writhe and the band-regularized writhe of `WritheGeometry` as the band
integral of the kernel. -/
theorem gaussWrithe_sub_writheBand_eq (γ : ℝ → (Fin 3 → ℝ)) {δ : ℝ}
    (hint : Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure) :
    gaussWrithe γ - writheBand γ δ
      = ∫ p in gaussBand δ, writheKernel γ p.1 p.2 ∂gaussMeasure := by
  have hm := measurableSet_gaussBand δ
  have hcomp := integral_add_compl hm hint
  have hband : writheBand γ δ
      = ∫ p in (gaussBand δ)ᶜ, writheKernel γ p.1 p.2 ∂gaussMeasure := by
    rw [← integral_indicator (MeasurableSet.compl hm)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      by_cases hp : |p.1 - p.2| < δ
      · simp [gaussBand, hp]
      · simp [gaussBand, hp])
  rw [hband]
  have hfull : gaussWrithe γ
      = (∫ p in gaussBand δ, writheKernel γ p.1 p.2 ∂gaussMeasure)
        + ∫ p in (gaussBand δ)ᶜ, writheKernel γ p.1 p.2 ∂gaussMeasure :=
    hcomp.symm
  rw [hfull]
  ring

/-- **Explicit near-diagonal control.** For a regular simple `C²` centerline with tangent
bounds `τ ≤ |γ'| ≤ B` in the sense of `KernelBounds` and curvature bound `M`, the
contribution of the near-diagonal band `|s - t| < δ` to the actual self Gauss writhe is
at most the explicit constant `324 · B⁴ M² / (π τ⁶) · 2π · 2δ`: the band measure is
linear in `δ` and the kernel is uniformly bounded there. This is the verifiable rate at
which the band-regularized writhe converges to the singular writhe; nothing here claims
convergence of any pairing to a continuous-vorticity limit. -/
theorem abs_gaussWrithe_sub_writheBand_le (γ : ℝ → (Fin 3 → ℝ)) (hγ : ContDiff ℝ 2 γ)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    (hint : Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 3 * M * B * δ ≤ τ ^ 2 / 2) :
    |gaussWrithe γ - writheBand γ δ|
      ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (2 * π * (2 * δ)) := by
  rw [gaussWrithe_sub_writheBand_eq γ hint]
  have hm := measurableSet_gaussBand δ
  have habs : |∫ p in gaussBand δ, writheKernel γ p.1 p.2 ∂gaussMeasure|
      ≤ ∫ p in gaussBand δ, |writheKernel γ p.1 p.2| ∂gaussMeasure :=
    abs_integral_le_integral_abs
      (f := fun p : ℝ × ℝ => writheKernel γ p.1 p.2)
      (μ := gaussMeasure.restrict (gaussBand δ))
  have hmono : ∫ p in gaussBand δ, |writheKernel γ p.1 p.2| ∂gaussMeasure
      ≤ ∫ p in gaussBand δ, (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) ∂gaussMeasure := by
    rw [← integral_indicator hm, ← integral_indicator hm]
    refine integral_mono (hint.abs.indicator hm)
      ((integrable_const _).indicator hm) ?_
    have hB0 : (0 : ℝ) ≤ B := (norm_nonneg (deriv γ 0)).trans (hB 0)
    have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (deriv (deriv γ) 0)).trans (hM 0)
    intro p
    by_cases hp : |p.1 - p.2| < δ
    · have hbind1 : (gaussBand δ).indicator
          (fun p : ℝ × ℝ => |writheKernel γ p.1 p.2|) p
          = |writheKernel γ p.1 p.2| := by
        simp [gaussBand, hp]
      have hbind2 : (gaussBand δ).indicator
          (fun _ : ℝ × ℝ => 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) p
          = 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) := by
        simp [gaussBand, hp]
      rw [hbind1, hbind2]
      refine abs_writheKernel_le_near γ hγ hτ0 hτ hB hM p.1 p.2 ?_
      have hpδ : |p.1 - p.2| < δ := hp
      have hMB : (0 : ℝ) ≤ 3 * M * B :=
        mul_nonneg (mul_nonneg (by norm_num) hM0) hB0
      calc 3 * M * B * |p.2 - p.1| = 3 * M * B * |p.1 - p.2| := by
            rw [abs_sub_comm]
        _ ≤ 3 * M * B * δ := mul_le_mul (le_refl _) hpδ.le (abs_nonneg _) hMB
        _ ≤ τ ^ 2 / 2 := hsmall
    · have hbind1 : (gaussBand δ).indicator
          (fun p : ℝ × ℝ => |writheKernel γ p.1 p.2|) p
          = 0 := by
        simp [gaussBand, hp]
      have hbind2 : (gaussBand δ).indicator
          (fun _ : ℝ × ℝ => 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) p
          = 0 := by
        simp [gaussBand, hp]
      rw [hbind1, hbind2]
  have hC : (0 : ℝ) ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) := by
    have hB0 : (0 : ℝ) ≤ B := (norm_nonneg (deriv γ 0)).trans (hB 0)
    have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (deriv (deriv γ) 0)).trans (hM 0)
    refine div_nonneg ?_ ?_
    · have h1 : (0 : ℝ) ≤ B ^ 4 := pow_nonneg hB0 4
      have h2 : (0 : ℝ) ≤ M ^ 2 := pow_nonneg hM0 2
      nlinarith
    · exact mul_nonneg Real.pi_pos.le (pow_nonneg hτ0.le 6)
  have hconst : ∫ p in gaussBand δ, (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) ∂gaussMeasure
      ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (2 * π * (2 * δ)) := by
    rw [← integral_indicator hm, integral_indicator_const _ hm, smul_eq_mul]
    calc gaussMeasure.real (gaussBand δ) * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6))
        ≤ 2 * π * (2 * δ) * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) :=
          mul_le_mul_of_nonneg_right (measureReal_gaussBand_le hδ) hC
      _ = 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (2 * π * (2 * δ)) := by ring
  exact habs.trans (hmono.trans hconst)

/-- Sufficient condition via `KernelBounds`: a simple regular `C²` arc has integrable
self kernel, so the explicit near-diagonal control applies. -/
theorem abs_gaussWrithe_sub_writheBand_le_of_regular (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    (hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      γ s = γ t → s = t)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 3 * M * B * δ ≤ τ ^ 2 / 2) :
    |gaussWrithe γ - writheBand γ δ|
      ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (2 * π * (2 * δ)) :=
  abs_gaussWrithe_sub_writheBand_le γ hγ hτ0 hτ hB hM
    (writheKernel_integrable_of_regular γ hγ hτ0 hτ hB hM hinj) hδ hsmall

/-- Sufficient condition via `ClosedWrithe`: a closed `C²` curve, injective on the
half-open period and everywhere regular, has integrable self kernel, so the explicit
near-diagonal control applies to genuine closed centerlines. -/
theorem abs_gaussWrithe_sub_writheBand_le_of_closed_regular (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ) (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π))) (hregular : ∀ t, deriv γ t ≠ 0)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 3 * M * B * δ ≤ τ ^ 2 / 2) :
    |gaussWrithe γ - writheBand γ δ|
      ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (2 * π * (2 * δ)) :=
  abs_gaussWrithe_sub_writheBand_le γ hγ hτ0 hτ hB hM
    (writheKernel_integrable_of_closed_regular γ hγ hp hinj hregular) hδ hsmall

/-- The band-truncated helicity of a geometric bundle: the off-diagonal Gauss pairing
(never singular for disjoint filaments) plus the band-regularized self terms. -/
noncomputable def truncatedGaussHelicity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) (δ : ℝ) : ℝ :=
  pairLinkingGauss κ γ + ∑ i, κ i ^ 2 * writheBand (γ i) δ

/-- At the bundle level, truncation costs at most the sum of squared circulations times
the explicit near-diagonal constant times `δ`-worth of band, uniformly over the family
under uniform regularity constants. The off-diagonal pairing enters both sides
unchanged: only the self terms are regularized. -/
theorem abs_truncatedGaussHelicity_sub_centerlineHelicityGaussSelf_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ))
    {τ B M : ℝ} (hτ0 : 0 < τ)
    (hγ : ∀ i, ContDiff ℝ 2 (γ i))
    (hτ : ∀ i u, τ ^ 2 ≤ dot3 (deriv (γ i) u) (deriv (γ i) u))
    (hB : ∀ i u, ‖deriv (γ i) u‖ ≤ B)
    (hM : ∀ i u, ‖deriv (deriv (γ i)) u‖ ≤ M)
    (hint : ∀ i, Integrable (fun p : ℝ × ℝ => writheKernel (γ i) p.1 p.2) gaussMeasure)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 3 * M * B * δ ≤ τ ^ 2 / 2) :
    |truncatedGaussHelicity κ γ δ - centerlineHelicityGaussSelf κ γ|
      ≤ (∑ i, κ i ^ 2) * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) * (2 * π * (2 * δ)) := by
  have hsplit : truncatedGaussHelicity κ γ δ - centerlineHelicityGaussSelf κ γ
      = ∑ i, κ i ^ 2 * (writheBand (γ i) δ - gaussWrithe (γ i)) := by
    rw [truncatedGaussHelicity, centerlineHelicityGaussSelf_eq]
    simp only [writheGaussPart]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  have hterm : ∀ i : ι, |κ i ^ 2 * (writheBand (γ i) δ - gaussWrithe (γ i))|
      ≤ κ i ^ 2 * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) * (2 * π * (2 * δ)) := by
    intro i
    have h1 := abs_gaussWrithe_sub_writheBand_le (γ i) (hγ i) hτ0 (hτ i) (hB i) (hM i)
      (hint i) hδ hsmall
    rw [abs_mul, abs_of_nonneg (sq_nonneg (κ i))]
    calc κ i ^ 2 * |writheBand (γ i) δ - gaussWrithe (γ i)|
        ≤ κ i ^ 2 * |gaussWrithe (γ i) - writheBand (γ i) δ| := by
          rw [abs_sub_comm]
      _ ≤ κ i ^ 2 * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (2 * π * (2 * δ))) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg (κ i))
      _ = κ i ^ 2 * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) * (2 * π * (2 * δ)) := by
          ring
  have hsum : |∑ i, κ i ^ 2 * (writheBand (γ i) δ - gaussWrithe (γ i))|
      ≤ ∑ i, κ i ^ 2 * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) * (2 * π * (2 * δ)) :=
    le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ)
      (Finset.sum_le_sum fun i _ => hterm i)
  refine le_trans hsum ?_
  rw [Finset.sum_mul, Finset.sum_mul]

/-- Normalized truncation error: after division by the squared total circulation, the
band-truncated bundle helicity differs from the rescaled fully geometric centerline
helicity by at most the inverse effective bundle size times the explicit near-diagonal
constant times `δ`. The truncation error is thus governed by the same suppression factor
that controls the writhe in the classical limit of `NonuniformCL`. -/
theorem abs_rescaled_truncatedGaussHelicity_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ))
    {τ B M : ℝ} (hτ0 : 0 < τ)
    (hγ : ∀ i, ContDiff ℝ 2 (γ i))
    (hτ : ∀ i u, τ ^ 2 ≤ dot3 (deriv (γ i) u) (deriv (γ i) u))
    (hB : ∀ i u, ‖deriv (γ i) u‖ ≤ B)
    (hM : ∀ i u, ‖deriv (deriv (γ i)) u‖ ≤ M)
    (hint : ∀ i, Integrable (fun p : ℝ × ℝ => writheKernel (γ i) p.1 p.2) gaussMeasure)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 3 * M * B * δ ≤ τ ^ 2 / 2)
    (hκ : ∑ i, κ i ≠ 0) :
    |truncatedGaussHelicity κ γ δ / (∑ i, κ i) ^ 2
        - centerlineHelicityGaussSelf κ γ / (∑ i, κ i) ^ 2|
      ≤ ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2)
        * (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) * (2 * π * (2 * δ)) := by
  have hpos : (0 : ℝ) < (∑ i, κ i) ^ 2 := sq_pos_of_ne_zero hκ
  have h := abs_truncatedGaussHelicity_sub_centerlineHelicityGaussSelf_le κ γ hτ0 hγ hτ
    hB hM hint hδ hsmall
  rw [div_sub_div_same, abs_div, abs_of_pos hpos]
  exact le_trans ((div_le_div_iff₀ hpos hpos).2
    (mul_le_mul_of_nonneg_right h hpos.le))
    (le_of_eq (by ring))

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
