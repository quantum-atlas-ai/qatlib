/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonBand
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonError

/-!
# The Călugăreanu–White–Fuller identity for a smooth closed normal ribbon

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
For a simple closed unit-speed centerline and a closed orthogonal unit
framing, the Gauss linking of the core and a sufficiently narrow
positive offset equals the self Gauss integral plus the twist integral.
The uniform diagonal error vanishes after the band shrinks.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge (cross3_apply_zero cross3_apply_one
  cross3_apply_two)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open Filter MeasureTheory Set
open scoped Real Topology

set_option maxHeartbeats 600000 in
/-- The pointwise error gives an integrated error proportional to the
width of the symmetric parameter band. -/
private theorem abs_ribbonNear_sub_model_le {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : ContDiff ℝ 1 N)
    (hpγ : Function.Periodic γ (2 * π)) {a δ K : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hδπ : δ ≤ π)
    (hdisj : ∀ s t, γ s ≠ normalRibbonPoint γ N a t)
    (herr : ∀ s h : ℝ, |h| ≤ δ →
      |gaussKernel γ (normalRibbonPoint γ N a) (s + h) s - frozenRibbonKernel γ N a s h| ≤ K) :
    |circularRibbonNear γ N δ a -
      (δ / Real.sqrt (δ ^ 2 + a ^ 2)) * ribbonTwist γ N| ≤ 4 * π * K * δ := by
  let X := Icc (0 : ℝ) (2 * π)
  let Y := Icc (-δ) δ
  let μ := (volume.restrict X).prod (volume.restrict Y)
  let f (p : ℝ × ℝ) := gaussKernel γ (normalRibbonPoint γ N a) (p.1 + p.2) p.1
  let g (p : ℝ × ℝ) := frozenRibbonKernel γ N a p.1 p.2
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hNoff : ContDiff ℝ 1 (normalRibbonPoint γ N a) := hγ1.add (hN.const_smul a)
  have hfc : Continuous f :=
    (continuous_gaussKernel γ (normalRibbonPoint γ N a) hγ1 hNoff hdisj).comp
      ((continuous_fst.add continuous_snd).prodMk continuous_fst)
  have hT := hγ.continuous_deriv (by norm_num)
  have hTd : ContDiff ℝ 1 (deriv γ) := ContDiff.deriv' hγ
  have hA := hTd.continuous_deriv_one
  have hV := hN.continuous_deriv_one
  have hU := hN.continuous
  have hgc : Continuous g := by
    unfold g frozenRibbonKernel ribbonTwistDensity ribbonBendDensity
    simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro p
    positivity
  have hμ : μ = (volume.prod volume).restrict (X ×ˢ Y) := by
    unfold μ
    rw [Measure.prod_restrict]
  have hXY : IsCompact (X ×ˢ Y) := isCompact_Icc.prod isCompact_Icc
  have hf : Integrable f μ := by
    rw [hμ]
    exact hfc.continuousOn.integrableOn_compact hXY
  have hg : Integrable g μ := by
    rw [hμ]
    exact hgc.continuousOn.integrableOn_compact hXY
  have fubini (H : ℝ × ℝ → ℝ) (hH : Integrable H μ) :
      (∫ p, H p ∂μ) = ∫ s in 0..(2 * π), ∫ h in -δ..δ, H (s, h) := by
    change (∫ p, H p ∂(volume.restrict X).prod (volume.restrict Y)) = _
    rw [integral_prod H hH]
    simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le (by linarith : -δ ≤ δ), integral_Icc_eq_integral_Ioc, X, Y]
  have hk : Integrable (fun _ : ℝ × ℝ => K) μ := integrable_const _
  have hbound : ∀ᵐ p ∂μ, ‖f p - g p‖ ≤ K := by
    have hdom : ∀ᵐ p ∂μ, p ∈ X ×ˢ Y := by
      rw [hμ]
      exact ae_restrict_mem hXY.measurableSet
    filter_upwards [hdom] with p hp
    simpa only [Real.norm_eq_abs, f, g] using herr p.1 p.2 (abs_le.mpr hp.2)
  rw [circularRibbonNear_eq_intervalIntegral hγ1 hN hpγ hdisj hδ hδπ,
    ← integral_integral_frozenRibbonKernel γ N ha.ne' δ]
  change |(∫ s in 0..(2 * π), ∫ h in -δ..δ, f (s, h)) -
    (∫ s in 0..(2 * π), ∫ h in -δ..δ, g (s, h))| ≤ _
  rw [← fubini f hf, ← fubini g hg, ← integral_sub hf hg]
  calc
    _ ≤ ∫ p, K ∂μ := by
      rw [← Real.norm_eq_abs]
      exact (norm_integral_le_integral_norm _).trans
        (integral_mono_ae (hf.sub hg).norm hk hbound)
    _ = _ := by
      rw [fubini _ hk]
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      ring

set_option maxHeartbeats 500000 in
/-- The Călugăreanu–White–Fuller identity for a simple closed unit-speed
`C³` curve and a periodic orthogonal unit `C²` normal. Every sufficiently
narrow positive edge is disjoint from the core and its actual Gauss
linking equals the core writhe plus the framing twist. -/
theorem exists_normalRibbon_gaussLinking_eq_writhe_add_twist {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 3 γ) (hN : ContDiff ℝ 2 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π)))
    (hspeed : ∀ s, dot3 (deriv γ s) (deriv γ s) = 1)
    (hunit : ∀ s, dot3 (N s) (N s) = 1)
    (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ ε > 0, ∀ a : ℝ, 0 < a → a < ε →
      (∀ s t, γ s ≠ normalRibbonPoint γ N a t) ∧
      gaussLinking γ (normalRibbonPoint γ N a) = gaussLinking γ γ + ribbonTwist γ N := by
  have hγ2 : ContDiff ℝ 2 γ := hγ.of_le (by norm_num)
  have hN1 : ContDiff ℝ 1 N := hN.of_le (by norm_num)
  have hreg (s : ℝ) : deriv γ s ≠ 0 := by
    intro hz
    have hh := hspeed s
    rw [hz] at hh
    norm_num [dot3] at hh
  have hnz (s : ℝ) : N s ≠ 0 := by
    intro hz
    have hh := hunit s
    rw [hz] at hh
    norm_num [dot3] at hh
  obtain ⟨ε₁, hε₁, hnear⟩ :=
    exists_circularRibbonNear_iterated_limit hγ2 hN hpγ hpN hinj hreg hnz horth
  obtain ⟨ε₂, hε₂, hstrip⟩ :=
    exists_normalRibbon_injective hγ2 hN1 hpγ hpN hinj hreg hnz horth
  obtain ⟨η, hη, K, hK, herr⟩ :=
    exists_abs_normalRibbon_kernel_sub_le hγ hN1 hpγ hpN hspeed hunit horth
  have hdisj (a : ℝ) (ha : 0 < a) (haε : a < ε₂) (s t : ℝ) :
      γ s ≠ normalRibbonPoint γ N a t := by
    intro heq
    have heq' : normalRibbonPoint γ N 0 s = normalRibbonPoint γ N a t := by
      simpa only [normalRibbonPoint_zero] using heq
    have hw := hstrip 0 a s t (by simpa using hε₂)
      (by simpa only [abs_of_pos ha] using haε) heq'
    exact ha.ne hw.2
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun b hb hbε => ⟨?_, ?_⟩⟩
  · exact hdisj b hb (hbε.trans_le (min_le_right _ _))
  · let L := gaussLinking γ (normalRibbonPoint γ N b)
    let T := ribbonTwist γ N
    obtain ⟨hnear', hwr⟩ := hnear b hb (hbε.trans_le (min_le_left _ _))
    have hsmall (δ : ℝ) (hδ : 0 < δ) (hδπ : δ ≤ π) (hδη : δ ≤ η) :
        |L - circularWritheBand γ δ - T| ≤ 4 * π * K * δ := by
      have hlim := ((hnear' δ hδ hδπ).sub
        ((tendsto_ribbonBand_mass hδ).mul (tendsto_const_nhds (x := T)))).abs
      simp only [one_mul] at hlim
      apply le_of_tendsto hlim
      have he : Iio ε₂ ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds hε₂)
      filter_upwards [self_mem_nhdsWithin, he] with a ha haε
      exact abs_ribbonNear_sub_model_le hγ2 hN1 hpγ ha hδ hδπ (hdisj a ha haε)
        (fun s h hh => herr a s h ha (hh.trans hδη))
    have hz : |L - gaussLinking γ γ - T| ≤ 0 := by
      have hd := (hwr.sub (tendsto_const_nhds (x := T))).abs
      have hc : ContinuousAt (fun δ : ℝ => 4 * π * K * δ) 0 := by fun_prop
      have hc' := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp only [mul_zero] at hc'
      apply le_of_tendsto_of_tendsto hd hc'
      have he : Iio (min π η) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (lt_min Real.pi_pos hη))
      filter_upwards [self_mem_nhdsWithin, he] with δ hδ hδ'
      exact hsmall δ hδ ((lt_min_iff.mp hδ').1.le) ((lt_min_iff.mp hδ').2.le)
    have heq : L - gaussLinking γ γ - T = 0 := abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
    change L = gaussLinking γ γ + T
    linarith

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
