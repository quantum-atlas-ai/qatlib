/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.NormalRibbon

import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The offset Gauss integral outside the circular diagonal

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
At every fixed positive circular parameter gap the actual Gauss kernel of
a core and its normal offset converges in the integral to the cut-off
self Gauss kernel. The gap excludes both the ordinary diagonal and the
identified endpoint corners of the parameter square.
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

/-- The part of the core–edge Gauss integral at circular gap at least `δ`. -/
def circularRibbonFar (γ N : ℝ → Fin 3 → ℝ) (δ a : ℝ) : ℝ :=
  ∫ p in {p : ℝ × ℝ | δ ≤ circularParameterGap p.1 p.2},
    gaussKernel γ (normalRibbonPoint γ N a) p.1 p.2 ∂gaussMeasure

/-- The part of the core–edge Gauss integral at circular gap less than `δ`. -/
def circularRibbonNear (γ N : ℝ → Fin 3 → ℝ) (δ a : ℝ) : ℝ :=
  ∫ p in {p : ℝ × ℝ | circularParameterGap p.1 p.2 < δ},
    gaussKernel γ (normalRibbonPoint γ N a) p.1 p.2 ∂gaussMeasure

/-- Circular gap is continuous in the two parameters. -/
private theorem continuous_circularParameterGap :
    Continuous (fun p : ℝ × ℝ => circularParameterGap p.1 p.2) := by
  unfold circularParameterGap
  exact (continuous_snd.sub continuous_fst).abs.min
    (continuous_const.sub (continuous_snd.sub continuous_fst).abs)

/-- The true normal offset at zero width is the centerline itself. -/
theorem normalRibbonPoint_zero (γ N : ℝ → Fin 3 → ℝ) :
    normalRibbonPoint γ N 0 = γ := by
  funext s
  simp [normalRibbonPoint]

/-- For disjoint curves the circular cut splits the complete core–edge integral. -/
theorem circularRibbonNear_add_far {γ N : ℝ → Fin 3 → ℝ} (hγ : ContDiff ℝ 1 γ)
    (hN : ContDiff ℝ 1 N) {a : ℝ} (hdisj : ∀ s t, γ s ≠ normalRibbonPoint γ N a t)
    (δ : ℝ) :
    circularRibbonNear γ N δ a + circularRibbonFar γ N δ a =
      gaussLinking γ (normalRibbonPoint γ N a) := by
  let U : Set (ℝ × ℝ) := {p | circularParameterGap p.1 p.2 < δ}
  have hU : MeasurableSet U :=
    (isOpen_lt continuous_circularParameterGap continuous_const).measurableSet
  have hc : ContDiff ℝ 1 (normalRibbonPoint γ N a) := hγ.add (hN.const_smul a)
  have hi := integrable_gaussKernel γ (normalRibbonPoint γ N a) hγ hc hdisj
  have hUc : Uᶜ = {p : ℝ × ℝ | δ ≤ circularParameterGap p.1 p.2} := by
    ext p
    exact (show ¬ circularParameterGap p.1 p.2 < δ ↔ δ ≤ circularParameterGap p.1 p.2 from not_lt)
  have hadd := integral_add_compl hU hi
  rw [hUc] at hadd
  exact hadd

/-- Away from the circular diagonal, a smooth thin offset has the same
zero-width integral limit as the actual cut-off self kernel. This result
requires simplicity and periodicity of the core on one full period. -/
theorem tendsto_circularRibbonFar {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hN : ContDiff ℝ 1 N)
    (hpγ : Function.Periodic γ (2 * π)) (hinj : InjOn γ (Ico 0 (2 * π)))
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    Tendsto (circularRibbonFar γ N δ) (𝓝 0) (𝓝 (circularWritheBand γ δ)) := by
  let F : Set (ℝ × ℝ) := {p | δ ≤ circularParameterGap p.1 p.2}
  let K := gaussDomain ∩ F
  let μ : Measure (ℝ × ℝ) := gaussMeasure.restrict F
  have hF : IsClosed F := isClosed_le continuous_const continuous_circularParameterGap
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right hF
  have hμ : μ = (volume.prod (volume : Measure ℝ)).restrict K := by
    change gaussMeasure.restrict F = _
    rw [gaussMeasure, Measure.prod_restrict, ← show gaussDomain =
      Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π) from rfl,
      Measure.restrict_restrict hF.measurableSet, inter_comm]
  have hKae : ∀ᵐ p ∂μ, p ∈ K := by
    rw [hμ]
    exact ae_restrict_mem hK.measurableSet
  obtain ⟨m, hm, hmin⟩ := exists_closed_curve_chord_min hγ.continuous hpγ hinj hδ hδπ
  have hNcomp : IsCompact (N '' Icc (0 : ℝ) (2 * π)) := isCompact_Icc.image hN.continuous
  obtain ⟨B, hB⟩ := hNcomp.isBounded.exists_norm_le
  let M := max 1 B
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  let r := m / (2 * M)
  have hr : 0 < r := by positivity
  let W := Icc (-r) r
  let f (q : ℝ × (ℝ × ℝ)) :=
    gaussKernel γ (normalRibbonPoint γ N q.1) q.2.1 q.2.2
  have hcont : ContinuousOn f (W ×ˢ K) := by
    let D (q : ℝ × (ℝ × ℝ)) := γ q.2.1 - normalRibbonPoint γ N q.1 q.2.2
    have hD : Continuous D := by unfold D normalRibbonPoint; fun_prop
    have hdγ := hγ.continuous_deriv_one
    have hdN := hN.continuous_deriv_one
    have hnum : Continuous (fun q : ℝ × (ℝ × ℝ) =>
        dot3 (cross3 (deriv γ q.2.1)
          (deriv γ q.2.2 + q.1 • deriv N q.2.2)) (D q)) := by
      simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
      fun_prop
    have hden : Continuous fun q => 4 * π * euclideanLength (D q) ^ 3 := by fun_prop
    have hne (q : ℝ × (ℝ × ℝ)) (hq : q ∈ W ×ˢ K) : D q ≠ 0 := by
      have hgap : δ ≤ min |q.2.2 - q.2.1| (2 * π - |q.2.2 - q.2.1|) := hq.2.2
      have hsep := hmin q.2 hq.2.1 (le_min_iff.mp hgap).1
        (by linarith only [(le_min_iff.mp hgap).2])
      have hwidth : |q.1| ≤ r := abs_le.mpr hq.1
      have hnormal : ‖N q.2.2‖ ≤ M :=
        (hB _ ⟨q.2.2, hq.2.1.2, rfl⟩).trans (le_max_right _ _)
      have hmove : ‖q.1 • N q.2.2‖ ≤ m / 2 := by
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ r * M := mul_le_mul hwidth hnormal (norm_nonneg _) hr.le
          _ = m / 2 := by dsimp only [r]; field_simp
      intro hz
      have he : γ q.2.1 - γ q.2.2 = q.1 • N q.2.2 := by
        have hz' : γ q.2.1 = γ q.2.2 + q.1 • N q.2.2 := sub_eq_zero.mp hz
        rw [hz', add_sub_cancel_left]
      rw [he] at hsep
      linarith
    have hd (q : ℝ × (ℝ × ℝ)) (hq : q ∈ W ×ˢ K) :
        4 * π * euclideanLength (D q) ^ 3 ≠ 0 := by
      have hpos := (norm_pos_iff.mpr (hne q hq)).trans_le (norm_le_euclideanLength _)
      positivity
    have hc := hnum.continuousOn.div hden.continuousOn hd
    refine hc.congr fun q _ => ?_
    unfold f gaussKernel
    rw [(hasDerivAt_normalRibbonPoint (a := q.1) (hγ.differentiable (by norm_num) q.2.2)
      (hN.differentiable (by norm_num) q.2.2)).deriv]
    rfl
  have hfK : IsCompact (f '' (W ×ˢ K)) := (isCompact_Icc.prod hK).image_of_continuousOn hcont
  obtain ⟨C, hC⟩ := hfK.isBounded.exists_norm_le
  have hW : W ∈ 𝓝 (0 : ℝ) := mem_of_superset (Ioo_mem_nhds (by linarith) hr) Ioo_subset_Icc_self
  have hslice (a : ℝ) (ha : a ∈ W) : ContinuousOn (fun p => f (a, p)) K :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hp => ⟨ha, hp⟩)
  have hlim : Tendsto (fun a => ∫ p, f (a, p) ∂μ) (𝓝 0) (𝓝 (∫ p, f (0, p) ∂μ)) := by
    have : IsFiniteMeasure μ := by
      rw [hμ, isFiniteMeasure_restrict]
      exact (hK.measure_lt_top (μ := volume.prod volume)).ne
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · filter_upwards [hW] with a ha
      rw [hμ]
      exact ((hslice a ha).integrableOn_compact hK).aestronglyMeasurable
    · filter_upwards [hW] with a ha
      filter_upwards [hKae] with p hp
      exact hC _ ⟨(a, p), ⟨ha, hp⟩, rfl⟩
    · exact integrable_const _
    · filter_upwards [hKae] with p hp
      have hp' : (0, p) ∈ W ×ˢ K := ⟨⟨by linarith, hr.le⟩, hp⟩
      have hpair : Tendsto (fun a => (a, p)) (𝓝 0) (𝓝[W ×ˢ K] (0, p)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
        filter_upwards [hW] with a ha
        exact ⟨ha, hp⟩
      exact (hcont (0, p) hp').tendsto.comp hpair
  have heq : (∫ p, f (0, p) ∂μ) = circularWritheBand γ δ := by
    change (∫ p in F, gaussKernel γ (normalRibbonPoint γ N 0) p.1 p.2 ∂gaussMeasure) = _
    rw [normalRibbonPoint_zero, ← integral_indicator hF.measurableSet]
    unfold circularWritheBand
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : circularParameterGap p.1 p.2 < δ <;> simp [F, Set.indicator, hp, writheKernel]
  rw [heq] at hlim
  exact hlim

/-- The actual narrow-band integral admits the iterated zero-width and
zero-band limit. For any sufficiently narrow reference edge that limit
is its Gauss linking with the core minus the core writhe. -/
theorem exists_circularRibbonNear_iterated_limit {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : ContDiff ℝ 2 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hreg : ∀ s, deriv γ s ≠ 0)
    (hNnz : ∀ s, N s ≠ 0) (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ ε > 0, ∀ b : ℝ, 0 < b → b < ε →
      (∀ δ : ℝ, 0 < δ → δ ≤ π →
        Tendsto (circularRibbonNear γ N δ) (𝓝[>] 0)
          (𝓝 (gaussLinking γ (normalRibbonPoint γ N b) - circularWritheBand γ δ))) ∧
      Tendsto (fun δ => gaussLinking γ (normalRibbonPoint γ N b) - circularWritheBand γ δ)
        (𝓝[>] 0) (𝓝 (gaussLinking γ (normalRibbonPoint γ N b) - gaussLinking γ γ)) := by
  obtain ⟨ε, hε, _, hdisj, hsame⟩ :=
    exists_normalRibbon_gaussLinking_stable hγ hN hpγ hpN hinj hreg hNnz horth
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hN1 : ContDiff ℝ 1 N := hN.of_le (by norm_num)
  refine ⟨ε, hε, fun b hb hbε => ⟨?_, ?_⟩⟩
  · intro δ hδ hδπ
    have hfar := (tendsto_circularRibbonFar hγ1 hN1 hpγ hinj hδ hδπ).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    refine (tendsto_const_nhds.sub hfar).congr' ?_
    have hsmall : Iio ε ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hε)
    filter_upwards [self_mem_nhdsWithin, hsmall] with a ha haε
    have ha' : 0 < a := mem_Ioi.mp ha
    have h0 : |(0 : ℝ)| < ε := by simpa using hε
    have haε' : |a| < ε := by simpa only [abs_of_pos ha'] using (mem_Iio.mp haε)
    have hbε' : |b| < ε := by simpa only [abs_of_pos hb] using hbε
    have hsplit := circularRibbonNear_add_far hγ1 hN1 (by
      simpa only [normalRibbonPoint_zero] using (fun s t => hdisj 0 a s t h0 haε' ha'.ne)) δ
    have heq := hsame 0 a 0 b h0 haε' h0 hbε' ha' hb
    rw [normalRibbonPoint_zero] at heq
    rw [heq] at hsplit
    exact sub_eq_of_eq_add hsplit.symm
  · exact tendsto_const_nhds.sub
      (tendsto_circularWritheBand_of_closed_regular γ hγ hpγ hinj hreg)

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
