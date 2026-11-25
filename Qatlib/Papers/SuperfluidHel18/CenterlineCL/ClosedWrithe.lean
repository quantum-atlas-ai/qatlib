/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.KernelBounds
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Integrability and regularization of writhe for closed curves

[Kedia2018SuperfluidHelicity], Section II and Eq. (6),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
For a regular simple periodic curve, the self Gauss integrand has potential
singularities on the parameter diagonal and at the identified endpoints
of a period. Periodicity transports the near-diagonal estimate to the
endpoint corners. On the rest of the parameter square, simplicity and
compactness give positive chord separation.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open scoped Real Topology

/-- The derivative of a differentiable periodic vector curve has the same period. -/
theorem periodic_deriv_curve {γ : ℝ → (Fin 3 → ℝ)} {P : ℝ}
    (hp : Function.Periodic γ P) (hd : Differentiable ℝ γ) :
    Function.Periodic (deriv γ) P := by
  intro t
  have hline : HasDerivAt (fun u : ℝ => u + P) 1 t := (hasDerivAt_id t).add_const P
  have hshift := (hd (t + P)).hasDerivAt.scomp t hline
  have hsame : γ =ᶠ[𝓝 t] (γ ∘ fun u => u + P) :=
    Filter.Eventually.of_forall fun u => (hp u).symm
  simpa only [one_smul] using (hshift.congr_of_eventuallyEq hsame).deriv.symm

/-- The self Gauss kernel is periodic in its second parameter whenever
the curve and its tangent are periodic. -/
theorem writheKernel_periodic_right {γ : ℝ → (Fin 3 → ℝ)} {P : ℝ}
    (hp : Function.Periodic γ P) (hd : Differentiable ℝ γ) (s : ℝ) :
    Function.Periodic (writheKernel γ s) P := by
  intro t
  simp only [writheKernel, gaussKernel, hp t, periodic_deriv_curve hp hd t]

/-- Two parameters in one closed period with strictly intermediate
oriented separation have distinct images if the curve is simple on the
half-open period. -/
private theorem closed_curve_separated_of_lt {γ : ℝ → (Fin 3 → ℝ)}
    (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π))) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 (2 * π)) (ht : t ∈ Set.Icc 0 (2 * π))
    (hst : s < t) (hgap : t - s < 2 * π) :
    γ s ≠ γ t := by
  intro heq
  have hs' : s ∈ Set.Ico 0 (2 * π) := ⟨hs.1, hst.trans_le ht.2⟩
  rcases ht.2.lt_or_eq with ht' | ht'
  · exact hst.ne (hinj hs' ⟨ht.1, ht'⟩ heq)
  · have hend : γ t = γ 0 := by
      simpa only [zero_add, ht'] using hp 0
    have he : s = 0 := hinj hs' ⟨le_rfl, Real.two_pi_pos⟩ (heq.trans hend)
    rw [he, ht', sub_zero] at hgap
    exact (lt_irrefl _) hgap

/-- Distinct parameters of a simple closed curve have distinct positions
unless their difference is an entire period. -/
private theorem closed_curve_separated {γ : ℝ → (Fin 3 → ℝ)}
    (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π))) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 (2 * π)) (ht : t ∈ Set.Icc 0 (2 * π))
    (hpos : 0 < |t - s|) (hgap : |t - s| < 2 * π) :
    γ s ≠ γ t := by
  rcases lt_or_ge s t with hlt | hle
  · exact closed_curve_separated_of_lt hp hinj hs ht hlt
      (by rwa [abs_of_pos (sub_pos.mpr hlt)] at hgap)
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hgap hpos
    exact (closed_curve_separated_of_lt hp hinj ht hs (sub_pos.mp hpos) hgap).symm

/-- Chords separated from both the diagonal and its periodic copies have
a uniform positive lower bound for a simple closed curve. -/
theorem exists_closed_curve_chord_min {γ : ℝ → (Fin 3 → ℝ)}
    (hc : Continuous γ) (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π))) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ ≤ π) :
    ∃ m > 0, ∀ p ∈ gaussDomain, δ ≤ |p.2 - p.1| →
      |p.2 - p.1| ≤ 2 * π - δ → m ≤ ‖γ p.1 - γ p.2‖ := by
  let gap : ℝ × ℝ → ℝ := fun p => |p.2 - p.1|
  let K := gaussDomain ∩ {p | δ ≤ gap p} ∩ {p | gap p ≤ 2 * π - δ}
  have hgap : Continuous gap := (continuous_snd.sub continuous_fst).abs
  have hK : IsCompact K :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hgap)).inter_right (isClosed_le hgap continuous_const)
  have hne : K.Nonempty := by
    refine ⟨(0, π), ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact ⟨⟨le_rfl, Real.two_pi_pos.le⟩, ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩⟩
    · change δ ≤ |π - 0|
      simpa only [sub_zero, abs_of_pos Real.pi_pos] using hδπ
    · change |π - 0| ≤ 2 * π - δ
      rw [sub_zero, abs_of_pos Real.pi_pos]
      linarith
  let chord : ℝ × ℝ → ℝ := fun p => ‖γ p.1 - γ p.2‖
  have hchord : Continuous chord := ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne hchord.continuousOn
  have hpnear : δ ≤ |p.2 - p.1| := hpK.1.2
  have hpend : |p.2 - p.1| ≤ 2 * π - δ := hpK.2
  have hdistinct := closed_curve_separated hp hinj hpK.1.1.1 hpK.1.1.2
    (hδ.trans_le hpnear) (hpend.trans_lt (sub_lt_self _ hδ))
  refine ⟨chord p, norm_pos_iff.mpr (sub_ne_zero.mpr hdistinct), ?_⟩
  exact fun p' hp' hnear hend => hpmin ⟨⟨hp', hnear⟩, hend⟩

/-- A regular `C²` curve that is simple on one half-open period has
integrable writhe on the full square, including the identified endpoints.
The speed and derivative bounds use the same coordinate estimates as
the near-diagonal kernel theorem. -/
theorem writheKernel_integrable_of_periodic_regular (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ) (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π)))
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure := by
  let K := 3 * M * B
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num)
    ((norm_nonneg _).trans (hM 0))) ((norm_nonneg _).trans (hB 0))
  let δ := min (τ ^ 2 / (2 * (K + 1))) π
  have hden : 0 < 2 * (K + 1) := by positivity
  have hδ : 0 < δ := lt_min (div_pos (pow_pos hτ0 _) hden) Real.pi_pos
  have hδπ : δ ≤ π := min_le_right _ _
  have hKδ : K * δ ≤ τ ^ 2 / 2 := calc
    _ ≤ (K + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ ≤ (K + 1) * (τ ^ 2 / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ = τ ^ 2 / 2 := by field_simp
  let C := 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)
  have hnear (s t : ℝ) (hst : |t - s| ≤ δ) : |writheKernel γ s t| ≤ C :=
    abs_writheKernel_le_near γ hγ hτ0 hτ hB hM s t
      ((mul_le_mul_of_nonneg_left hst hK).trans hKδ)
  obtain ⟨m, hm, hmin⟩ := exists_closed_curve_chord_min hγ.continuous hp hinj hδ hδπ
  apply writheKernel_integrable_of_uniform_bound γ hγ (max C (3 * B ^ 2 / (2 * π * m ^ 2)))
  rintro ⟨s, t⟩ hst
  change |writheKernel γ s t| ≤ _
  by_cases hsmall : |t - s| ≤ δ
  · exact (hnear s t hsmall).trans (le_max_left _ _)
  by_cases hwrap : 2 * π - δ ≤ |t - s|
  · have hper := writheKernel_periodic_right hp (hγ.differentiable (by norm_num)) s
    have hs : s ∈ Set.Icc 0 (2 * π) := hst.1
    have ht : t ∈ Set.Icc 0 (2 * π) := hst.2
    rcases le_total s t with hs' | ht'
    · have habs : |t - 2 * π - s| = 2 * π - |t - s| := by
        rw [abs_of_nonpos (by linarith [ht.2, hs.1]), abs_of_nonneg (sub_nonneg.mpr hs')]
        ring
      have heq : writheKernel γ s t = writheKernel γ s (t - 2 * π) := by
        simpa only [sub_add_cancel] using hper (t - 2 * π)
      rw [heq]
      exact (hnear s (t - 2 * π) (by rw [habs]; linarith)).trans (le_max_left _ _)
    · have habs : |t + 2 * π - s| = 2 * π - |t - s| := by
        rw [abs_of_nonneg (by linarith [ht.1, hs.2]), abs_of_nonpos (sub_nonpos.mpr ht')]
        ring
      rw [← hper t]
      exact (hnear s (t + 2 * π) (by rw [habs]; linarith)).trans (le_max_left _ _)
  have hlarge := lt_of_not_ge hsmall
  have hmid := lt_of_not_ge hwrap
  have hlow : m ≤ ‖γ s - γ t‖ := hmin (s, t) hst hlarge.le hmid.le
  have hsep : γ s ≠ γ t := by
    intro he
    rw [he, sub_self, norm_zero] at hlow
    exact hm.not_ge hlow
  calc
    _ ≤ 3 * B ^ 2 / (2 * π * ‖γ s - γ t‖ ^ 2) := abs_writheKernel_le_far γ hB s t hsep
    _ ≤ 3 * B ^ 2 / (2 * π * m ^ 2) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      gcongr
    _ ≤ max C (3 * B ^ 2 / (2 * π * m ^ 2)) := le_max_right _ _

/-- The Gauss writhe kernel of a simple closed regular `C²` curve is
integrable. Periodicity and the nonvanishing tangent supply all uniform
speed and acceleration bounds from compactness of a single period. -/
theorem writheKernel_integrable_of_closed_regular (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ) (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π))) (hregular : ∀ t, deriv γ t ≠ 0) :
    Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure := by
  have hγ' : ContDiff ℝ 1 (deriv γ) := by
    apply ContDiff.deriv'
    norm_num
    exact hγ
  have hp' := periodic_deriv_curve hp (hγ.differentiable (by norm_num))
  have hp'' := periodic_deriv_curve hp' (hγ'.differentiable (by norm_num))
  have hperNe := Real.two_pi_pos.ne'
  have hspeed : Function.Periodic (fun t => ‖deriv γ t‖) (2 * π) :=
    fun t => congrArg norm (hp' t)
  have hsCompact := hspeed.compact_of_continuous hperNe hγ'.continuous.norm
  obtain ⟨τ, ⟨t₀, ht₀⟩, hmin⟩ := hsCompact.exists_isMinOn
    (Set.range_nonempty _) continuous_id.continuousOn
  have hτ : 0 < τ := ht₀ ▸ norm_pos_iff.mpr (hregular t₀)
  obtain ⟨B, hB⟩ := (hp'.compact_of_continuous hperNe hγ'.continuous).isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := (hp''.compact_of_continuous hperNe
    hγ'.continuous_deriv_one).isBounded.exists_norm_le
  refine writheKernel_integrable_of_periodic_regular γ hγ hp hinj hτ ?_
    (fun t => hB _ (Set.mem_range_self t)) (fun t => hM _ (Set.mem_range_self t))
  intro t
  have hspeedBound : τ ≤ ‖deriv γ t‖ := hmin (Set.mem_range_self t)
  calc
    τ ^ 2 ≤ euclideanLength (deriv γ t) ^ 2 :=
      pow_le_pow_left₀ hτ.le (hspeedBound.trans (norm_le_euclideanLength _)) 2
    _ = dot3 (deriv γ t) (deriv γ t) := by
      rw [euclideanLength, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      simp [dot3, pow_two]

/-- Separation on the parameter circle of period `2π`, evaluated on
the closed parameter square. -/
noncomputable def circularParameterGap (s t : ℝ) : ℝ :=
  min |t - s| (2 * π - |t - s|)

/-- The self Gauss integral after cutting out a band in the circular
parameter distance, including the identified corner points. -/
noncomputable def circularWritheBand (γ : ℝ → (Fin 3 → ℝ)) (δ : ℝ) : ℝ :=
  ∫ p, if circularParameterGap p.1 p.2 < δ then 0 else writheKernel γ p.1 p.2 ∂gaussMeasure

/-- A zero circular gap on the parameter square pairs equal parameters or
periodic copies, in both cases giving zero kernel value. -/
private theorem circular_gap_pos_or_kernel_zero (γ : ℝ → (Fin 3 → ℝ))
    (hγ : Differentiable ℝ γ) (hp : Function.Periodic γ (2 * π))
    {p : ℝ × ℝ} (hmem : p ∈ gaussDomain) :
    0 < circularParameterGap p.1 p.2 ∨ writheKernel γ p.1 p.2 = 0 := by
  have hs : p.1 ∈ Set.Icc 0 (2 * π) := hmem.1
  have ht : p.2 ∈ Set.Icc 0 (2 * π) := hmem.2
  by_cases hdiag : p.1 = p.2
  · right
    rw [hdiag]
    exact writheKernel_diag_eq_zero γ p.2
  have hUpper : |p.2 - p.1| ≤ 2 * π := abs_le.2
    ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
  rcases hUpper.lt_or_eq with hlt | heq
  · exact Or.inl (lt_min (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hdiag))) (sub_pos.mpr hlt))
  right
  rcases le_total p.1 p.2 with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at heq
    have hs0 : p.1 = 0 := by linarith [hs.1, ht.2]
    have htP : p.2 = 2 * π := by linarith
    rw [hs0, htP]
    simpa only [zero_add, writheKernel_diag_eq_zero] using writheKernel_periodic_right hp hγ 0 0
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at heq
    have hsP : p.1 = 2 * π := by linarith [hs.2, ht.1]
    have ht0 : p.2 = 0 := by linarith [hs.2, ht.1]
    rw [hsP, ht0]
    simpa only [zero_add, writheKernel_diag_eq_zero] using
      (writheKernel_periodic_right hp hγ (2 * π) 0).symm

/-- Circular band regularization of the writhe of a simple closed regular
curve converges to the full self Gauss integral. -/
theorem tendsto_circularWritheBand_of_closed_regular (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ) (hp : Function.Periodic γ (2 * π))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * π))) (hregular : ∀ t, deriv γ t ≠ 0) :
    Tendsto (fun δ => circularWritheBand γ δ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussLinking γ γ)) := by
  have hint := writheKernel_integrable_of_closed_regular γ hγ hp hinj hregular
  have hgap : Continuous fun p : ℝ × ℝ => circularParameterGap p.1 p.2 := by
    unfold circularParameterGap
    exact (continuous_snd.sub continuous_fst).abs.min
      (continuous_const.sub ((continuous_snd.sub continuous_fst).abs))
  have hdom : ∀ᵐ p ∂gaussMeasure, p ∈ gaussDomain := by
    rw [gaussMeasure, Measure.prod_restrict]
    exact ae_restrict_mem (MeasurableSet.prod measurableSet_Icc measurableSet_Icc)
  change Tendsto _ _ (nhds (∫ p, writheKernel γ p.1 p.2 ∂gaussMeasure))
  refine tendsto_of_seq_tendsto fun δ hδ => ?_
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun p : ℝ × ℝ => if circularParameterGap p.1 p.2 < δ n then 0 else writheKernel γ p.1 p.2)
      gaussMeasure := by
    let band : Set (ℝ × ℝ) := {p | δ n ≤ circularParameterGap p.1 p.2}
    have heq : (fun p : ℝ × ℝ =>
        if circularParameterGap p.1 p.2 < δ n then 0 else writheKernel γ p.1 p.2) =
      band.indicator (fun p => writheKernel γ p.1 p.2) := by
      funext p
      by_cases h : circularParameterGap p.1 p.2 < δ n <;> simp [band, Set.indicator, h]
    rw [heq]
    exact hint.aestronglyMeasurable.indicator (measurableSet_le measurable_const hgap.measurable)
  refine tendsto_integral_of_dominated_convergence (fun p => |writheKernel γ p.1 p.2|)
    hmeas hint.abs (fun n => Eventually.of_forall fun p => ?_) ?_
  · by_cases h : circularParameterGap p.1 p.2 < δ n <;> simp [h]
  · filter_upwards [hdom] with p hmem
    rcases circular_gap_pos_or_kernel_zero γ (hγ.differentiable (by norm_num)) hp hmem with hs | hz
    · have hlt := hδ.eventually (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hs))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlt] with n hn
      simp [not_lt_of_gt (Set.mem_Iio.mp hn)]
    · simp [hz]

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
