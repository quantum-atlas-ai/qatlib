/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticAxisIntegral
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.KernelBounds

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Dominated convergence of the magnetic Gauss integrals

A compact central region stays uniformly separated from the pole.
Outside that region the chord grows at least linearly in the rescaled
parameter. The resulting integrable bound permits the axis limit
over the expanding intervals.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.SuperfluidHel18.CenterlineCL
  (euclideanLength norm_le_euclideanLength continuous_euclideanLength
    abs_dot3_le norm_cross3_le_mul)
open MeasureTheory Filter Set
open scoped Topology

/-- The first-angle interval after rescaling by the magnetic label. -/
def rescaledMagneticInterval (u : ℝ) : Set ℝ :=
  {s | |u * s| ≤ Real.pi}

/-- Integration on the full first-parameter line and one full pole period. -/
def magneticAxisMeasure : Measure (ℝ × ℝ) :=
  volume.prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))

/-- The kernel on the rescaled interval, extended by zero on the rest
of the line so all labels use the same measure. -/
def truncatedMagneticGaussKernel (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  (rescaledMagneticInterval u).indicator (fun s => rescaledMagneticGaussKernel u s p.2) p.1

private def magneticChord (u s t : ℝ) : Fin 3 → ℝ :=
  rescaledMagneticCircle u s - ![0, Real.cos t, -Real.sin t]

private def magneticPoleTangent (t : ℝ) : Fin 3 → ℝ :=
  ![0, -Real.sin t, -Real.cos t]

/-- The separation on the central parameter interval is uniformly
positive at small positive real labels. -/
private theorem eventually_central_chord_lower :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ s ∈ Icc (-Real.pi) Real.pi,
      ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi), 1 / 2 ≤ euclideanLength (magneticChord u s t) := by
  let K := Icc (0 : ℝ) 1 ×ˢ (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) (2 * Real.pi))
  let F (q : ℝ × (ℝ × ℝ)) := euclideanLength (magneticChord q.1 q.2.1 q.2.2)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hP : Continuous (fun q : ℝ × (ℝ × ℝ) => rescaledMagneticCircle q.1 q.2.1) :=
    continuous_rescaledMagneticCircle.comp (continuous_fst.prodMk continuous_snd.fst)
  have hQ : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      (![(0 : ℝ), Real.cos q.2.2, -Real.sin q.2.2] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro j
    fin_cases j <;> fun_prop
  have hF : Continuous F := continuous_euclideanLength.comp (hP.sub hQ)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hF.continuousOn) (1 / 2) (by norm_num)
  have hm : ∀ᶠ u : ℝ in 𝓝[>] 0, u < min δ 1 :=
    (eventually_lt_nhds (lt_min hδ zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0), hm] with u hu hsmall
  have hu0 : 0 < u := hu
  intro s hs t ht
  have hx : (u, (s, t)) ∈ K := ⟨⟨hu0.le, (lt_min_iff.mp hsmall).2.le⟩, hs, ht⟩
  have hy : ((0 : ℝ), (s, t)) ∈ K := ⟨⟨le_rfl, zero_le_one⟩, hs, ht⟩
  have hdist : dist (u, (s, t)) ((0 : ℝ), (s, t)) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_pos hu0, max_eq_left hu0.le]
    exact (lt_min_iff.mp hsmall).1
  have hclose := hmod _ hx _ hy hdist
  have hzero : F (0, (s, t)) = Real.sqrt (s ^ 2 + 1) := by
    change euclideanLength (magneticChord 0 s t) = _
    rw [magneticChord, rescaledMagneticCircle_zero, euclideanLength_magnetic_axis_chord]
  have hlarge : 1 ≤ Real.sqrt (s ^ 2 + 1) := by
    calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith [sq_nonneg s])
  rw [Real.dist_eq, hzero, abs_lt] at hclose
  change 1 / 2 ≤ F (u, (s, t))
  linarith only [hclose.1, hlarge]

/-- The two rescaled tangent vectors have uniformly bounded coordinate norms. -/
private theorem magnetic_tangent_norms_le (u s t : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖rescaledMagneticTangent u s‖ ≤ 2 ∧ ‖magneticPoleTangent t‖ ≤ 1 := by
  have hR : Real.sqrt (u ^ 2 + 1) ≤ 2 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
  constructor
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_
    intro i
    fin_cases i
    · change ‖-Real.cos (u * s)‖ ≤ 2
      rw [Real.norm_eq_abs, abs_neg]
      exact (Real.abs_cos_le_one _).trans (by norm_num)
    · change ‖-Real.sqrt (u ^ 2 + 1) * Real.sin (u * s)‖ ≤ 2
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)).trans
        (by simpa only [mul_one] using hR)
    · change ‖-u * Real.cos (u * s)‖ ≤ 2
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hu]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hu.le).trans
        (by simpa only [mul_one] using hu1.trans (by norm_num : (1 : ℝ) ≤ 2))
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_
    intro i
    fin_cases i
    · change ‖(0 : ℝ)‖ ≤ 1
      simp
    · change ‖-Real.sin t‖ ≤ 1
      simpa only [Real.norm_eq_abs, abs_neg] using Real.abs_sin_le_one t
    · change ‖-Real.cos t‖ ≤ 1
      simpa only [Real.norm_eq_abs, abs_neg] using Real.abs_cos_le_one t

/-- The tangent bounds and the cubic denominator give inverse-square
decay in the chord length. -/
private theorem abs_rescaledMagneticGaussKernel_le (u s t : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hd : 0 < euclideanLength (magneticChord u s t)) :
    |rescaledMagneticGaussKernel u s t| ≤ 3 / (Real.pi * euclideanLength (magneticChord u s t) ^ 2) := by
  let a := rescaledMagneticTangent u s
  let b := magneticPoleTangent t
  let d := magneticChord u s t
  let L := euclideanLength d
  obtain ⟨ha, hb⟩ := magnetic_tangent_norms_le u s t hu hu1
  have hc : ‖Qatlib.Papers.KnottedLight08.HopfField.cross3 a b‖ ≤ 4 :=
    (norm_cross3_le_mul a b).trans (by
      have ha' : 2 * ‖a‖ ≤ 4 := by linarith
      calc
        2 * ‖a‖ * ‖b‖ ≤ 4 * 1 :=
          mul_le_mul ha' hb (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num)
  have hbound : |Qatlib.Papers.KnottedLight08.HopfField.dot3
      (Qatlib.Papers.KnottedLight08.HopfField.cross3 a b) d| ≤ 12 * L :=
    (abs_dot3_le _ _).trans (by
      have hc' : (3 : ℝ) * ‖Qatlib.Papers.KnottedLight08.HopfField.cross3 a b‖ ≤ 12 := by
        linarith
      exact mul_le_mul hc' (norm_le_euclideanLength d) (norm_nonneg _) (by norm_num))
  change |_ / (4 * Real.pi * L ^ 3)| ≤ 3 / (Real.pi * L ^ 2)
  have hL : 0 < L := hd
  rw [abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi * L ^ 3)]
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi * L ^ 3)).2
  calc
    _ ≤ 12 * L := hbound
    _ = _ := by
      field_simp
      norm_num

/-- Combining the central and tail estimates bounds the reciprocal
squared chord by an integrable reciprocal quadratic. -/
private theorem eventually_chord_quadratic_lower :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ s t, |u * s| ≤ Real.pi →
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      0 < euclideanLength (magneticChord u s t) ∧
      1 + s ^ 2 ≤ 4 * (1 + Real.pi ^ 2) * euclideanLength (magneticChord u s t) ^ 2 := by
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
    eventually_central_chord_lower] with u hu hc
  have hu0 : 0 < u := hu
  intro s t hs ht
  let L := euclideanLength (magneticChord u s t)
  by_cases hsmall : |s| ≤ Real.pi
  · have hL : 1 / 2 ≤ L := hc s (abs_le.mp hsmall) t ht
    have hsq : s ^ 2 ≤ Real.pi ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s) hsmall 2
    have h2L : 1 ≤ 2 * L := by linarith
    have hLs : 1 ≤ 4 * L ^ 2 := by
      nlinarith only [pow_le_pow_left₀ zero_le_one h2L 2]
    refine ⟨by linarith, ?_⟩
    calc
      1 + s ^ 2 ≤ 1 + Real.pi ^ 2 := by linarith
      _ ≤ (1 + Real.pi ^ 2) * (4 * L ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hLs (by positivity : 0 ≤ 1 + Real.pi ^ 2)
      _ = _ := by ring
  · have hlarge : Real.pi ≤ |s| := (lt_of_not_ge hsmall).le
    have hh := le_rescaledMagneticCircle_pole_chord u s t hu0 hs hlarge
    rw [magneticPoleCircleAt_zero_coords] at hh
    change |s| / Real.pi ≤ L at hh
    have hL : 1 ≤ L :=
      ((le_div_iff₀ Real.pi_pos).2 (by simpa only [one_mul] using hlarge)).trans hh
    have happ : |s| ≤ Real.pi * L := by
      simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).1 hh
    have hsq : s ^ 2 ≤ Real.pi ^ 2 * L ^ 2 := by
      simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg s) happ 2
    have hLs : 1 ≤ L ^ 2 := by
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hL 2
    refine ⟨by linarith, ?_⟩
    nlinarith only [hsq, hLs, mul_nonneg (sq_nonneg Real.pi) (sq_nonneg L)]

/-- For sufficiently small labels the entire truncated kernel is
dominated almost everywhere by a fixed integrable function. -/
private theorem eventually_truncatedMagneticGaussKernel_bound :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ᵐ p ∂magneticAxisMeasure,
      ‖truncatedMagneticGaussKernel u p‖ ≤
        (12 * (1 + Real.pi ^ 2) / Real.pi) * (1 + p.1 ^ 2)⁻¹ := by
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0), hsmall,
    eventually_chord_quadratic_lower] with u hu hu1 hL
  have ht : ∀ᵐ p ∂magneticAxisMeasure, p.2 ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    have hm : magneticAxisMeasure = ((volume : Measure ℝ).prod volume).restrict
        ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := by
      rw [magneticAxisMeasure, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [hm]
    exact (ae_restrict_mem ((MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod
      measurableSet_Icc)).mono (fun _ hp => hp.2)
  filter_upwards [ht] with p hp
  by_cases hs : |u * p.1| ≤ Real.pi
  · have hs' : p.1 ∈ rescaledMagneticInterval u := hs
    have ⟨hpos, hsq⟩ := hL p.1 p.2 hs hp
    let L := euclideanLength (magneticChord u p.1 p.2)
    have hpos' : 0 < L := hpos
    change 1 + p.1 ^ 2 ≤ 4 * (1 + Real.pi ^ 2) * L ^ 2 at hsq
    rw [truncatedMagneticGaussKernel, indicator_of_mem hs', Real.norm_eq_abs]
    apply (abs_rescaledMagneticGaussKernel_le u p.1 p.2 hu hu1.le hpos).trans
    have hj : 0 < (1 : ℝ) + p.1 ^ 2 := by positivity
    rw [← div_eq_mul_inv, div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * L ^ 2)
      (by positivity : 0 < Real.pi * (1 + p.1 ^ 2))).2
    calc
      3 * (Real.pi * (1 + p.1 ^ 2)) ≤ 3 * Real.pi * (4 * (1 + Real.pi ^ 2) * L ^ 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  · have hs' : p.1 ∉ rescaledMagneticInterval u := hs
    rw [truncatedMagneticGaussKernel, indicator_of_notMem hs', norm_zero]
    positivity

/-- The actual rescaled kernels are measurable, including at excluded
parameters where they are extended by zero. -/
private theorem measurable_truncatedMagneticGaussKernel (u : ℝ) :
    Measurable (truncatedMagneticGaussKernel u) := by
  have hP : Continuous (fun s : ℝ => rescaledMagneticCircle u s) :=
    continuous_rescaledMagneticCircle.comp (continuous_const.prodMk continuous_id)
  have hT : Continuous (fun s : ℝ => rescaledMagneticTangent u s) :=
    continuous_rescaledMagneticTangent.comp (continuous_const.prodMk continuous_id)
  have hQ : Continuous (fun t : ℝ => (![(0 : ℝ), Real.cos t, -Real.sin t] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro j
    fin_cases j <;> fun_prop
  have hR : Continuous magneticPoleTangent := by
    unfold magneticPoleTangent
    apply continuous_pi
    intro j
    fin_cases j <;> fun_prop
  have hd : Continuous (fun p : ℝ × ℝ => magneticChord u p.1 p.2) :=
    (hP.comp continuous_fst).sub (hQ.comp continuous_snd)
  have hg : Measurable (fun p : ℝ × ℝ => rescaledMagneticGaussKernel u p.1 p.2) := by
    change Measurable (fun p : ℝ × ℝ => Qatlib.Papers.KnottedLight08.HopfField.dot3
      (Qatlib.Papers.KnottedLight08.HopfField.cross3
        (rescaledMagneticTangent u p.1) (magneticPoleTangent p.2))
        (magneticChord u p.1 p.2) / (4 * Real.pi * euclideanLength (magneticChord u p.1 p.2) ^ 3))
    have ha (j : Fin 3) := continuous_pi_iff.mp hT j
    have hb (j : Fin 3) := continuous_pi_iff.mp hR j
    have hc (j : Fin 3) := continuous_pi_iff.mp hd j
    simp only [Qatlib.Papers.KnottedLight08.HopfField.dot3,
      Qatlib.Papers.SuperfluidHel18.VanishCharge.cross3_apply_zero,
      Qatlib.Papers.SuperfluidHel18.VanishCharge.cross3_apply_one,
      Qatlib.Papers.SuperfluidHel18.VanishCharge.cross3_apply_two]
    fun_prop
  have hs : MeasurableSet (rescaledMagneticInterval u) :=
    measurableSet_le (by fun_prop : Measurable (fun s : ℝ => |u * s|)) measurable_const
  change Measurable ((Prod.fst ⁻¹' rescaledMagneticInterval u).indicator
    (fun p : ℝ × ℝ => rescaledMagneticGaussKernel u p.1 p.2))
  exact hg.indicator (measurable_fst hs)

/-- The integrals on the expanding rescaled intervals converge to the
integral of the axis–pole kernel, which has value one. -/
theorem tendsto_truncatedMagneticGaussIntegral :
    Tendsto (fun u => ∫ p, truncatedMagneticGaussKernel u p ∂magneticAxisMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  rw [← integral_magnetic_axis_pole_kernel]
  change Tendsto _ _ (𝓝 (∫ p, rescaledMagneticGaussKernel 0 p.1 p.2 ∂magneticAxisMeasure))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p : ℝ × ℝ => (12 * (1 + Real.pi ^ 2) / Real.pi) * (1 + p.1 ^ 2)⁻¹)
  · exact Eventually.of_forall fun u => (measurable_truncatedMagneticGaussKernel u).aestronglyMeasurable
  · exact eventually_truncatedMagneticGaussKernel_bound
  · have hi : Integrable (fun s : ℝ => (12 * (1 + Real.pi ^ 2) / Real.pi) * (1 + s ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    simpa only [magneticAxisMeasure, smul_eq_mul, mul_one] using
      hi.smul_prod (integrable_const (μ := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) (1 : ℝ))
  · apply Eventually.of_forall
    intro p
    rw [rescaledMagneticGaussKernel_zero]
    apply (tendsto_rescaledMagneticGaussKernel p.1 p.2).congr'
    have hc : ContinuousAt (fun u : ℝ => |u * p.1|) 0 := by fun_prop
    have hs : ∀ᶠ u in 𝓝[>] (0 : ℝ), |u * p.1| < Real.pi :=
      (hc.eventually_lt continuousAt_const (by simpa only [zero_mul, abs_zero] using Real.pi_pos)
        ).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs] with u hu
    have hm : p.1 ∈ rescaledMagneticInterval u := hu.le
    rw [truncatedMagneticGaussKernel, indicator_of_mem hm]

end Qatlib.Papers.KnottedLight08.NullLinking
