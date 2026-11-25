/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussSoftCutoff

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Ring

/-!
# Oriented vorticity measures

The norm of a tangent or vorticity is pushed into the measure; the
position and normalized direction are pushed forward together. A
product pairing of the resulting measures exactly recovers the
original weighted Gauss interaction.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge
  (cross3_apply_zero cross3_apply_one cross3_apply_two)
open scoped ENNReal NNReal Real

local notation "VorticitySpace" => Fin 3 → ℝ

/-- A vorticity direction has coordinate norm at most one and is
assigned zero when the original vector vanishes. -/
noncomputable def vorticityDirection (u : VorticitySpace) : {v : VorticitySpace // ‖v‖ ≤ 1} :=
  ⟨‖u‖⁻¹ • u, by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    · rw [inv_mul_cancel₀ hu]⟩

/-- The vorticity norm times its direction recovers the original vector. -/
theorem norm_smul_vorticityDirection (u : VorticitySpace) :
    ‖u‖ • (vorticityDirection u).val = u := by
  by_cases hu : u = 0
  · subst u
    simp
  · change ‖u‖ • (‖u‖⁻¹ • u) = u
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]

/-- The direction is measurable including its assigned value at zero. -/
theorem measurable_vorticityDirection : Measurable vorticityDirection := by
  exact Measurable.subtype_mk (measurable_norm.inv.smul measurable_id)

/-- Push the measure weighted by tangent magnitude to position and direction.
The source can be physical volume or the parameter measure of a curve. -/
noncomputable def orientedVorticityMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (position tangent : α → VorticitySpace) : Measure VorticityElement :=
  Measure.map (fun a => (position a, vorticityDirection (tangent a)))
    (μ.withDensity fun a => ‖tangent a‖ₑ)

/-- With measurable position and tangent, the oriented measure has
total mass equal to the integral of the tangent magnitude. -/
theorem orientedVorticityMeasure_univ {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {position tangent : α → VorticitySpace} (hp : Measurable position) (ht : Measurable tangent) :
    orientedVorticityMeasure μ position tangent univ = ∫⁻ a, ‖tangent a‖ₑ ∂μ := by
  have h : Measurable (fun a => (position a, vorticityDirection (tangent a))) :=
    hp.prodMk (measurable_vorticityDirection.comp ht)
  rw [orientedVorticityMeasure, Measure.map_apply h MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- Integrable tangents induce a finite oriented measure. -/
theorem isFiniteMeasure_orientedVorticityMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {position tangent : α → VorticitySpace} (hp : Measurable position) (ht : Measurable tangent)
    (hInt : Integrable tangent μ) :
    IsFiniteMeasure (orientedVorticityMeasure μ position tangent) :=
  ⟨by rw [orientedVorticityMeasure_univ μ hp ht]; exact hInt.hasFiniteIntegral⟩

/-- The softened interaction is measurable for every cutoff including zero. -/
theorem measurable_gaussSoftKernel (δ : ℝ) :
    Measurable (fun p : VorticityElement × VorticityElement => gaussSoftKernel δ p.1 p.2) := by
  let u := fun p : VorticityElement × VorticityElement => p.1.2.val
  let v := fun p : VorticityElement × VorticityElement => p.2.2.val
  let w := fun p : VorticityElement × VorticityElement => p.1.1 - p.2.1
  have hu : Measurable u := measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)
  have hv : Measurable v := measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hw : Measurable w := (measurable_fst.comp measurable_fst).sub (measurable_fst.comp measurable_snd)
  have hp : Measurable fun p => dot3 (u p) (cross3 (v p) (w p)) := by
    simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
    fun_prop
  exact hp.div (by fun_prop)

/-- Putting both magnitudes back into the normalized directions restores
the interaction of the original tangent vectors. -/
private theorem weighted_gaussSoftKernel (δ : ℝ) (x y u v : VorticitySpace) :
    ‖u‖ * ‖v‖ * gaussSoftKernel δ (x, vorticityDirection u) (y, vorticityDirection v) =
      dot3 u (cross3 v (x - y)) / (4 * π * max δ (euclideanLength (x - y)) ^ 3) := by
  have hu := norm_smul_vorticityDirection u
  have hv := norm_smul_vorticityDirection v
  conv_rhs => rw [← hu, ← hv]
  rw [gaussSoftKernel, cross3_smul_left, dot3_smul_left, dot3_smul_right]
  ring

/-- Absolute integrability for the oriented product is equivalent to
absolute integrability of the interaction with the original tangents. -/
theorem integrable_prod_orientedVorticityMeasure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {p u : α → VorticitySpace} {q v : β → VorticitySpace}
    (hp : Measurable p) (hu : Measurable u) (hq : Measurable q) (hv : Measurable v) (δ : ℝ) :
    Integrable (fun s => gaussSoftKernel δ s.1 s.2)
      ((orientedVorticityMeasure μ p u).prod (orientedVorticityMeasure ν q v)) ↔
    Integrable (fun s : α × β => dot3 (u s.1) (cross3 (v s.2) (p s.1 - q s.2)) /
      (4 * π * max δ (euclideanLength (p s.1 - q s.2)) ^ 3)) (μ.prod ν) := by
  have hp' : Measurable (fun a => (p a, vorticityDirection (u a))) :=
    hp.prodMk (measurable_vorticityDirection.comp hu)
  have hq' : Measurable (fun a => (q a, vorticityDirection (v a))) :=
    hq.prodMk (measurable_vorticityDirection.comp hv)
  have hmd : Measurable (fun s : α × β => ‖u s.1‖ₑ * ‖v s.2‖ₑ) :=
    (hu.enorm.comp measurable_fst).mul (hv.enorm.comp measurable_snd)
  have hd : ∀ᵐ s : α × β ∂(μ.prod ν), ‖u s.1‖ₑ * ‖v s.2‖ₑ < ∞ :=
    Eventually.of_forall fun _ => ENNReal.mul_lt_top (by simp) (by simp)
  rw [orientedVorticityMeasure, orientedVorticityMeasure, Measure.map_prod_map _ _ hp' hq',
    integrable_map_measure (measurable_gaussSoftKernel δ).aestronglyMeasurable
      (hp'.prodMap hq').aemeasurable,
    prod_withDensity hu.enorm hv.enorm, integrable_withDensity_iff_integrable_smul' hmd hd]
  refine integrable_congr (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, ENNReal.toReal_mul, toReal_enorm, smul_eq_mul]
  exact weighted_gaussSoftKernel δ (p s.1) (q s.2) (u s.1) (v s.2)

/-- The product measure of two oriented vorticities integrates the
actual regularized kernel of their original position and tangent data. -/
theorem integral_prod_orientedVorticityMeasure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {p u : α → VorticitySpace} {q v : β → VorticitySpace}
    (hp : Measurable p) (hu : Measurable u) (hq : Measurable q) (hv : Measurable v) (δ : ℝ) :
    (∫ s, gaussSoftKernel δ s.1 s.2
      ∂((orientedVorticityMeasure μ p u).prod (orientedVorticityMeasure ν q v))) =
    ∫ s, dot3 (u s.1) (cross3 (v s.2) (p s.1 - q s.2)) /
      (4 * π * max δ (euclideanLength (p s.1 - q s.2)) ^ 3) ∂(μ.prod ν) := by
  have hp' : Measurable (fun a => (p a, vorticityDirection (u a))) :=
    hp.prodMk (measurable_vorticityDirection.comp hu)
  have hq' : Measurable (fun a => (q a, vorticityDirection (v a))) :=
    hq.prodMk (measurable_vorticityDirection.comp hv)
  have hud := hu.enorm
  have hvd := hv.enorm
  rw [orientedVorticityMeasure, orientedVorticityMeasure, Measure.map_prod_map _ _ hp' hq',
    integral_map (hp'.prodMap hq').aemeasurable (measurable_gaussSoftKernel δ).aestronglyMeasurable,
    prod_withDensity hud hvd]
  have hmd : Measurable (fun s : α × β => ‖u s.1‖ₑ * ‖v s.2‖ₑ) :=
    (hud.comp measurable_fst).mul (hvd.comp measurable_snd)
  have hd : ∀ᵐ s : α × β ∂(μ.prod ν), ‖u s.1‖ₑ * ‖v s.2‖ₑ < ∞ :=
    Eventually.of_forall fun _ => ENNReal.mul_lt_top (by simp) (by simp)
  rw [integral_withDensity_eq_integral_toReal_smul hmd hd]
  apply integral_congr_ae
  filter_upwards with s
  simp only [ENNReal.toReal_mul, toReal_enorm, smul_eq_mul]
  exact weighted_gaussSoftKernel δ (p s.1) (q s.2) (u s.1) (v s.2)

/-- An absolute interaction restricted by the positions can be
computed directly in the original parameters, with the original
tangent magnitudes and orientation. -/
theorem setIntegral_abs_prod_orientedVorticityMeasure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {p u : α → VorticitySpace} {q v : β → VorticitySpace}
    (hp : Measurable p) (hu : Measurable u) (hq : Measurable q) (hv : Measurable v)
    (δ : ℝ) {S : Set (VorticitySpace × VorticitySpace)} (hS : MeasurableSet S) :
    (∫ s in {s : VorticityElement × VorticityElement | (s.1.1, s.2.1) ∈ S},
      |gaussSoftKernel δ s.1 s.2| ∂((orientedVorticityMeasure μ p u).prod
        (orientedVorticityMeasure ν q v))) =
    ∫ s in {s : α × β | (p s.1, q s.2) ∈ S},
      |dot3 (u s.1) (cross3 (v s.2) (p s.1 - q s.2)) /
        (4 * π * max δ (euclideanLength (p s.1 - q s.2)) ^ 3)| ∂(μ.prod ν) := by
  have hp' : Measurable (fun a => (p a, vorticityDirection (u a))) :=
    hp.prodMk (measurable_vorticityDirection.comp hu)
  have hq' : Measurable (fun a => (q a, vorticityDirection (v a))) :=
    hq.prodMk (measurable_vorticityDirection.comp hv)
  have htarget :
      MeasurableSet {s : VorticityElement × VorticityElement | (s.1.1, s.2.1) ∈ S} :=
    (measurable_fst.prodMap measurable_fst) hS
  have hsource : MeasurableSet {s : α × β | (p s.1, q s.2) ∈ S} :=
    (hp.prodMap hq) hS
  let e := Prod.map (fun a => (p a, vorticityDirection (u a)))
    (fun a => (q a, vorticityDirection (v a)))
  let A := {s : α × β | (p s.1, q s.2) ∈ S}
  have hAbs : Measurable (fun s : VorticityElement × VorticityElement => |gaussSoftKernel δ s.1 s.2|) :=
    continuous_abs.measurable.comp (measurable_gaussSoftKernel δ)
  rw [orientedVorticityMeasure, orientedVorticityMeasure, Measure.map_prod_map _ _ hp' hq',
    setIntegral_map htarget hAbs.aestronglyMeasurable (hp'.prodMap hq').aemeasurable,
    prod_withDensity hu.enorm hv.enorm]
  change (∫ s in A, |gaussSoftKernel δ (e s).1 (e s).2| ∂((μ.prod ν).withDensity
    fun s => ‖u s.1‖ₑ * ‖v s.2‖ₑ)) = _
  have hmd : Measurable (fun s : α × β => ‖u s.1‖ₑ * ‖v s.2‖ₑ) :=
    (hu.enorm.comp measurable_fst).mul (hv.enorm.comp measurable_snd)
  have hd : ∀ᵐ s : α × β ∂((μ.prod ν).restrict A), ‖u s.1‖ₑ * ‖v s.2‖ₑ < ∞ :=
    Eventually.of_forall fun _ => ENNReal.mul_lt_top (by simp) (by simp)
  rw [restrict_withDensity hsource, integral_withDensity_eq_integral_toReal_smul hmd hd]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [ENNReal.toReal_mul, toReal_enorm, smul_eq_mul]
  rw [← abs_of_nonneg (mul_nonneg (norm_nonneg (u s.1)) (norm_nonneg (v s.2))), ← abs_mul]
  exact congrArg abs (weighted_gaussSoftKernel δ (p s.1) (q s.2) (u s.1) (v s.2))

/-- At zero cutoff the oriented continuum measure exactly recovers the
original untruncated Biot–Savart pairing. -/
theorem integral_orientedVorticityMeasure_eq_crossPairing {ω φ : VorticitySpace → VorticitySpace}
    (hω : Measurable ω) (hφ : Measurable φ) :
    (∫ s, gaussSoftKernel 0 s.1 s.2 ∂((orientedVorticityMeasure volume id ω).prod
      (orientedVorticityMeasure volume id φ))) = crossPairing ω φ := by
  have hlen (x : VorticitySpace) : 0 ≤ euclideanLength x := norm_nonneg _
  rw [integral_prod_orientedVorticityMeasure volume volume measurable_id hω measurable_id hφ]
  simp only [id_eq, max_eq_right (hlen _), crossPairing, bsPairKernel]

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
