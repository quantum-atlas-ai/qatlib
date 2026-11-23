/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Exact momentum-square transport on the torus

The correlated two-particle angular transform is handled through the genuine surjective
sum/difference homomorphism of the angular torus. Haar measure preservation supplies the
normalization and product-law transport needed for packet concentration estimates.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

variable (T : ℝ) [Fact (0 < T)]

/-- The actual sum/difference momentum map on the angular torus. -/
def torusMix : (AddCircle T × AddCircle T) →+ (AddCircle T × AddCircle T) where
  toFun p := (p.1 + p.2, p.1 - p.2)
  map_zero' := by simp
  map_add' p q := by
    apply Prod.ext <;> dsimp <;> abel

omit [Fact (0 < T)] in
/-- The two angular momentum coordinates depend continuously on the input torus. -/
theorem torusMix_continuous : Continuous (torusMix T) := by
  change Continuous (fun p : AddCircle T × AddCircle T => (p.1 + p.2, p.1 - p.2))
  fun_prop

omit [Fact (0 < T)] in
/-- Every pair of angular momenta has an actual preimage under the sum/difference map. -/
theorem torusMix_surjective : Function.Surjective (torusMix T) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨((((a + b) / 2 : ℝ) : AddCircle T), (((a - b) / 2 : ℝ) : AddCircle T)), ?_⟩
  apply Prod.ext
  · change (((a + b) / 2 : ℝ) : AddCircle T) + (((a - b) / 2 : ℝ) : AddCircle T) = _
    rw [← AddCircle.coe_add]
    congr 1
    ring
  · change (((a + b) / 2 : ℝ) : AddCircle T) - (((a - b) / 2 : ℝ) : AddCircle T) = _
    rw [← AddCircle.coe_sub]
    congr 1
    ring

/-- The exact sum/difference angular transform preserves the product Haar measure. -/
theorem torusMix_measure : MeasurePreserving (torusMix T)
    ((volume : Measure (AddCircle T)).prod volume)
    ((volume : Measure (AddCircle T)).prod volume) := by
  exact (torusMix T).measurePreserving (torusMix_continuous T) (torusMix_surjective T) rfl

/-- Integration of measurable spectral observables is unchanged by the physical angular transport. -/
theorem torusMix_integral (f : AddCircle T × AddCircle T → ℝ)
    (hf : AEStronglyMeasurable f ((volume : Measure (AddCircle T)).prod volume)) :
    ∫ p : AddCircle T × AddCircle T, f (torusMix T p)
        ∂((volume : Measure (AddCircle T)).prod volume) =
      ∫ p : AddCircle T × AddCircle T, f p
        ∂((volume : Measure (AddCircle T)).prod volume) := by
  have h := torusMix_measure T
  have hf' : AEStronglyMeasurable f
      (Measure.map (torusMix T) ((volume : Measure (AddCircle T)).prod volume)) := by
    rw [h.map_eq]
    exact hf
  rw [← integral_map h.measurable.aemeasurable hf', h.map_eq]


/-- Integrating over the relative angle gives the center-angle marginal of an observable. -/
def mixedMarginal (f : AddCircle T × AddCircle T → ℝ) (s : AddCircle T) : ℝ :=
  ∫ t : AddCircle T, f (s + t, s - t)

/-- The relative angular integration makes the center marginal invariant under a half-period. -/
theorem mixedMarginal_half (f : AddCircle T × AddCircle T → ℝ) (s : AddCircle T) :
    mixedMarginal T f (s + ((T / 2 : ℝ) : AddCircle T)) = mixedMarginal T f s := by
  let q : AddCircle T := ((T / 2 : ℝ) : AddCircle T)
  have hq : q + q = 0 := by
    dsimp [q]
    rw [← AddCircle.coe_add, add_halves, AddCircle.coe_period]
  have hqneg : q = -q := eq_neg_iff_add_eq_zero.mpr hq
  have hp (t : AddCircle T) : (s + q + t, s + q - t) = (s + (t + q), s - (t + q)) := by
    apply Prod.ext
    · abel
    · exact (congrArg (fun r => s + r - t) hqneg).trans (by abel)
  unfold mixedMarginal
  change (∫ t : AddCircle T, f (s + q + t, s + q - t)) = _
  simp_rw [hp]
  exact (measurePreserving_add_right (volume : Measure (AddCircle T)) q).integral_comp
    (MeasurableEquiv.addRight q).measurableEmbedding (fun t => f (s + t, s - t))

/-- The lifted center-angle marginal has half the original angular period. -/
theorem mixedMarginal_periodic (f : AddCircle T × AddCircle T → ℝ) :
    Function.Periodic (fun s : ℝ => mixedMarginal T f (s : AddCircle T)) (T / 2) := by
  intro s
  change mixedMarginal T f (((s + T / 2 : ℝ) : AddCircle T)) = _
  rw [AddCircle.coe_add]
  exact mixedMarginal_half T f _

/-- Compressing the center angular coordinate by two leaves the full-period marginal integral unchanged. -/
theorem mixedMarginal_compress (f : AddCircle T × AddCircle T → ℝ)
    (hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s : ℝ => mixedMarginal T f (s : AddCircle T)) volume a b) :
    (∫ s in -(T / 2)..T / 2, mixedMarginal T f ((s / 2 : ℝ) : AddCircle T)) =
      ∫ s in -(T / 2)..T / 2, mixedMarginal T f (s : AddCircle T) := by
  let g := fun s : ℝ => mixedMarginal T f (s : AddCircle T)
  have hg := mixedMarginal_periodic T f
  have hperiod := hg.intervalIntegral_add_zsmul_eq 2 (-(T / 2)) hint
  have hstart := hg.intervalIntegral_add_eq (-(T / 2)) (-(T / 2) / 2)
  have heq1 : -(T / 2) + (2 : ℤ) • (T / 2) = T / 2 := by ring
  have heq2 : -(T / 2) + T / 2 = 0 := by ring
  have heq3 : -(T / 2) / 2 + T / 2 = (T / 2) / 2 := by ring
  rw [heq1, heq2] at hperiod
  rw [heq2, heq3] at hstart
  change (∫ s in -(T / 2)..T / 2, g (s / 2)) = ∫ s in -(T / 2)..T / 2, g s
  rw [intervalIntegral.integral_comp_div (f := g) (by norm_num : (2 : ℝ) ≠ 0)]
  change (2 : ℝ) • ∫ s in -(T / 2) / 2..(T / 2) / 2, g s = _
  rw [← hstart]
  simpa only [zsmul_eq_mul, smul_eq_mul, Int.cast_ofNat] using hperiod.symm


/-- A full real angular period represents the exact Haar integral of a torus observable. -/
theorem period_integral (f : AddCircle T → ℝ) :
    (∫ s in -(T / 2)..T / 2, f (s : AddCircle T)) = ∫ s : AddCircle T, f s := by
  simpa only [show -(T / 2) + T = T / 2 by ring] using
    AddCircle.intervalIntegral_preimage T (-(T / 2)) f

/-- The relative real-period integral is exactly the genuine sum/difference torus marginal. -/
theorem mixedMarginal_real (f : AddCircle T × AddCircle T → ℝ) (s : ℝ) :
    (∫ t in -(T / 2)..T / 2,
      f (((s + t : ℝ) : AddCircle T), ((s - t : ℝ) : AddCircle T))) =
      mixedMarginal T f (s : AddCircle T) := by
  simp_rw [AddCircle.coe_add, AddCircle.coe_sub]
  exact period_integral T (fun t => f ((s : AddCircle T) + t, (s : AddCircle T) - t))

/-- Exact angular-square transport for every integrable torus observable. -/
theorem angular_square_transport (f : AddCircle T × AddCircle T → ℝ)
    (hf : Integrable f ((volume : Measure (AddCircle T)).prod volume))
    (hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s : ℝ => mixedMarginal T f (s : AddCircle T)) volume a b) :
    (∫ s in -(T / 2)..T / 2, ∫ t in -(T / 2)..T / 2,
      f (((s / 2 + t : ℝ) : AddCircle T), ((s / 2 - t : ℝ) : AddCircle T))) =
      ∫ s in -(T / 2)..T / 2, ∫ t in -(T / 2)..T / 2,
        f ((s : AddCircle T), (t : AddCircle T)) := by
  simp_rw [mixedMarginal_real]
  rw [mixedMarginal_compress T f hint, period_integral]
  have hcomp : Integrable (fun p => f (torusMix T p))
      ((volume : Measure (AddCircle T)).prod volume) :=
    (torusMix_measure T).integrable_comp_of_integrable hf
  have hmarg : (∫ s : AddCircle T, mixedMarginal T f s) =
      ∫ p : AddCircle T × AddCircle T, f (torusMix T p)
        ∂((volume : Measure (AddCircle T)).prod volume) := by
    exact MeasureTheory.integral_integral hcomp
  rw [hmarg, torusMix_integral T f hf.aestronglyMeasurable]
  symm
  have hinner (s : ℝ) : (∫ t in -(T / 2)..T / 2,
      f ((s : AddCircle T), (t : AddCircle T))) =
      ∫ t : AddCircle T, f ((s : AddCircle T), t) :=
    period_integral T (fun t => f ((s : AddCircle T), t))
  simp_rw [hinner]
  rw [period_integral T (fun s => ∫ t : AddCircle T, f (s, t))]
  exact MeasureTheory.integral_integral hf

end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
