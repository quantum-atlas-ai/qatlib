/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.MovingAirfoil

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The far-boundary term in the moving airfoil impulse law

[Musser2019Superfoil], equations (1) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
Exhausting the reference plane identifies the infinite-contour
term in the impulse law for a translating localized soft potential.
An integrable difference of endpoint momenta suffices. The far flux
vanishes when the boundary deviation from a spatially uniform far
stress is uniformly of order `o(1/R)`, where `R` is the square radius.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Filter Set MeasureTheory
open scoped Topology

/-- The difference of endpoint laboratory momentum densities at the
same reference point of the translating plane. -/
def gpeMovingMomentumChange (hbar : ℝ) (ψ : GPESpacetime → ℂ) (η : ℝ → ℝ × ℝ)
    (k : Fin 2) (t₀ t₁ : ℝ) (x : ℝ × ℝ) : ℝ :=
  gpeMomentum hbar ψ k (t₁, x + η t₁) - gpeMomentum hbar ψ k (t₀, x + η t₀)

/-- The impulse due to the relative outward flux along the translating
square of radius `R` in the reference plane. -/
def gpeMovingSquareFluxImpulse (mass gint hbar : ℝ) (ψ : GPESpacetime → ℂ)
    (η : ℝ → ℝ × ℝ) (k : Fin 2) (t₀ t₁ R : ℝ) : ℝ :=
  ∫ t in t₀..t₁, gpeMovingRectangleFlux mass gint hbar ψ η k (-R, -R) (R, R) t

/-- Increasing the radius of the reference square enlarges its domain. -/
private theorem reference_square_subset {r R : ℝ} (h : r ≤ R) :
    Icc (-r, -r) (r, r) ⊆ Icc (-R, -R) (R, R) :=
  Icc_subset_Icc ⟨neg_le_neg h, neg_le_neg h⟩ ⟨h, h⟩

/-- The reference plane is exhausted by all real-radius squares. -/
private theorem iUnion_reference_square :
    (⋃ R : ℝ, Icc (-R, -R) (R, R)) = (univ : Set (ℝ × ℝ)) := by
  apply eq_univ_of_forall
  intro x
  let R := max |x.1| |x.2|
  have hx₁ := abs_le.mp (le_max_left |x.1| |x.2|)
  have hx₂ := abs_le.mp (le_max_right |x.1| |x.2|)
  exact mem_iUnion.mpr ⟨R, ⟨⟨hx₁.1, hx₂.1⟩, ⟨hx₁.2, hx₂.2⟩⟩⟩

/-- An integrable difference of endpoint laboratory momenta gives the
limit of the finite moving-square momentum changes. Each endpoint
density may have a nonintegrable uniform background. -/
theorem tendsto_gpeMovingSquareMomentumChange (hbar : ℝ) {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 2 ψ) (η : ℝ → ℝ × ℝ) (k : Fin 2) (t₀ t₁ : ℝ)
    (hE : Integrable (gpeMovingMomentumChange hbar ψ η k t₀ t₁)) :
    Tendsto (fun R : ℝ =>
      gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₁ -
        gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₀)
      atTop (𝓝 (∫ x, gpeMovingMomentumChange hbar ψ η k t₀ t₁ x)) := by
  let E := gpeMovingMomentumChange hbar ψ η k t₀ t₁
  let Sq (R : ℝ) : Set (ℝ × ℝ) := Icc (-R, -R) (R, R)
  have hm : Monotone Sq := fun _ _ hr => reference_square_subset hr
  have hE' : IntegrableOn E (⋃ R, Sq R) := hE.integrableOn
  have h := tendsto_setIntegral_of_monotone (fun R => (measurableSet_Icc : MeasurableSet (Sq R)))
    hm hE'
  change Tendsto _ _ (𝓝 (∫ x in ⋃ R : ℝ, Icc (-R, -R) (R, R), E x)) at h
  rw [iUnion_reference_square, setIntegral_univ] at h
  apply h.congr'
  filter_upwards with R
  have hPc (t : ℝ) : Continuous (fun x : ℝ × ℝ => gpeMomentum hbar ψ k (t, x + η t)) :=
    (contDiff_gpeMomentum hbar k hψ).continuous.comp
      (continuous_const.prodMk (continuous_id.add continuous_const))
  change (∫ x in Icc (-R, -R) (R, R), E x) = _
  unfold E gpeMovingMomentumChange
  rw [integral_sub ((hPc t₁).continuousOn.integrableOn_compact isCompact_Icc)
    ((hPc t₀).continuousOn.integrableOn_compact isCompact_Icc),
    setIntegral_translate_rectangle (fun y => gpeMomentum hbar ψ k (t₁, y)) (-R, -R) (R, R) (η t₁),
    setIntegral_translate_rectangle (fun y => gpeMomentum hbar ψ k (t₀, y)) (-R, -R) (R, R) (η t₀)]
  rfl

/-- The actual far-boundary flux impulse converges whenever the
reference endpoint momentum difference is integrable. Its limit is the
negative reaction impulse minus the whole-plane momentum change. -/
theorem tendsto_gpeMovingSquareFluxImpulse_of_momentumChange (mass gint hbar : ℝ)
    {W : ℝ × ℝ → ℝ} {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hW : ContDiff ℝ 1 W) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar (gpeTranslatingPotential η W) ψ p)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) (hslab : Icc t₀ t₁ ×ˢ (univ : Set (ℝ × ℝ)) ⊆ U)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hWout : ∀ y ∉ Icc (-R₀, -R₀) (R₀, R₀), W y = 0)
    (k : Fin 2) (hE : Integrable (gpeMovingMomentumChange hbar ψ η k t₀ t₁)) :
    Tendsto (gpeMovingSquareFluxImpulse mass gint hbar ψ η k t₀ t₁) atTop
      (𝓝 (-(∫ t in t₀..t₁, gpeAirfoilReactionForce ψ η W k t) -
        (∫ x, gpeMovingMomentumChange hbar ψ η k t₀ t₁ x))) := by
  let I := -(∫ t in t₀..t₁, gpeAirfoilReactionForce ψ η W k t)
  have hm := tendsto_gpeMovingSquareMomentumChange hbar (hψ.of_le (by norm_num))
    η k t₀ t₁ hE
  apply ((tendsto_const_nhds (x := I)).sub hm).congr'
  filter_upwards [eventually_ge_atTop R₀] with R hRR
  have hp := hR₀.trans_le hRR
  have hbox : MapsTo (gpeTranslate η) (Icc t₀ t₁ ×ˢ Icc (-R, -R) (R, R)) U :=
    fun x hx => hslab ⟨hx.1, mem_univ _⟩
  have hz (y : ℝ × ℝ) (hy : y ∉ Icc (-R, -R) (R, R)) : W y = 0 :=
    hWout y (fun hy' => hy (reference_square_subset hRR hy'))
  have hb := gpe_moving_airfoil_impulse_balance mass gint hbar hW hψ hη hU hEq hT
    (a := (-R, -R)) (b := (R, R)) ⟨by linarith, by linarith⟩ hbox hz k
  change I - (gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₁ -
    gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₀) = _
  unfold I gpeMovingSquareFluxImpulse
  linarith only [hb]

/-- If opposite edges are both within `K` of the same uniform value,
their signed contribution is bounded by twice `K` times the edge length. -/
private theorem abs_opposite_edges_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {R K c : ℝ} (hR : 0 ≤ R)
    (hfb : ∀ x ∈ Icc (-R) R, |f x - c| ≤ K)
    (hgb : ∀ x ∈ Icc (-R) R, |g x - c| ≤ K) :
    |(∫ x in -R..R, f x) - (∫ x in -R..R, g x)| ≤ 4 * R * K := by
  have hle : -R ≤ R := by linarith
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    ← Real.norm_eq_abs]
  have hb (x : ℝ) (hx : x ∈ uIoc (-R) R) : ‖f x - g x‖ ≤ 2 * K := by
    have hx' : x ∈ Icc (-R) R := by
      rw [uIoc_of_le hle] at hx
      exact Ioc_subset_Icc_self hx
    rw [Real.norm_eq_abs, show f x - g x = (f x - c) - (g x - c) by ring]
    exact (abs_sub _ _).trans (by linarith [hfb x hx', hgb x hx'])
  calc
    _ ≤ (2 * K) * |R - (-R)| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = _ := by rw [abs_of_nonneg (by linarith : 0 ≤ R - (-R))]; ring

/-- A spatially uniform vector contributes no net outward square flux.
A deviation bounded by `K` on the four edges contributes at most
`8 * R * K`. The reference vector can be different for each fixed time. -/
theorem abs_rectangleForce_square_le (J : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (c : Fin 2 → ℝ) (hJ : ∀ j, Continuous fun x => J x j k)
    {R K : ℝ} (hR : 0 ≤ R)
    (hK : ∀ x ∈ Icc (-R, -R) (R, R), (|x.1| = R ∨ |x.2| = R) →
      ∀ j, |J x j k - c j| ≤ K) :
    |rectangleForce J k (-R, -R) (R, R)| ≤ 8 * R * K := by
  have hle : -R ≤ R := by linarith
  have hy := abs_opposite_edges_le
    ((hJ 1).comp (continuous_id.prodMk (continuous_const (y := R))))
    ((hJ 1).comp (continuous_id.prodMk (continuous_const (y := -R)))) (c := c 1) hR
    (fun x hx => hK (x, R) ⟨⟨hx.1, hle⟩, ⟨hx.2, le_rfl⟩⟩
      (Or.inr (abs_of_nonneg hR)) 1)
    (fun x hx => hK (x, -R) ⟨⟨hx.1, le_rfl⟩, ⟨hx.2, hle⟩⟩
      (Or.inr (by rw [abs_neg, abs_of_nonneg hR])) 1)
  have hx := abs_opposite_edges_le
    ((hJ 0).comp ((continuous_const (y := R)).prodMk continuous_id))
    ((hJ 0).comp ((continuous_const (y := -R)).prodMk continuous_id)) (c := c 0) hR
    (fun y hy' => hK (R, y) ⟨⟨hle, hy'.1⟩, ⟨le_rfl, hy'.2⟩⟩
      (Or.inl (abs_of_nonneg hR)) 0)
    (fun y hy' => hK (-R, y) ⟨⟨le_rfl, hy'.1⟩, ⟨hle, hy'.2⟩⟩
      (Or.inl (by rw [abs_neg, abs_of_nonneg hR])) 0)
  change |(((∫ x in -R..R, J (x, R) 1 k) - (∫ x in -R..R, J (x, -R) 1 k)) +
      (∫ y in -R..R, J (R, y) 0 k)) - (∫ y in -R..R, J (-R, y) 0 k)| ≤ _
  rw [add_sub_assoc]
  simp only [Function.comp_def, id_eq] at hy hx
  exact (abs_add_le _ _).trans ((add_le_add hy hx).trans_eq (by ring))

/-- Uniform spatial decay relative to a time-dependent constant stress
forces the total moving-square boundary impulse to tend to zero. -/
theorem tendsto_gpeMovingSquareFluxImpulse_zero (mass gint hbar : ℝ)
    {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) (k : Fin 2) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (far : Fin 2 → ℝ → ℝ) (err : ℝ → ℝ)
    (hsmall : Tendsto (fun R => R * err R) atTop (𝓝 0))
    (hfar : ∀ R, R₀ ≤ R → ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc (-R, -R) (R, R),
      (|x.1| = R ∨ |x.2| = R) → ∀ j,
      |gpeMovingMomentumFlux mass gint hbar ψ η j k (t, x + η t) - far j t| ≤ err R) :
    Tendsto (gpeMovingSquareFluxImpulse mass gint hbar ψ η k t₀ t₁) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hlim : Tendsto (fun R => (8 * |t₁ - t₀|) * (R * err R)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (8 * |t₁ - t₀|)
  apply squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop R₀] with R hRR
  have hp := hR₀.trans_le hRR
  have hpoint (t : ℝ) (ht : t ∈ uIoc t₀ t₁) :
      ‖gpeMovingRectangleFlux mass gint hbar ψ η k (-R, -R) (R, R) t‖ ≤ 8 * R * err R := by
    have ht' : t ∈ Icc t₀ t₁ := by
      rw [uIoc_of_le hT] at ht
      exact Ioc_subset_Icc_self ht
    let J (x : ℝ × ℝ) (j l : Fin 2) :=
      gpeMovingMomentumFlux mass gint hbar ψ η j l (t, x + η t)
    have hJ j : Continuous fun x => J x j k :=
      (contDiff_gpeMovingMomentumFlux mass gint hbar hψ hη j k).continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const))
    have hEq : rectangleForce J k (-R, -R) (R, R) =
        gpeMovingRectangleFlux mass gint hbar ψ η k (-R, -R) (R, R) t :=
      rectangleForce_translate (fun x j l => gpeMovingMomentumFlux mass gint hbar ψ η j l (t, x))
        k (-R, -R) (R, R) (η t)
    rw [Real.norm_eq_abs, ← hEq]
    exact abs_rectangleForce_square_le J k (fun j => far j t) hJ hp.le (hfar R hRR t ht')
  calc
    _ ≤ (8 * R * err R) * |t₁ - t₀| := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = _ := by ring

/-- If the relative far stress has uniform spatial decay, the whole
reaction impulse equals the negative whole-plane change of the fluid
momentum, without a residual far-boundary flux. -/
theorem gpe_moving_airfoil_impulse_of_far_decay (mass gint hbar : ℝ)
    {W : ℝ × ℝ → ℝ} {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hW : ContDiff ℝ 1 W) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar (gpeTranslatingPotential η W) ψ p)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) (hslab : Icc t₀ t₁ ×ˢ (univ : Set (ℝ × ℝ)) ⊆ U)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hWout : ∀ y ∉ Icc (-R₀, -R₀) (R₀, R₀), W y = 0)
    (k : Fin 2) (hE : Integrable (gpeMovingMomentumChange hbar ψ η k t₀ t₁))
    (far : Fin 2 → ℝ → ℝ) (err : ℝ → ℝ)
    (hsmall : Tendsto (fun R => R * err R) atTop (𝓝 0))
    (hfar : ∀ R, R₀ ≤ R → ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc (-R, -R) (R, R),
      (|x.1| = R ∨ |x.2| = R) → ∀ j,
      |gpeMovingMomentumFlux mass gint hbar ψ η j k (t, x + η t) - far j t| ≤ err R) :
    (∫ x, gpeMovingMomentumChange hbar ψ η k t₀ t₁ x) =
      -(∫ t in t₀..t₁, gpeAirfoilReactionForce ψ η W k t) := by
  have hf := tendsto_gpeMovingSquareFluxImpulse_zero mass gint hbar hψ hη hT k hR₀ far err hsmall hfar
  have hl := tendsto_gpeMovingSquareFluxImpulse_of_momentumChange mass gint hbar
    hW hψ hη hU hEq hT hslab hR₀ hWout k hE
  have he := tendsto_nhds_unique hl hf
  linarith only [he]

end Qatlib.Papers.SuperfoilLift19.LiftForce
