/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.FarFieldImpulse

/-!
# Finite-contour error in the moving-airfoil impulse law

[Musser2019Superfoil], equations (1) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
The far-boundary estimate is quantitative before taking a limit. A uniform
relative-flux error `err` on a square of radius `R` costs at most
`8 |t₁-t₀| R err`. Together with an explicit endpoint-momentum tail bound,
this controls the difference between the actual airfoil reaction impulse and
the whole-plane fluid momentum change.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Filter Set MeasureTheory
open scoped Topology

/-- On one fixed moving square, a relative-flux error bounded by `err`
gives an impulse error at most `8 |t₁-t₀| R err`. -/
theorem abs_gpeMovingSquareFluxImpulse_le (mass gint hbar : ℝ)
    {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η)
    {t₀ t₁ R : ℝ} (hT : t₀ ≤ t₁) (k : Fin 2) {R₀ : ℝ} (hR₀ : 0 < R₀) (hR : R₀ ≤ R)
    (far : Fin 2 → ℝ → ℝ) (err : ℝ)
    (hfar : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc (-R, -R) (R, R),
      (|x.1| = R ∨ |x.2| = R) → ∀ j,
      |gpeMovingMomentumFlux mass gint hbar ψ η j k (t, x + η t) - far j t| ≤ err) :
    |gpeMovingSquareFluxImpulse mass gint hbar ψ η k t₀ t₁ R| ≤
      (8 * |t₁ - t₀|) * (R * err) := by
  have hp := hR₀.trans_le hR
  have hpoint (t : ℝ) (ht : t ∈ uIoc t₀ t₁) :
      ‖gpeMovingRectangleFlux mass gint hbar ψ η k (-R, -R) (R, R) t‖ ≤ 8 * R * err := by
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
    exact abs_rectangleForce_square_le J k (fun j => far j t) hJ hp.le (hfar t ht')
  unfold gpeMovingSquareFluxImpulse
  calc
    _ ≤ (8 * R * err) * |t₁ - t₀| := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = _ := by ring

/-- The actual reaction impulse differs from the negative whole-plane
momentum change by at most the supplied endpoint tail plus the finite
square-flux error. No far-field limit or zero-error assumption is made. -/
theorem abs_gpeAirfoilImpulse_add_momentumChange_le (mass gint hbar : ℝ)
    {W : ℝ × ℝ → ℝ} {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hW : ContDiff ℝ 1 W) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar (gpeTranslatingPotential η W) ψ p)
    {t₀ t₁ R : ℝ} (hT : t₀ ≤ t₁) (hslab : Icc t₀ t₁ ×ˢ (univ : Set (ℝ × ℝ)) ⊆ U)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hR : R₀ ≤ R)
    (hWout : ∀ y ∉ Icc (-R₀, -R₀) (R₀, R₀), W y = 0) (k : Fin 2)
    (far : Fin 2 → ℝ → ℝ) (tail err : ℝ)
    (htail : |(∫ x, gpeMovingMomentumChange hbar ψ η k t₀ t₁ x) -
      (gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₁ -
        gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₀)| ≤ tail)
    (hfar : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc (-R, -R) (R, R),
      (|x.1| = R ∨ |x.2| = R) → ∀ j,
      |gpeMovingMomentumFlux mass gint hbar ψ η j k (t, x + η t) - far j t| ≤ err) :
    |(∫ t in t₀..t₁, gpeAirfoilReactionForce ψ η W k t) +
      (∫ x, gpeMovingMomentumChange hbar ψ η k t₀ t₁ x)| ≤
        tail + (8 * |t₁ - t₀|) * (R * err) := by
  let M := gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₁ -
    gpeMovingRectangleMomentum hbar ψ η k (-R, -R) (R, R) t₀
  let F := gpeMovingSquareFluxImpulse mass gint hbar ψ η k t₀ t₁ R
  let I := ∫ t in t₀..t₁, gpeAirfoilReactionForce ψ η W k t
  let Δ := ∫ x, gpeMovingMomentumChange hbar ψ η k t₀ t₁ x
  have hbox : MapsTo (gpeTranslate η) (Icc t₀ t₁ ×ˢ Icc (-R, -R) (R, R)) U :=
    fun x hx => hslab ⟨hx.1, mem_univ _⟩
  have hsub : Icc (-R₀, -R₀) (R₀, R₀) ⊆ Icc (-R, -R) (R, R) :=
    Icc_subset_Icc (show (-R, -R) ≤ (-R₀, -R₀) from ⟨neg_le_neg hR, neg_le_neg hR⟩)
      (show (R₀, R₀) ≤ (R, R) from ⟨hR, hR⟩)
  have hz (y : ℝ × ℝ) (hy : y ∉ Icc (-R, -R) (R, R)) : W y = 0 :=
    hWout y (fun hy' => hy (hsub hy'))
  have hb : M + F = -I := by
    exact gpe_moving_airfoil_impulse_balance mass gint hbar hW hψ hη hU hEq hT
      (a := (-R, -R)) (b := (R, R)) ⟨by linarith [hR₀.trans_le hR], by linarith [hR₀.trans_le hR]⟩
      hbox hz k
  have hF : |F| ≤ (8 * |t₁ - t₀|) * (R * err) :=
    abs_gpeMovingSquareFluxImpulse_le mass gint hbar hψ hη hT k hR₀ hR far err hfar
  have hid : I + Δ = (Δ - M) - F := by
    dsimp only [I, Δ, M, F] at hb ⊢
    linarith
  change |I + Δ| ≤ tail + (8 * |t₁ - t₀|) * (R * err)
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add htail hF)

end Qatlib.Papers.SuperfoilLift19.LiftForce
