/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.MovingContour

/-!
# Reaction force on a translating soft airfoil potential

[Musser2019Superfoil], equations (1) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
For a translated, spatially localized potential, the integral of the
laboratory force on the fluid is the negative of the reaction force
on the airfoil. Every co-moving rectangular contour enclosing the
potential support yields the same reaction impulse after accounting
for the fluid momentum change inside that contour.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Set Filter MeasureTheory
open scoped Topology

/-- The laboratory potential of a fixed airfoil profile translated
along a trajectory. -/
def gpeTranslatingPotential (η : ℝ → ℝ × ℝ) (W : ℝ × ℝ → ℝ)
    (p : GPESpacetime) : ℝ :=
  W (p.2 - η p.1)

/-- Translating a smooth potential along a smooth trajectory preserves
its joint spacetime regularity. -/
theorem contDiff_gpeTranslatingPotential {η : ℝ → ℝ × ℝ} {W : ℝ × ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hW : ContDiff ℝ 1 W) :
    ContDiff ℝ 1 (gpeTranslatingPotential η W) :=
  hW.comp (contDiff_snd.sub (hη.comp contDiff_fst))

/-- The spatial gradient of the laboratory potential is the gradient of
the fixed profile evaluated at the contour-relative position. -/
theorem gpePartial_translatingPotential_space {η : ℝ → ℝ × ℝ} {W : ℝ × ℝ → ℝ}
    (p : GPESpacetime) (k : Fin 2) (hη : DifferentiableAt ℝ η p.1)
    (hW : DifferentiableAt ℝ W (p.2 - η p.1)) :
    gpePartial (gpeSpaceDirection k) (gpeTranslatingPotential η W) p =
      fderiv ℝ W (p.2 - η p.1) (gpeSpaceDirection k).2 := by
  let I := gpeTranslate (-η)
  have he : gpeTranslatingPotential η W = (W ∘ Prod.snd) ∘ I := by
    funext q
    simp [gpeTranslatingPotential, I, gpeTranslate, sub_eq_add_neg]
  have hW' : DifferentiableAt ℝ W (I p).2 := by
    simpa [I, gpeTranslate, sub_eq_add_neg] using hW
  have hS := hasFDerivAt_snd (𝕜 := ℝ) (p := I p)
  rw [he]
  change gpePartial (gpeSpaceDirection k) ((W ∘ Prod.snd) ∘ gpeTranslate (-η)) p = _
  rw [gpePartial_translate_space hη.neg (hW'.comp (I p) hS.differentiableAt)]
  change fderiv ℝ (W ∘ Prod.snd) (I p) (gpeSpaceDirection k) = _
  rw [(hW'.hasFDerivAt.comp (I p) hS).fderiv]
  simp [I, gpeTranslate, sub_eq_add_neg]

/-- The reaction force density on the airfoil, written on the fixed
coordinate plane of the airfoil. It is opposite to the force density
that the external potential applies to the fluid. -/
def gpeAirfoilReactionDensity (ψ : GPESpacetime → ℂ) (η : ℝ → ℝ × ℝ)
    (W : ℝ × ℝ → ℝ) (k : Fin 2) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  gpeDensity ψ (t, x + η t) * fderiv ℝ W x (gpeSpaceDirection k).2

/-- The total reaction force on the translating airfoil in direction `k`. -/
def gpeAirfoilReactionForce (ψ : GPESpacetime → ℂ) (η : ℝ → ℝ × ℝ)
    (W : ℝ × ℝ → ℝ) (k : Fin 2) (t : ℝ) : ℝ :=
  ∫ x, gpeAirfoilReactionDensity ψ η W k t x

/-- A smooth potential that vanishes outside a closed rectangle has
zero gradient there. -/
private theorem fderiv_potential_eq_zero_outside {W : ℝ × ℝ → ℝ} {a b x : ℝ × ℝ}
    (hWout : ∀ y ∉ Icc a b, W y = 0) (hx : x ∉ Icc a b) : fderiv ℝ W x = 0 := by
  have hm : (Icc a b)ᶜ ∈ 𝓝 x := isClosed_Icc.isOpen_compl.mem_nhds hx
  have he : W =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hm] with y hy
    exact hWout y hy
  rw [he.fderiv_eq]
  simp

/-- The reaction force density is absolutely integrable if the potential
is smooth and vanishes outside a finite rectangle. -/
theorem integrable_gpeAirfoilReactionDensity {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ}
    {W : ℝ × ℝ → ℝ} {a b : ℝ × ℝ} (hψ : Continuous ψ) (hW : ContDiff ℝ 1 W)
    (hWout : ∀ y ∉ Icc a b, W y = 0) (k : Fin 2) (t : ℝ) :
    Integrable (gpeAirfoilReactionDensity ψ η W k t) := by
  have hmap : Continuous (fun x : ℝ × ℝ => (t, x + η t)) :=
    continuous_const.prodMk (continuous_id.add continuous_const)
  have hρ : Continuous (fun x : ℝ × ℝ => gpeDensity ψ (t, x + η t)) :=
    Complex.continuous_normSq.comp (hψ.comp hmap)
  have hgrad : Continuous (fun x => fderiv ℝ W x (gpeSpaceDirection k).2) :=
    (hW.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous.clm_apply
      continuous_const
  have hc : Continuous (gpeAirfoilReactionDensity ψ η W k t) := hρ.mul hgrad
  have hsupp : Function.support (gpeAirfoilReactionDensity ψ η W k t) ⊆ Icc a b := by
    intro x hx
    by_contra hout
    exact hx (by simp [gpeAirfoilReactionDensity, fderiv_potential_eq_zero_outside hWout hout])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (hc.continuousOn.integrableOn_compact isCompact_Icc)

/-- The potential term in a containing translating contour equals the
whole-plane reaction force on the airfoil at each time. -/
theorem gpeAirfoilReactionForce_eq_contour {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ}
    {W : ℝ × ℝ → ℝ} {a b : ℝ × ℝ} (hη : Differentiable ℝ η)
    (hW : Differentiable ℝ W) (hWout : ∀ y ∉ Icc a b, W y = 0) (k : Fin 2) (t : ℝ) :
    (∫ y in Icc (a + η t) (b + η t),
      gpeDensity ψ (t, y) * gpePartial (gpeSpaceDirection k) (gpeTranslatingPotential η W) (t, y)) =
        gpeAirfoilReactionForce ψ η W k t := by
  rw [← setIntegral_translate_rectangle _ a b (η t)]
  calc
    _ = ∫ x in Icc a b, gpeAirfoilReactionDensity ψ η W k t x := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      have hx : (x + η t) - η t = x := add_sub_cancel_right _ _
      have hgrad := gpePartial_translatingPotential_space (t, x + η t) k (hη t) (hW _)
      simp only [hx] at hgrad
      change gpeDensity ψ (t, x + η t) *
        gpePartial (gpeSpaceDirection k) (gpeTranslatingPotential η W) (t, x + η t) = _
      rw [hgrad]
      rfl
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [gpeAirfoilReactionDensity, fderiv_potential_eq_zero_outside hWout hx]

/-- For a moving soft airfoil, the actual GPE yields its reaction
impulse from the moving contour flux and endpoint fluid momenta. -/
theorem gpe_moving_airfoil_impulse_balance (mass gint hbar : ℝ)
    {W : ℝ × ℝ → ℝ} {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hW : ContDiff ℝ 1 W) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar (gpeTranslatingPotential η W) ψ p)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) {a b : ℝ × ℝ} (hab : a ≤ b)
    (hbox : MapsTo (gpeTranslate η) (Icc t₀ t₁ ×ˢ Icc a b) U)
    (hWout : ∀ y ∉ Icc a b, W y = 0) (k : Fin 2) :
    gpeMovingRectangleMomentum hbar ψ η k a b t₁ -
        gpeMovingRectangleMomentum hbar ψ η k a b t₀ +
        (∫ t in t₀..t₁, gpeMovingRectangleFlux mass gint hbar ψ η k a b t) =
      -(∫ t in t₀..t₁, gpeAirfoilReactionForce ψ η W k t) := by
  have hV := contDiff_gpeTranslatingPotential (hη.of_le (by norm_num)) hW
  have hb := gpe_moving_rectangle_impulse_balance mass gint hbar hV hψ hη hU hEq hT hab hbox k
  simp_rw [gpeAirfoilReactionForce_eq_contour (hη.differentiable (by norm_num))
    (hW.differentiable (by norm_num)) hWout k] at hb
  exact hb

/-- Laboratory momentum in the translating shell between the two nested
rectangles, with the enclosed inner rectangle removed. -/
def gpeMovingShellMomentum (hbar : ℝ) (ψ : GPESpacetime → ℂ) (η : ℝ → ℝ × ℝ)
    (k : Fin 2) (c d a b : ℝ × ℝ) (t : ℝ) : ℝ :=
  ∫ y in Icc (c + η t) (d + η t) \ Icc (a + η t) (b + η t), gpeMomentum hbar ψ k (t, y)

/-- The shell integral subtracts the momentum in the inner rectangle
from the momentum in the outer rectangle. -/
theorem gpeMovingShellMomentum_eq_sub (hbar : ℝ) {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 2 ψ) (η : ℝ → ℝ × ℝ) (k : Fin 2)
    {c d a b : ℝ × ℝ} (hca : c ≤ a) (hbd : b ≤ d) (t : ℝ) :
    gpeMovingShellMomentum hbar ψ η k c d a b t =
      gpeMovingRectangleMomentum hbar ψ η k c d t -
        gpeMovingRectangleMomentum hbar ψ η k a b t := by
  have hP : Continuous (fun y : ℝ × ℝ => gpeMomentum hbar ψ k (t, y)) :=
    (contDiff_gpeMomentum hbar k hψ).continuous.comp (continuous_const.prodMk continuous_id)
  have hca' : c + η t ≤ a + η t := by
    change c.1 + (η t).1 ≤ a.1 + (η t).1 ∧ c.2 + (η t).2 ≤ a.2 + (η t).2
    exact ⟨by linarith only [hca.1], by linarith only [hca.2]⟩
  have hbd' : b + η t ≤ d + η t := by
    change b.1 + (η t).1 ≤ d.1 + (η t).1 ∧ b.2 + (η t).2 ≤ d.2 + (η t).2
    exact ⟨by linarith only [hbd.1], by linarith only [hbd.2]⟩
  have hsub := Icc_subset_Icc hca' hbd'
  exact setIntegral_sdiff measurableSet_Icc
    (hP.continuousOn.integrableOn_compact isCompact_Icc) hsub

/-- Between nested moving contours enclosing the soft potential, the
outer impulse minus the inner impulse is the negative change in the
momentum of the fluid in the intervening shell. -/
theorem gpe_moving_airfoil_shell_impulse_balance (mass gint hbar : ℝ)
    {W : ℝ × ℝ → ℝ} {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hW : ContDiff ℝ 1 W) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar (gpeTranslatingPotential η W) ψ p)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) {c d a b : ℝ × ℝ}
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hbox : MapsTo (gpeTranslate η) (Icc t₀ t₁ ×ˢ Icc c d) U)
    (hWout : ∀ y ∉ Icc a b, W y = 0) (k : Fin 2) :
    gpeMovingShellMomentum hbar ψ η k c d a b t₁ -
        gpeMovingShellMomentum hbar ψ η k c d a b t₀ +
      ((∫ t in t₀..t₁, gpeMovingRectangleFlux mass gint hbar ψ η k c d t) -
        (∫ t in t₀..t₁, gpeMovingRectangleFlux mass gint hbar ψ η k a b t)) = 0 := by
  have hsub := Icc_subset_Icc hca hbd
  have hInner : MapsTo (gpeTranslate η) (Icc t₀ t₁ ×ˢ Icc a b) U :=
    hbox.mono (Set.prod_mono subset_rfl hsub) subset_rfl
  have hz (y : ℝ × ℝ) (hy : y ∉ Icc c d) : W y = 0 :=
    hWout y (fun ha => hy (hsub ha))
  have ho := gpe_moving_airfoil_impulse_balance mass gint hbar hW hψ hη hU hEq hT
    (hca.trans (hab.trans hbd)) hbox hz k
  have hi := gpe_moving_airfoil_impulse_balance mass gint hbar hW hψ hη hU hEq hT hab hInner hWout k
  rw [gpeMovingShellMomentum_eq_sub hbar (hψ.of_le (by norm_num)) η k hca hbd,
    gpeMovingShellMomentum_eq_sub hbar (hψ.of_le (by norm_num)) η k hca hbd]
  linarith only [ho, hi]

end Qatlib.Papers.SuperfoilLift19.LiftForce
