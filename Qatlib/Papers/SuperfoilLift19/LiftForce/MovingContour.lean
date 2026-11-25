/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.DynamicContour

import Mathlib.MeasureTheory.Group.Integral

/-!
# Momentum balance on a translating airfoil contour

[Musser2019Superfoil], equations (1), (2), and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
A translating control rectangle carries laboratory momentum through its
boundary as it moves. Its outward momentum flux is the wave stress
minus the boundary velocity times the momentum density. The force
density is still given by the laboratory potential gradient.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Set MeasureTheory

/-- The change from coordinates attached to the translating contour
to laboratory spacetime coordinates. -/
def gpeTranslate (η : ℝ → ℝ × ℝ) (p : GPESpacetime) : GPESpacetime :=
  (p.1, p.2 + η p.1)

/-- The Cartesian component of the contour's laboratory velocity. -/
def gpeContourVelocity (η : ℝ → ℝ × ℝ) (j : Fin 2) (t : ℝ) : ℝ :=
  if j = 0 then (deriv η t).1 else (deriv η t).2

/-- Flux of laboratory momentum relative to the moving boundary. -/
def gpeMovingMomentumFlux (mass gint hbar : ℝ) (ψ : GPESpacetime → ℂ)
    (η : ℝ → ℝ × ℝ) (j k : Fin 2) (p : GPESpacetime) : ℝ :=
  gpeWaveStress mass gint hbar ψ j k p - gpeContourVelocity η j p.1 * gpeMomentum hbar ψ k p

/-- The total laboratory momentum of the wave inside the current
position of the contour. -/
def gpeMovingRectangleMomentum (hbar : ℝ) (ψ : GPESpacetime → ℂ) (η : ℝ → ℝ × ℝ)
    (k : Fin 2) (a b : ℝ × ℝ) (t : ℝ) : ℝ :=
  gpeRectangleMomentum hbar ψ k (a + η t) (b + η t) t

/-- The boundary integral at the current laboratory position of the
contour, with flux measured relative to its translational velocity. -/
def gpeMovingRectangleFlux (mass gint hbar : ℝ) (ψ : GPESpacetime → ℂ) (η : ℝ → ℝ × ℝ)
    (k : Fin 2) (a b : ℝ × ℝ) (t : ℝ) : ℝ :=
  rectangleForce (fun y j l => gpeMovingMomentumFlux mass gint hbar ψ η j l (t, y)) k
    (a + η t) (b + η t)

/-- A smooth translation gives a smooth map of spacetime. -/
theorem contDiff_gpeTranslate {η : ℝ → ℝ × ℝ} {n : WithTop ℕ∞}
    (hη : ContDiff ℝ n η) : ContDiff ℝ n (gpeTranslate η) :=
  contDiff_fst.prodMk (contDiff_snd.add (hη.comp contDiff_fst))

/-- The derivative's spatial part adds the displacement derivative
times the time component of the input direction. -/
private def translateFDeriv (η : ℝ → ℝ × ℝ) (t : ℝ) : GPESpacetime →L[ℝ] GPESpacetime :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) +
      (fderiv ℝ η t).comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))

/-- The joint Fréchet chain rule for the time-dependent translation. -/
private theorem hasFDerivAt_gpeTranslate {η : ℝ → ℝ × ℝ} {p : GPESpacetime}
    (hη : DifferentiableAt ℝ η p.1) :
    HasFDerivAt (gpeTranslate η) (translateFDeriv η p.1) p := by
  have h := hη.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).add h)

/-- A spatial directional derivative commutes with the pullback by the translation. -/
theorem gpePartial_translate_space {η : ℝ → ℝ × ℝ} {f : GPESpacetime → ℝ} {p : GPESpacetime}
    (hη : DifferentiableAt ℝ η p.1) (hf : DifferentiableAt ℝ f (gpeTranslate η p)) (j : Fin 2) :
    gpePartial (gpeSpaceDirection j) (f ∘ gpeTranslate η) p =
      gpePartial (gpeSpaceDirection j) f (gpeTranslate η p) := by
  unfold gpePartial
  rw [(hf.hasFDerivAt.comp p (hasFDerivAt_gpeTranslate hη)).fderiv]
  change (fderiv ℝ f (gpeTranslate η p)) (translateFDeriv η p.1 (gpeSpaceDirection j)) = _
  have heq : translateFDeriv η p.1 (gpeSpaceDirection j) = gpeSpaceDirection j := by
    fin_cases j <;> simp [translateFDeriv, gpeSpaceDirection]
  rw [heq]

/-- The reference time derivative includes the laboratory time
derivative and advection by the contour velocity. -/
theorem gpePartial_translate_time {η : ℝ → ℝ × ℝ} {f : GPESpacetime → ℝ} {p : GPESpacetime}
    (hη : DifferentiableAt ℝ η p.1) (hf : DifferentiableAt ℝ f (gpeTranslate η p)) :
    gpePartial gpeTimeDirection (f ∘ gpeTranslate η) p =
      gpePartial gpeTimeDirection f (gpeTranslate η p) +
        ∑ j : Fin 2, gpeContourVelocity η j p.1 *
          gpePartial (gpeSpaceDirection j) f (gpeTranslate η p) := by
  have hdir : translateFDeriv η p.1 gpeTimeDirection =
      gpeTimeDirection + gpeContourVelocity η 0 p.1 • gpeSpaceDirection 0 +
        gpeContourVelocity η 1 p.1 • gpeSpaceDirection 1 := by
    have he : translateFDeriv η p.1 gpeTimeDirection = (1, deriv η p.1) := by
      change (1, (0 : ℝ × ℝ) + fderiv ℝ η p.1 1) = _
      rw [zero_add]
      rfl
    rw [he]
    rcases hw : deriv η p.1 with ⟨u, v⟩
    simp [gpeTimeDirection, gpeContourVelocity, gpeSpaceDirection, hw]
  simp only [gpePartial, (hf.hasFDerivAt.comp p (hasFDerivAt_gpeTranslate hη)).fderiv,
    ContinuousLinearMap.comp_apply, hdir, Fin.sum_univ_two, map_add, map_smul, smul_eq_mul,
    add_assoc]

/-- A continuously differentiable velocity component is constant on
each spatial slice of spacetime. -/
private theorem contDiff_contourVelocity {η : ℝ → ℝ × ℝ} (hη : ContDiff ℝ 2 η)
    (j : Fin 2) : ContDiff ℝ 1 (fun q : GPESpacetime => gpeContourVelocity η j q.1) := by
  have hv : ContDiff ℝ 1 (deriv η) := ContDiff.deriv' hη
  fin_cases j
  · exact hv.fst.comp contDiff_fst
  · exact hv.snd.comp contDiff_fst

/-- The velocity has zero spatial derivative even while the contour accelerates. -/
private theorem gpePartial_contourVelocity_space {η : ℝ → ℝ × ℝ} (hη : ContDiff ℝ 2 η)
    (p : GPESpacetime) (j : Fin 2) :
    gpePartial (gpeSpaceDirection j) (fun q => gpeContourVelocity η j q.1) p = 0 := by
  have hV := (contDiff_contourVelocity hη j).differentiable (by norm_num)
  rw [gpePartial_space_eq_axisLine p j (hV p)]
  change deriv (fun _ : ℝ => gpeContourVelocity η j p.1) 0 = 0
  exact deriv_const _ _

/-- The relative normal flux is continuously differentiable for a
smooth wave and a twice differentiable contour trajectory. -/
theorem contDiff_gpeMovingMomentumFlux (mass gint hbar : ℝ) {ψ : GPESpacetime → ℂ}
    {η : ℝ → ℝ × ℝ} (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (j k : Fin 2) :
    ContDiff ℝ 1 (gpeMovingMomentumFlux mass gint hbar ψ η j k) := by
  exact (contDiff_gpeWaveStress mass gint hbar j k hψ).sub
    ((contDiff_contourVelocity hη j).mul (contDiff_gpeMomentum hbar k (hψ.of_le (by norm_num))))

/-- An integral over a reference rectangle equals the laboratory
integral over its translate, since translation preserves area. -/
theorem setIntegral_translate_rectangle (f : ℝ × ℝ → ℝ) (a b z : ℝ × ℝ) :
    (∫ x in Icc a b, f (x + z)) = ∫ y in Icc (a + z) (b + z), f y := by
  let τ := Homeomorph.addRight z
  have hτ : MeasurableEmbedding τ := τ.isClosedEmbedding.measurableEmbedding
  have hmap : Measure.map τ volume = volume := by
    change Measure.map (Prod.map (fun x : ℝ => x + z.1) (fun y : ℝ => y + z.2))
      (volume.prod volume) = volume.prod volume
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      map_add_right_eq_self volume z.1, map_add_right_eq_self volume z.2]
  have hpre : τ ⁻¹' Icc (a + z) (b + z) = Icc a b := by
    ext x
    change ((a.1 + z.1 ≤ x.1 + z.1 ∧ a.2 + z.2 ≤ x.2 + z.2) ∧
      (x.1 + z.1 ≤ b.1 + z.1 ∧ x.2 + z.2 ≤ b.2 + z.2)) ↔
      ((a.1 ≤ x.1 ∧ a.2 ≤ x.2) ∧ (x.1 ≤ b.1 ∧ x.2 ≤ b.2))
    simp only [add_le_add_iff_right]
  change (∫ x in Icc a b, f (τ x)) = _
  rw [← hpre, ← hτ.setIntegral_map, hmap]

/-- Translating the four rectangle edges leaves their signed flux
integrals equal to the pullback integrals on the reference edges. -/
theorem rectangleForce_translate (J : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (a b z : ℝ × ℝ) :
    rectangleForce (fun x j l => J (x + z) j l) k a b =
      rectangleForce J k (a + z) (b + z) := by
  rcases z with ⟨u, v⟩
  unfold rectangleForce
  simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  rw [intervalIntegral.integral_comp_add_right (fun x => J (x, b.2 + v) 1 k) u,
    intervalIntegral.integral_comp_add_right (fun x => J (x, a.2 + v) 1 k) u,
    intervalIntegral.integral_comp_add_right (fun y => J (b.1 + u, y) 0 k) v,
    intervalIntegral.integral_comp_add_right (fun y => J (a.1 + u, y) 0 k) v]

set_option maxHeartbeats 400000 in
/-- The translated spacetime law balances the derivative of laboratory
momentum in reference coordinates with the divergence of relative flux. -/
theorem gpe_translated_local_momentum_balance (mass gint hbar : ℝ)
    {ψ : GPESpacetime → ℂ} {V : GPESpacetime → ℝ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar V ψ p)
    (q : GPESpacetime) (hq : gpeTranslate η q ∈ U) (k : Fin 2) :
    gpePartial gpeTimeDirection (gpeMomentum hbar ψ k ∘ gpeTranslate η) q +
      (∑ j : Fin 2, gpePartial (gpeSpaceDirection j)
        (gpeMovingMomentumFlux mass gint hbar ψ η j k ∘ gpeTranslate η) q) =
      -(gpeDensity ψ (gpeTranslate η q) * gpePartial (gpeSpaceDirection k) V (gpeTranslate η q)) := by
  let p := gpeTranslate η q
  let P := gpeMomentum hbar ψ k
  let T (j : Fin 2) := gpeWaveStress mass gint hbar ψ j k
  let W (j : Fin 2) (x : GPESpacetime) := gpeContourVelocity η j x.1
  have hηd := hη.differentiable (by norm_num) q.1
  have hPd : DifferentiableAt ℝ P p :=
    (contDiff_gpeMomentum hbar k (hψ.of_le (by norm_num))).differentiable (by norm_num) p
  have hTd (j : Fin 2) : DifferentiableAt ℝ (T j) p :=
    (contDiff_gpeWaveStress mass gint hbar j k hψ).differentiable (by norm_num) p
  have hWd (j : Fin 2) : DifferentiableAt ℝ (W j) p :=
    (contDiff_contourVelocity hη j).differentiable (by norm_num) p
  have hflux (j : Fin 2) :
      gpePartial (gpeSpaceDirection j)
        (gpeMovingMomentumFlux mass gint hbar ψ η j k ∘ gpeTranslate η) q =
      gpePartial (gpeSpaceDirection j) (T j) p -
        gpeContourVelocity η j q.1 * gpePartial (gpeSpaceDirection j) P p := by
    change gpePartial (gpeSpaceDirection j) ((T j - W j * P) ∘ gpeTranslate η) q = _
    rw [gpePartial_translate_space hηd ((hTd j).sub ((hWd j).mul hPd))]
    have hz : fderiv ℝ (W j) p (gpeSpaceDirection j) = 0 :=
      gpePartial_contourVelocity_space hη p j
    change fderiv ℝ (T j - W j * P) p (gpeSpaceDirection j) =
      fderiv ℝ (T j) p (gpeSpaceDirection j) - W j p * fderiv ℝ P p (gpeSpaceDirection j)
    rw [fderiv_sub (hTd j) ((hWd j).mul hPd), fderiv_mul (hWd j) hPd]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
  change gpePartial gpeTimeDirection (P ∘ gpeTranslate η) q + _ = _
  rw [gpePartial_translate_time hηd hPd]
  simp only [hflux, Finset.sum_sub_distrib]
  have hlocal := gpe_local_momentum_balance mass gint hbar hV hψ hU hEq p hq k
  rw [neg_mul] at hlocal
  change gpePartial gpeTimeDirection P p +
    (∑ j : Fin 2, gpeContourVelocity η j q.1 * gpePartial (gpeSpaceDirection j) P p) +
    ((∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (T j) p) -
      ∑ j : Fin 2, gpeContourVelocity η j q.1 * gpePartial (gpeSpaceDirection j) P p) = _
  linarith only [hlocal]

set_option maxHeartbeats 400000 in
/-- Exact impulse balance on a finite translating rectangular contour
for the actual time-dependent Gross–Pitaevskii equation. The wave
momentum and potential force are integrated in laboratory coordinates
at each position of the contour. -/
theorem gpe_moving_rectangle_impulse_balance (mass gint hbar : ℝ)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ} {η : ℝ → ℝ × ℝ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hη : ContDiff ℝ 2 η) (hU : IsOpen U)
    (hEq : ∀ p ∈ U, GrossPitaevskiiAt mass gint hbar V ψ p)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) {a b : ℝ × ℝ} (hab : a ≤ b)
    (hbox : MapsTo (gpeTranslate η) (Icc t₀ t₁ ×ˢ Icc a b) U) (k : Fin 2) :
    gpeMovingRectangleMomentum hbar ψ η k a b t₁ -
        gpeMovingRectangleMomentum hbar ψ η k a b t₀ +
        (∫ t in t₀..t₁, gpeMovingRectangleFlux mass gint hbar ψ η k a b t) =
      -(∫ t in t₀..t₁, ∫ y in Icc (a + η t) (b + η t),
        gpeDensity ψ (t, y) * gpePartial (gpeSpaceDirection k) V (t, y)) := by
  let F (p : GPESpacetime) := gpeDensity ψ p * gpePartial (gpeSpaceDirection k) V p
  let P := gpeMomentum hbar ψ k ∘ gpeTranslate η
  let J (j : Fin 2) := gpeMovingMomentumFlux mass gint hbar ψ η j k ∘ gpeTranslate η
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hFc : Continuous F :=
    (Complex.continuous_normSq.comp hψ.continuous).mul
      (contDiff_gpePartial hV (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1) _).continuous
  have hP : ContDiff ℝ 1 P :=
    (contDiff_gpeMomentum hbar k (hψ.of_le (by norm_num))).comp (contDiff_gpeTranslate hη1)
  have hJ (j : Fin 2) : ContDiff ℝ 1 (J j) :=
    (contDiff_gpeMovingMomentumFlux mass gint hbar hψ hη j k).comp (contDiff_gpeTranslate hη1)
  have hloc (t : ℝ) (x : ℝ × ℝ) (ht : t ∈ Icc t₀ t₁) (hx : x ∈ Icc a b) :
      gpePartial gpeTimeDirection P (t, x) +
        (∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (J j) (t, x)) =
        -(F ∘ gpeTranslate η) (t, x) :=
    gpe_translated_local_momentum_balance mass gint hbar hV hψ hη hU hEq
      (t, x) (hbox ⟨ht, hx⟩) k
  have hv := rectangle_impulse_balance_of_local hP
    (hFc.comp (contDiff_gpeTranslate hη1).continuous) hJ hT hab hloc
  have hP' (t : ℝ) : (∫ x in Icc a b, P (t, x)) =
      gpeMovingRectangleMomentum hbar ψ η k a b t :=
    setIntegral_translate_rectangle (fun y => gpeMomentum hbar ψ k (t, y)) a b (η t)
  have hJ' (t : ℝ) : rectangleForce (fun x j (_ : Fin 2) => J j (t, x)) 0 a b =
      gpeMovingRectangleFlux mass gint hbar ψ η k a b t :=
    rectangleForce_translate (fun y j l => gpeMovingMomentumFlux mass gint hbar ψ η j l (t, y))
      k a b (η t)
  have hF' (t : ℝ) : (∫ x in Icc a b, (F ∘ gpeTranslate η) (t, x)) =
      ∫ y in Icc (a + η t) (b + η t), F (t, y) :=
    setIntegral_translate_rectangle (fun y => F (t, y)) a b (η t)
  simpa only [hP', hJ', hF', F] using hv

end Qatlib.Papers.SuperfoilLift19.LiftForce
