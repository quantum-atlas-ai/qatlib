/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.DynamicMomentum

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

/-!
# Finite control-volume impulse of a Gross–Pitaevskii wave

[Musser2019Superfoil], equations (1), (2), and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
On a rectangle the stress flux, body force from the real potential,
and momentum accumulation are related by the actual wave equation.
Time integration gives a balance of endpoint momenta and integrated
fluxes, with no stationarity assumption.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Set MeasureTheory

/-- The fixed-time spatial Fréchet derivative evaluated in a
coordinate direction is the corresponding spacetime partial. -/
private theorem spatial_fderiv_eq_gpePartial {f : GPESpacetime → ℝ}
    (t : ℝ) (x : ℝ × ℝ) (j : Fin 2) (hf : DifferentiableAt ℝ f (t, x)) :
    fderiv ℝ (fun y => f (t, y)) x (if j = 0 then (1, 0) else (0, 1)) =
      gpePartial (gpeSpaceDirection j) f (t, x) := by
  have h := hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  change (fderiv ℝ (f ∘ Prod.mk t) x) (if j = 0 then (1, 0) else (0, 1)) = _
  rw [h.fderiv]
  fin_cases j <;> simp [gpePartial, gpeSpaceDirection]

/-- The oriented flux of a smooth Cartesian field out of a rectangle is
the integral of its spatial divergence at the fixed time. -/
private theorem rectangle_flux_eq_integral_divergence {J : Fin 2 → GPESpacetime → ℝ}
    (hJ : ∀ j, ContDiff ℝ 1 (J j)) (t : ℝ) {a b : ℝ × ℝ} (hab : a ≤ b) :
    rectangleForce (fun x j (_ : Fin 2) => J j (t, x)) 0 a b =
      ∫ x in Icc a b, ∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (J j) (t, x) := by
  let T (j : Fin 2) (x : ℝ × ℝ) := J j (t, x)
  have hT (j : Fin 2) : ContDiff ℝ 1 (T j) :=
    (hJ j).comp (contDiff_const.prodMk contDiff_id)
  have hT' (j : Fin 2) : Differentiable ℝ (T j) := (hT j).differentiable (by norm_num)
  let D (x : ℝ × ℝ) := fderiv ℝ (T 0) x (1, 0) + fderiv ℝ (T 1) x (0, 1)
  have hC (j : Fin 2) (e : ℝ × ℝ) : Continuous (fun x => fderiv ℝ (T j) x e) :=
    ((hT j).fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous.clm_apply
      continuous_const
  have hD : Continuous D := (hC 0 (1, 0)).add (hC 1 (0, 1))
  have hIntegral := integral_divergence_prod_Icc_of_hasFDerivAt_of_le (T 0) (T 1)
    (fderiv ℝ (T 0)) (fderiv ℝ (T 1)) a b hab
    (hT 0).continuous.continuousOn (hT 1).continuous.continuousOn
    (fun x _ => (hT' 0 x).hasFDerivAt) (fun x _ => (hT' 1 x).hasFDerivAt)
    (hD.continuousOn.integrableOn_compact isCompact_Icc)
  calc
    _ = ∫ x in Icc a b, D x := hIntegral.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      have hd (j : Fin 2) := spatial_fderiv_eq_gpePartial t x j
        ((hJ j).differentiable (by norm_num) (t, x))
      have h0 : fderiv ℝ (T 0) x (1, 0) =
          gpePartial (gpeSpaceDirection 0) (J 0) (t, x) := by
        simpa only [T, ite_true] using hd 0
      have h1 : fderiv ℝ (T 1) x (0, 1) =
          gpePartial (gpeSpaceDirection 1) (J 1) (t, x) := by
        simpa [T] using hd 1
      simp only [D, Fin.sum_univ_two, h0, h1]

/-- The stress flux out of a finite rectangle is the negative of the
integrated momentum accumulation and potential force term. -/
theorem gpe_rectangle_stress_balance (mass gint hbar : ℝ)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hU : IsOpen U)
    (hEq : ∀ x ∈ U, GrossPitaevskiiAt mass gint hbar V ψ x)
    (t : ℝ) {a b : ℝ × ℝ} (hab : a ≤ b) (ht : ∀ x ∈ Icc a b, (t, x) ∈ U)
    (k : Fin 2) :
    rectangleForce (fun x j l => gpeWaveStress mass gint hbar ψ j l (t, x)) k a b =
      -(∫ x in Icc a b,
        (gpePartial gpeTimeDirection (gpeMomentum hbar ψ k) (t, x) +
          gpeDensity ψ (t, x) * gpePartial (gpeSpaceDirection k) V (t, x))) := by
  calc
    _ = ∫ x in Icc a b, ∑ j : Fin 2,
          gpePartial (gpeSpaceDirection j) (gpeWaveStress mass gint hbar ψ j k) (t, x) :=
      rectangle_flux_eq_integral_divergence
        (fun j => contDiff_gpeWaveStress mass gint hbar j k hψ) t hab
    _ = _ := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hbal := gpe_local_momentum_balance mass gint hbar hV hψ hU hEq (t, x) (ht x hx) k
      linarith only [hbal]

/-- The physical wave momentum contained in the control rectangle. -/
def gpeRectangleMomentum (hbar : ℝ) (ψ : GPESpacetime → ℂ) (k : Fin 2)
    (a b : ℝ × ℝ) (t : ℝ) : ℝ :=
  ∫ x in Icc a b, gpeMomentum hbar ψ k (t, x)

/-- Continuity on a compact spacetime box makes the iterated integral
over the fixed spatial rectangle interval-integrable in time. -/
private theorem integral_box_integrable {f : GPESpacetime → ℝ} (hf : Continuous f)
    (t₀ t₁ : ℝ) (a b : ℝ × ℝ) :
    Integrable f ((volume.restrict (uIoc t₀ t₁)).prod (volume.restrict (Icc a b))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  apply IntegrableOn.mono_set
    (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_Icc))
  exact Set.prod_mono Set.uIoc_subset_uIcc subset_rfl

/-- On a fixed reference rectangle, a local balance law gives the
exact endpoint momentum, boundary flux and body impulse relation. -/
theorem rectangle_impulse_balance_of_local {P F : GPESpacetime → ℝ}
    {J : Fin 2 → GPESpacetime → ℝ} (hP : ContDiff ℝ 1 P) (hF : Continuous F)
    (hJ : ∀ j, ContDiff ℝ 1 (J j)) {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁)
    {a b : ℝ × ℝ} (hab : a ≤ b)
    (hEq : ∀ t x, t ∈ Icc t₀ t₁ → x ∈ Icc a b →
      gpePartial gpeTimeDirection P (t, x) +
        (∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (J j) (t, x)) = -F (t, x)) :
    (∫ x in Icc a b, P (t₁, x)) - (∫ x in Icc a b, P (t₀, x)) +
        (∫ t in t₀..t₁, rectangleForce (fun x j (_ : Fin 2) => J j (t, x)) 0 a b) =
      -(∫ t in t₀..t₁, ∫ x in Icc a b, F (t, x)) := by
  let D := gpePartial gpeTimeDirection P
  have hD : Continuous D :=
    (contDiff_gpePartial hP (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1) _).continuous
  have hswap (x : ℝ × ℝ) :
      (∫ t in t₀..t₁, D (t, x)) = P (t₁, x) - P (t₀, x) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      have hline : HasDerivAt (fun s : ℝ => (s, x)) gpeTimeDirection t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
      exact (hP.differentiable (by norm_num) (t, x)).hasFDerivAt.comp_hasDerivAt t hline
    · exact (hD.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hDInt := integral_box_integrable hD t₀ t₁ a b
  have hFInt := integral_box_integrable hF t₀ t₁ a b
  have hTimeD : IntervalIntegrable (fun t => ∫ x in Icc a b, D (t, x)) volume t₀ t₁ :=
    intervalIntegrable_iff.mpr hDInt.integral_prod_left
  have hTimeF : IntervalIntegrable (fun t => ∫ x in Icc a b, F (t, x)) volume t₀ t₁ :=
    intervalIntegrable_iff.mpr hFInt.integral_prod_left
  have hEndpoint :
      (∫ t in t₀..t₁, ∫ x in Icc a b, D (t, x)) =
        (∫ x in Icc a b, P (t₁, x)) - ∫ x in Icc a b, P (t₀, x) := by
    rw [intervalIntegral_integral_swap (f := fun t x => D (t, x)) hDInt]
    simp_rw [hswap]
    exact integral_sub
      ((hP.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
      ((hP.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
  have hRect :
      (∫ t in t₀..t₁,
        rectangleForce (fun x j (_ : Fin 2) => J j (t, x)) 0 a b) =
      -(∫ t in t₀..t₁,
        (∫ x in Icc a b, D (t, x)) + ∫ x in Icc a b, F (t, x)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc t₀ t₁ := by simpa only [uIcc_of_le hT] using ht
    change rectangleForce (fun x j (_ : Fin 2) => J j (t, x)) 0 a b =
      -((∫ x in Icc a b, D (t, x)) + ∫ x in Icc a b, F (t, x))
    rw [rectangle_flux_eq_integral_divergence hJ t hab]
    have hEqIntegral :
        (∫ x in Icc a b, ∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (J j) (t, x)) =
          -(∫ x in Icc a b, D (t, x) + F (t, x)) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hlocal := hEq t x ht' hx
      change D (t, x) + (∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (J j) (t, x)) =
        -F (t, x) at hlocal
      linarith only [hlocal]
    rw [hEqIntegral]
    congr 1
    exact integral_add
      ((hD.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
      ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
  rw [hRect, intervalIntegral.integral_add hTimeD hTimeF, hEndpoint]
  change _ = -(∫ t in t₀..t₁, ∫ x in Icc a b, F (t, x))
  ring

/-- The exact dynamic impulse law on a finite spacetime box. The
change in fluid momentum plus outward stress flux equals the body
impulse from the actual potential in the wave equation. -/
theorem gpe_rectangle_impulse_balance (mass gint hbar : ℝ)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hU : IsOpen U)
    (hEq : ∀ x ∈ U, GrossPitaevskiiAt mass gint hbar V ψ x)
    {t₀ t₁ : ℝ} (hT : t₀ ≤ t₁) {a b : ℝ × ℝ} (hab : a ≤ b)
    (hbox : Icc t₀ t₁ ×ˢ Icc a b ⊆ U) (k : Fin 2) :
    gpeRectangleMomentum hbar ψ k a b t₁ - gpeRectangleMomentum hbar ψ k a b t₀ +
        (∫ t in t₀..t₁,
          rectangleForce (fun x j l => gpeWaveStress mass gint hbar ψ j l (t, x)) k a b) =
      -(∫ t in t₀..t₁, ∫ x in Icc a b,
        gpeDensity ψ (t, x) * gpePartial (gpeSpaceDirection k) V (t, x)) := by
  let F (p : GPESpacetime) := gpeDensity ψ p * gpePartial (gpeSpaceDirection k) V p
  have hF : Continuous F :=
    (Complex.continuous_normSq.comp hψ.continuous).mul
      (contDiff_gpePartial hV (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1) _).continuous
  refine rectangle_impulse_balance_of_local
    (contDiff_gpeMomentum hbar k (hψ.of_le (by norm_num))) hF
    (fun j => contDiff_gpeWaveStress mass gint hbar j k hψ) hT hab ?_
  intro t x ht hx
  simpa only [F, neg_mul] using
    gpe_local_momentum_balance mass gint hbar hV hψ hU hEq (t, x) (hbox ⟨ht, hx⟩) k

end Qatlib.Papers.SuperfoilLift19.LiftForce
