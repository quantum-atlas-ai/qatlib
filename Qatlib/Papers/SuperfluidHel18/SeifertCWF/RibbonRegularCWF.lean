/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonArcLength
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussReparam

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Călugăreanu–White–Fuller for regular closed ribbons

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5).
A regular centerline can be parametrized at unit speed after a common
positive scaling of space. The Gauss integrals and the twist integral
transfer to the original parameter.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open MeasureTheory Set
open scoped Real ContDiff
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL

/-- The unit tangent in the original parameter of a regular curve. -/
def ribbonUnitTangent (γ : ℝ → Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  (1 / ribbonSpeed γ s) • deriv γ s

/-- Total twist computed using the unit tangent in an arbitrary
regular parameter on the fixed interval. -/
def regularRibbonTwist (γ N : ℝ → Fin 3 → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ s in 0..(2 * π), dot3 (cross3 (ribbonUnitTangent γ s) (N s)) (deriv N s)

/-- The twist integral pulls back under an increasing arc-length
parameter change when its new tangent is the old unit tangent. -/
private theorem ribbonTwist_eq_of_normalized {γ N Γ : ℝ → Fin 3 → ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hm : Monotone f) (hf0 : f 0 = 0) (hfP : f (2 * π) = 2 * π)
    (hN : Differentiable ℝ N) (hΓ : ∀ s, deriv Γ s = ribbonUnitTangent γ (f s)) :
    ribbonTwist Γ (N ∘ f) = regularRibbonTwist γ N := by
  let w (s : ℝ) := dot3 (cross3 (ribbonUnitTangent γ s) (N s)) (deriv N s)
  have hw (s : ℝ) :
      dot3 (cross3 (deriv Γ s) ((N ∘ f) s)) (deriv (N ∘ f) s) = (w ∘ f) s * deriv f s := by
    have hd := ((hN (f s)).hasDerivAt.scomp s (hf s).hasDerivAt).deriv
    rw [hΓ, hd, dot3_smul_right]
    simp only [w, Function.comp_apply, mul_comm]
  unfold ribbonTwist regularRibbonTwist
  simp_rw [hw]
  rw [intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := f) (f' := deriv f) (g := w) hf.continuous.continuousOn
    (fun x _ => (hf x).hasDerivAt) (fun _ _ => hm.deriv_nonneg), hf0, hfP]

set_option maxHeartbeats 500000 in
/-- The Călugăreanu–White–Fuller identity for any simple regular closed
C³ centerline with a periodic C² unit normal. Narrow positive offsets
are disjoint from the core and their Gauss linking is writhe plus twist. -/
theorem exists_regularRibbon_gaussLinking_eq_writhe_add_twist {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 3 γ) (hN : ContDiff ℝ 2 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hreg : ∀ s, deriv γ s ≠ 0)
    (hunit : ∀ s, dot3 (N s) (N s) = 1)
    (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ ε > 0, ∀ a : ℝ, 0 < a → a < ε →
      (∀ s t, γ s ≠ normalRibbonPoint γ N a t) ∧
      gaussLinking γ (normalRibbonPoint γ N a) = gaussLinking γ γ + regularRibbonTwist γ N := by
  have hγd := hγ.differentiable (by norm_num : (3 : ℕ∞ω) ≠ 0)
  have hNd := hN.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)
  obtain ⟨c, hc, f, _, hm, _, hfc, _, hf0, _, hfshift, _, hfd⟩ :=
    exists_normalized_arcLength (contDiff_ribbonSpeed hγ hreg)
      (fun s => ribbonSpeed_pos (hreg s)) Real.two_pi_pos (periodic_ribbonSpeed hγd hpγ)
  let θ := f.symm
  let Γ (s : ℝ) := c • γ (θ s)
  let M := N ∘ θ
  have hθc : ContDiff ℝ 3 θ := hfc
  have hθd := hθc.differentiable (by norm_num : (3 : ℕ∞ω) ≠ 0)
  have hθ0 : θ 0 = 0 := hf0
  have hθP : θ (2 * π) = 2 * π := by simpa only [zero_add, hf0] using hfshift 0
  have hΓc : ContDiff ℝ 3 Γ := (hγ.comp hθc).const_smul c
  have hθ2 : ContDiff ℝ 2 θ := hθc.of_le (by norm_num)
  have hMc : ContDiff ℝ 2 M := hN.comp hθ2
  have hΓper : Function.Periodic Γ (2 * π) := fun s => by
    change c • γ (θ (s + 2 * π)) = _
    rw [show θ (s + 2 * π) = θ s + 2 * π from hfshift s, hpγ]
  have hMper : Function.Periodic M (2 * π) := fun s => by
    change N (θ (s + 2 * π)) = _
    rw [show θ (s + 2 * π) = θ s + 2 * π from hfshift s, hpN]
    rfl
  have hscale_inj : Function.Injective (fun v : Fin 3 → ℝ => c • v) :=
    smul_right_injective (Fin 3 → ℝ) hc.ne'
  have hθI : MapsTo θ (Ico 0 (2 * π)) (Ico 0 (2 * π)) := by
    intro x hx
    exact ⟨hθ0 ▸ hm.monotone hx.1, hθP ▸ hm hx.2⟩
  have hΓinj : InjOn Γ (Ico 0 (2 * π)) := fun _ hx _ hy heq =>
    θ.injective (hinj (hθI hx) (hθI hy) (hscale_inj heq))
  have hΓ' (s : ℝ) : deriv Γ s = ribbonUnitTangent γ (θ s) := by
    have hd := (((hγd (θ s)).hasDerivAt.scomp s (hfd s)).const_smul c).deriv
    change deriv Γ s = c • ((1 / (c * ribbonSpeed γ (θ s))) • deriv γ (θ s)) at hd
    rw [hd]
    unfold ribbonUnitTangent
    rw [smul_smul]
    congr 1
    field_simp [hc.ne', (ribbonSpeed_pos (hreg (θ s))).ne']
  have hΓspeed (s : ℝ) : dot3 (deriv Γ s) (deriv Γ s) = 1 := by
    rw [hΓ', ribbonUnitTangent, dot3_smul_left, dot3_smul_right, ← ribbonSpeed_sq]
    field_simp [(ribbonSpeed_pos (hreg (θ s))).ne']
  have hΓorth (s : ℝ) : dot3 (deriv Γ s) (M s) = 0 := by
    rw [hΓ', ribbonUnitTangent, dot3_smul_left]
    simp only [M, Function.comp_apply, horth, mul_zero]
  obtain ⟨ε, hε, hCWF⟩ := exists_normalRibbon_gaussLinking_eq_writhe_add_twist
    hΓc hMc hΓper hMper hΓinj hΓspeed (fun s => hunit (θ s)) hΓorth
  have hθ1 : ContDiff ℝ 1 θ := hθc.of_le (by norm_num)
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hN1 : ContDiff ℝ 1 N := hN.of_le (by norm_num)
  have hlink (η : ℝ → Fin 3 → ℝ) (hη : ContDiff ℝ 1 η) :
      gaussLinking Γ (fun s => c • η (θ s)) = gaussLinking γ η := by
    calc
      _ = gaussLinking (γ ∘ θ) (η ∘ θ) :=
        gaussLinking_const_smul_eq _ _ hc (hγ1.comp hθ1) (hη.comp hθ1)
      _ = _ := gaussLinking_comp_eq γ η θ θ hθd hθd hγd
        (hη.differentiable (by norm_num)) hm hm hθ0 hθP hθ0 hθP
  have htwist := ribbonTwist_eq_of_normalized hθd hm.monotone hθ0 hθP hNd hΓ'
  refine ⟨ε / c, div_pos hε hc, fun a ha haε => ?_⟩
  have ha' : c * a < ε := by simpa only [mul_comm] using (lt_div_iff₀ hc).1 haε
  obtain ⟨hdisj, heq⟩ := hCWF (c * a) (mul_pos hc ha) ha'
  have hoff (s : ℝ) : normalRibbonPoint Γ M (c * a) s =
      c • normalRibbonPoint γ N a (θ s) := by
    simp only [normalRibbonPoint, Γ, M, Function.comp_apply, smul_add, smul_smul]
  constructor
  · intro s t h
    apply hdisj (f s) (f t)
    rw [hoff]
    change c • γ (f.symm (f s)) = c • normalRibbonPoint γ N a (f.symm (f t))
    rw [f.symm_apply_apply, f.symm_apply_apply, h]
  · have hη : ContDiff ℝ 1 (normalRibbonPoint γ N a) := hγ1.add (hN1.const_smul a)
    calc
      _ = gaussLinking Γ (fun s => c • normalRibbonPoint γ N a (θ s)) := (hlink _ hη).symm
      _ = gaussLinking Γ Γ + ribbonTwist Γ M := (congrArg (gaussLinking Γ) (funext hoff)).symm.trans heq
      _ = _ := congrArg₂ (· + ·) (hlink γ hγ1) htwist

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
