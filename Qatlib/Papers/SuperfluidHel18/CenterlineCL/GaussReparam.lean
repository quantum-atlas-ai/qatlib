/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussLinking

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Gauss integrals under orientation-preserving reparametrization

The exact two-dimensional Jacobian agrees with the two factors
in the reparametrized scalar triple product. The change of variables
applies also to the self-pair used for writhe.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open MeasureTheory Set
open scoped Real
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)

/-- A separate scalar factor on each tangent multiplies the cross
product by the product of the factors. -/
private theorem cross3_smul_both (a b : ℝ) (u v : Fin 3 → ℝ) :
    cross3 (a • u) (b • v) = (a * b) • cross3 u v := by
  funext i
  fin_cases i <;> simp [cross3] <;> ring

/-- The Gauss kernel is a two-parameter density under a differentiable
change of parameters, including at pairs where the chord vanishes. -/
theorem gaussKernel_comp (γ₁ γ₂ : ℝ → Fin 3 → ℝ) (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (h₁ : Differentiable ℝ γ₁) (h₂ : Differentiable ℝ γ₂) (s t : ℝ) :
    gaussKernel (γ₁ ∘ f) (γ₂ ∘ g) s t =
      (deriv f s * deriv g t) * gaussKernel γ₁ γ₂ (f s) (g t) := by
  have ha := ((h₁ (f s)).hasDerivAt.scomp s (hf s).hasDerivAt).deriv
  have hb := ((h₂ (g t)).hasDerivAt.scomp t (hg t).hasDerivAt).deriv
  simp only [gaussKernel, ha, hb, Function.comp_apply, cross3_smul_both, dot3_smul_left,
    mul_div_assoc]

/-- Increasing differentiable reparametrizations that fix both ends of
the parameter interval preserve the exact Gauss integral. -/
theorem gaussLinking_comp_eq (γ₁ γ₂ : ℝ → Fin 3 → ℝ) (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (h₁ : Differentiable ℝ γ₁) (h₂ : Differentiable ℝ γ₂)
    (hmf : StrictMono f) (hmg : StrictMono g)
    (hf0 : f 0 = 0) (hfP : f (2 * π) = 2 * π)
    (hg0 : g 0 = 0) (hgP : g (2 * π) = 2 * π) :
    gaussLinking (γ₁ ∘ f) (γ₂ ∘ g) = gaussLinking γ₁ γ₂ := by
  let A (x : ℝ) := (1 : ℝ →L[ℝ] ℝ).smulRight (deriv f x)
  let B (x : ℝ) := (1 : ℝ →L[ℝ] ℝ).smulRight (deriv g x)
  let D (p : ℝ × ℝ) := (A p.1).prodMap (B p.2)
  let F := Prod.map f g
  have hD (p : ℝ × ℝ) : HasFDerivAt F (D p) p :=
    HasFDerivAt.prodMap p (hf p.1).hasDerivAt.hasFDerivAt (hg p.2).hasDerivAt.hasFDerivAt
  have hdet (p : ℝ × ℝ) : (D p).det = deriv f p.1 * deriv g p.2 := by
    simp [D, A, B, ContinuousLinearMap.det, LinearMap.det_prodMap, LinearMap.det_ring]
  have hi : F '' gaussDomain = gaussDomain := by
    unfold F gaussDomain
    rw [Set.prodMap_image_prod,
      hf.continuous.continuousOn.image_Icc_of_monotoneOn Real.two_pi_pos.le (hmf.monotone.monotoneOn _),
      hg.continuous.continuousOn.image_Icc_of_monotoneOn Real.two_pi_pos.le (hmg.monotone.monotoneOn _),
      hf0, hfP, hg0, hgP]
  have hinj : Function.Injective F := hmf.injective.prodMap hmg.injective
  have hset : MeasurableSet gaussDomain := measurableSet_Icc.prod measurableSet_Icc
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    infer_instance
  have h := integral_image_eq_integral_abs_det_fderiv_smul (μ := (volume : Measure (ℝ × ℝ)))
    hset (fun p _ => (hD p).hasFDerivWithinAt) hinj.injOn
    (fun p => gaussKernel γ₁ γ₂ p.1 p.2)
  rw [hi] at h
  unfold gaussLinking gaussMeasure
  rw [Measure.prod_restrict]
  refine Eq.trans ?_ h.symm
  apply integral_congr_ae
  filter_upwards with p
  rw [gaussKernel_comp _ _ _ _ hf hg h₁ h₂, hdet,
    abs_of_nonneg (mul_nonneg (hmf.monotone.deriv_nonneg) (hmg.monotone.deriv_nonneg))]
  rfl

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
