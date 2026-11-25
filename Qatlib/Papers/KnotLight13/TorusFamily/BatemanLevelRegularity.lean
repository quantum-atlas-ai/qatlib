/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalTori

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Differential regularity of Bateman field-line labels

[Kedia2013TyingKnots], p. 150404-3,
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
Axial rotation and variation of the two sphere radii give concrete
transverse derivatives of the powered Bateman label.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

local notation "Space" => ℝ × ℝ × ℝ
open Qatlib.Papers.KnotLight13.TorusFamily (complex_rational_pair_unit)
open Filter Set
open scoped Real Topology

/-- The positive axial rotation has the usual infinitesimal generator
in the two horizontal coordinates. -/
theorem hasDerivAt_batemanAxialRotation_zero (s : Space) :
    HasDerivAt (fun θ => batemanAxialRotation θ s) (-s.2.1, s.1, 0) 0 := by
  have hc := Real.hasDerivAt_cos 0
  have hs := Real.hasDerivAt_sin 0
  have hx := (hc.mul_const s.1).fun_sub (hs.mul_const s.2.1)
  have hy := (hs.mul_const s.1).fun_add (hc.mul_const s.2.1)
  have hz : HasDerivAt (fun _ : ℝ => s.2.2) 0 0 := hasDerivAt_const 0 _
  simpa [batemanAxialRotation] using hx.prodMk (hy.prodMk hz)

/-- Along the axial rotation, the complex product label has derivative
`−iq` times its value at the original point. -/
theorem hasDerivAt_batemanPoweredLabel_axial (p q : ℕ) (t : ℝ) (s : Space) :
    HasDerivAt (fun θ => batemanPoweredLabel p q t (batemanAxialRotation θ s))
      (-(q : ℂ) * Complex.I * batemanPoweredLabel p q t s) 0 := by
  let a := batemanPoweredLabel p q t s
  have h₁ : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 0 := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h₂ : HasDerivAt batemanAxialPhase (-Complex.I) 0 := by
    change HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * Complex.I)) (-Complex.I) 0
    simpa using (h₁.neg.mul_const Complex.I).cexp
  have h₃ := (h₂.pow q).mul_const a
  have hphase : (fun θ => batemanPoweredLabel p q t (batemanAxialRotation θ s)) =
      fun θ => batemanAxialPhase θ ^ q * a := by
    rcases s with ⟨x, y, z⟩
    funext θ
    exact poweredProductLabel_axialRotation p q θ x y z t
  rw [hphase]
  exact h₃.congr_deriv (by simp [batemanAxialPhase, a, mul_neg, neg_mul])

/-- The real projection differentiates to `q` times the imaginary label
in the infinitesimal axial direction. -/
theorem fderiv_batemanRealLabel_axial (p q : ℕ) (t : ℝ) (s : Space) :
    fderiv ℝ (fun x => (batemanPoweredLabel p q t x).re) s (-s.2.1, s.1, 0) =
      (q : ℝ) * (batemanPoweredLabel p q t s).im := by
  have hR := hasDerivAt_batemanAxialRotation_zero s
  have hzero : batemanAxialRotation 0 s = s := by
    rcases s with ⟨x, y, z⟩
    simp [batemanAxialRotation]
  have h := ((contDiff_batemanPoweredLabel p q t).differentiable (by simp) s).hasFDerivAt
  have ha := h.comp_hasDerivAt_of_eq 0 hR hzero.symm
  have ha' := (hasDerivAt_batemanPoweredLabel_axial p q t s).unique ha
  have hr := Complex.reCLM.hasFDerivAt.comp s h
  calc
    _ = (fderiv ℝ (batemanPoweredLabel p q t) s (-s.2.1, s.1, 0)).re :=
      congrArg (fun D : Space →L[ℝ] ℝ => D (-s.2.1, s.1, 0)) hr.fderiv
    _ = _ := by simpa [Complex.mul_re, Complex.mul_im] using (congrArg Complex.re ha').symm

/-- Whenever the imaginary label is nonzero, the real level covector
is nonzero because of its value in the axial direction. -/
theorem fderiv_batemanRealLabel_ne_zero_of_im {q : ℕ} (hq : 0 < q) (p : ℕ) (t : ℝ) (s : Space)
    (hs : (batemanPoweredLabel p q t s).im ≠ 0) :
    fderiv ℝ (fun x => (batemanPoweredLabel p q t x).re) s ≠ 0 := by
  intro h
  have hq₀ : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hval := fderiv_batemanRealLabel_axial p q t s
  rw [h, zero_apply] at hval
  exact mul_ne_zero hq₀ hs hval.symm

/-- Rotating the two positive sphere radii gives a differentiable
physical curve with a prescribed derivative of the real label. -/
theorem exists_batemanRealLabel_radial (p q : ℕ) (t : ℝ) (s : Space)
    (hα : (batemanPairAt t s).1 ≠ 0) (hβ : (batemanPairAt t s).2 ≠ 0) :
    let A := ‖(batemanPairAt t s).1‖
    let B := ‖(batemanPairAt t s).2‖
    ∃ γ : ℝ → Space, γ 0 = s ∧ DifferentiableAt ℝ γ 0 ∧
      HasDerivAt (fun u => (batemanPoweredLabel p q t (γ u)).re)
        (((p : ℝ) * (B / A) - (q : ℝ) * (A / B)) * (batemanPoweredLabel p q t s).re) 0 := by
  let w := batemanPairAt t s
  let A := ‖w.1‖
  let B := ‖w.2‖
  have hA : 0 < A := norm_pos_iff.mpr hα
  have hB : 0 < B := norm_pos_iff.mpr hβ
  have hw : A ^ 2 + B ^ 2 = 1 := by
    simpa only [w, A, B, batemanPairAt, Complex.normSq_eq_norm_sq] using
      complex_rational_pair_unit s.1 s.2.1 s.2.2 t
  let f (u : ℝ) := Real.cos u + B / A * Real.sin u
  let g (u : ℝ) := Real.cos u - A / B * Real.sin u
  have hf : HasDerivAt f (B / A) 0 := by
    simpa [f] using (Real.hasDerivAt_cos 0).fun_add ((Real.hasDerivAt_sin 0).const_mul (B / A))
  have hg : HasDerivAt g (-(A / B)) 0 := by
    simpa [g] using (Real.hasDerivAt_cos 0).fun_sub ((Real.hasDerivAt_sin 0).const_mul (A / B))
  have hf₀ : f 0 = 1 := by simp [f]
  have hg₀ : g 0 = 1 := by simp [g]
  let z (u : ℝ) : ℂ × ℂ := ((f u : ℂ) * w.1, (g u : ℂ) * w.2)
  have hz₀ : z 0 = w := by simp [z, hf₀, hg₀]
  have hunit (u : ℝ) : ‖(z u).1‖ ^ 2 + ‖(z u).2‖ ^ 2 = 1 := by
    have hfa : f u * A = A * Real.cos u + B * Real.sin u := by
      unfold f
      field_simp [hA.ne']
    have hgb : g u * B = B * Real.cos u - A * Real.sin u := by
      unfold g
      field_simp [hB.ne']
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    change Complex.normSq ((f u : ℂ) * w.1) + Complex.normSq ((g u : ℂ) * w.2) = 1
    rw [map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    change f u * f u * A ^ 2 + g u * g u * B ^ 2 = 1
    calc
      _ = (f u * A) ^ 2 + (g u * B) ^ 2 := by ring
      _ = (A ^ 2 + B ^ 2) * (Real.cos u ^ 2 + Real.sin u ^ 2) := by rw [hfa, hgb]; ring
      _ = 1 := by rw [hw, Real.cos_sq_add_sin_sq, mul_one]
  have ha : DifferentiableAt ℝ (fun u => (z u).1) 0 := (hf.ofReal_comp.mul_const w.1).differentiableAt
  have hb : DifferentiableAt ℝ (fun u => (z u).2) 0 := (hg.ofReal_comp.mul_const w.2).differentiableAt
  have haRe : DifferentiableAt ℝ (fun u => (z u).1.re) 0 := Complex.reCLM.differentiableAt.comp 0 ha
  have hilt : (z 0).1.re < 1 := by
    rw [hz₀]
    exact rationalAlpha_re_lt_one _ _ _ _
  have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), (z u).1.re < 1 :=
    haRe.continuousAt (Iio_mem_nhds hilt)
  let γ (u : ℝ) := batemanRay t (initialCartesianPoint (z u))
  have hγ₀ : γ 0 = s := by
    simpa only [γ, hz₀, w] using batemanRay_initialCartesianPoint_batemanPairAt t s
  have hD : DifferentiableAt ℝ (fun u => 1 - (z u).1.re) 0 :=
    (differentiableAt_const (c := (1 : ℝ))).sub haRe
  have hD₀ : 1 - (z 0).1.re ≠ 0 := (sub_pos.mpr hilt).ne'
  have hx : DifferentiableAt ℝ (fun u => (z u).2.re / (1 - (z u).1.re)) 0 :=
    (Complex.reCLM.differentiableAt.comp 0 hb).div hD hD₀
  have hy : DifferentiableAt ℝ (fun u => -(z u).2.im / (1 - (z u).1.re)) 0 :=
    (Complex.imCLM.differentiableAt.comp 0 hb).neg.div hD hD₀
  have hz : DifferentiableAt ℝ (fun u => (z u).1.im / (1 - (z u).1.re)) 0 :=
    (Complex.imCLM.differentiableAt.comp 0 ha).div hD hD₀
  have hchart : DifferentiableAt ℝ (fun u => initialCartesianPoint (z u)) 0 :=
    hx.prodMk (hy.prodMk hz)
  have hγ : DifferentiableAt ℝ γ 0 :=
    ((contDiff_bateman_ray t).differentiable (by simp) _).comp 0 hchart
  have hlabels : (fun u => (batemanPoweredLabel p q t (γ u)).re) =ᶠ[𝓝 (0 : ℝ)]
      fun u => (f u ^ p * g u ^ q) * (batemanPoweredLabel p q t s).re := by
    filter_upwards [hnear] with u hu
    have he : batemanPairAt t (γ u) = z u := by
      change batemanPairAt t (batemanRay t (initialCartesianPoint (z u))) = z u
      rw [batemanPairAt_batemanRay]
      exact initialBatemanPair_initialCartesianPoint _ (hunit u) hu
    change ((batemanPairAt t (γ u)).1 ^ p * (batemanPairAt t (γ u)).2 ^ q).re =
      (f u ^ p * g u ^ q) * (w.1 ^ p * w.2 ^ q).re
    rw [he]
    change (((f u : ℂ) * w.1) ^ p * ((g u : ℂ) * w.2) ^ q).re = _
    have he' : (f u : ℂ) ^ p * (g u : ℂ) ^ q = ((f u ^ p * g u ^ q : ℝ) : ℂ) := by push_cast; rfl
    rw [mul_pow, mul_pow, mul_mul_mul_comm, he']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine ⟨γ, hγ₀, hγ, ?_⟩
  apply HasDerivAt.congr_of_eventuallyEq ?_ hlabels
  have h := ((hf.pow p).mul (hg.pow q)).mul_const (batemanPoweredLabel p q t s).re
  exact h.congr_deriv (by simp [hf₀, hg₀, sub_eq_add_neg, A, B, w])

/-- A nonzero magnetic label strictly inside its extremal values is a
regular level at every point of the physical slice. -/
theorem fderiv_batemanRealLabel_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) (s : Space)
    (hn : (batemanPoweredLabel p q t s).re ≠ 0)
    (hc : |(batemanPoweredLabel p q t s).re| < poweredPeakAmplitude p q) :
    fderiv ℝ (fun x => (batemanPoweredLabel p q t x).re) s ≠ 0 := by
  by_cases hi : (batemanPoweredLabel p q t s).im = 0
  · let w := batemanPairAt t s
    let A := ‖w.1‖
    let B := ‖w.2‖
    have hlabel : batemanPoweredLabel p q t s = w.1 ^ p * w.2 ^ q := rfl
    have hl : batemanPoweredLabel p q t s ≠ 0 := fun h => hn (by simp [h])
    have ha : w.1 ≠ 0 := by
      intro h
      apply hl
      rw [hlabel, h, zero_pow hp.ne', zero_mul]
    have hb : w.2 ≠ 0 := by
      intro h
      apply hl
      rw [hlabel, h, zero_pow hq.ne', mul_zero]
    have hA : 0 < A := norm_pos_iff.mpr ha
    have hB : 0 < B := norm_pos_iff.mpr hb
    have hu : Complex.normSq w.1 + Complex.normSq w.2 = 1 :=
      complex_rational_pair_unit s.1 s.2.1 s.2.2 t
    have hu' : A ^ 2 + B ^ 2 = 1 := by
      simpa only [Complex.normSq_eq_norm_sq, A, B] using hu
    have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    have hcoef : (p : ℝ) * (B / A) - (q : ℝ) * (A / B) ≠ 0 := by
      intro he
      have he' : (p : ℝ) * B ^ 2 - (q : ℝ) * A ^ 2 = 0 := by
        field_simp [hA.ne', hB.ne'] at he
        nlinarith
      have hpeak : Complex.normSq w.1 = poweredPeakRadius p q := by
        rw [Complex.normSq_eq_norm_sq, poweredPeakRadius]
        change A ^ 2 = (p : ℝ) / ((p : ℝ) + (q : ℝ))
        apply (eq_div_iff (by positivity)).mpr
        nlinarith [congrArg (fun y : ℝ => (p : ℝ) * y) hu']
      have hsq := (normSq_poweredProduct_eq_peak_iff hp hq hu).2 hpeak
      rw [← hlabel, Complex.normSq_apply, hi] at hsq
      have hm : |(batemanPoweredLabel p q t s).re| ^ 2 = poweredPeakAmplitude p q ^ 2 := by
        simpa [sq_abs, pow_two] using hsq
      exact (ne_of_lt hc) ((pow_left_inj₀ (abs_nonneg _) (poweredPeakAmplitude_pos hp hq).le
        (by decide : (2 : ℕ) ≠ 0)).mp hm)
    obtain ⟨γ, hγ₀, hγ, hd⟩ := exists_batemanRealLabel_radial p q t s ha hb
    intro hzero
    have hF : DifferentiableAt ℝ (fun x => (batemanPoweredLabel p q t x).re) s :=
      Complex.reCLM.differentiableAt.comp s ((contDiff_batemanPoweredLabel p q t).differentiable (by simp) s)
    have hD := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ.hasDerivAt hγ₀.symm
    rw [hzero, zero_apply] at hD
    exact mul_ne_zero hcoef hn (hd.unique hD)
  · exact fderiv_batemanRealLabel_ne_zero_of_im hq p t s hi

/-- A nonzero electric label strictly inside its extremal values also
has nonzero differential at every point of the physical slice. -/
theorem fderiv_batemanImagLabel_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) (s : Space)
    (hn : (batemanPoweredLabel p q t s).im ≠ 0)
    (hc : |(batemanPoweredLabel p q t s).im| < poweredPeakAmplitude p q) :
    fderiv ℝ (fun x => (batemanPoweredLabel p q t x).im) s ≠ 0 := by
  let θ := π / (2 * (q : ℝ))
  let e := batemanAxialHomeomorph θ
  let x := e.symm s
  have hx : batemanAxialRotation θ x = s := e.apply_symm_apply s
  have hLabel (y : Space) :
      (batemanPoweredLabel p q t (batemanAxialRotation θ y)).im =
        -(batemanPoweredLabel p q t y).re := by
    rcases y with ⟨a, b, c⟩
    have h := poweredProductLabel_axialRotation p q θ a b c t
    change batemanPoweredLabel p q t (batemanAxialRotation θ (a, b, c)) =
      batemanAxialPhase θ ^ q * batemanPoweredLabel p q t (a, b, c) at h
    rw [h, batemanAxialPhase_special hq]
    simp [Complex.mul_im]
  have hRe : (batemanPoweredLabel p q t x).re ≠ 0 := by
    intro h
    exact hn (by simpa only [hx, h, neg_zero] using hLabel x)
  have hI : |(batemanPoweredLabel p q t x).re| < poweredPeakAmplitude p q := by
    rwa [← abs_neg (batemanPoweredLabel p q t x).re, ← hLabel x, hx]
  intro hzero
  have hR : DifferentiableAt ℝ (batemanAxialRotation θ) x := by
    unfold batemanAxialRotation
    fun_prop
  have hF : DifferentiableAt ℝ (fun y => (batemanPoweredLabel p q t y).im) s :=
    Complex.imCLM.differentiableAt.comp s ((contDiff_batemanPoweredLabel p q t).differentiable (by simp) s)
  have hF' : HasFDerivAt (fun y => (batemanPoweredLabel p q t y).im)
      (0 : Space →L[ℝ] ℝ) (batemanAxialRotation θ x) := by
    rw [hx, ← hzero]
    exact hF.hasFDerivAt
  have hd := (hF'.comp x hR.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (batemanPoweredLabel p q t (batemanAxialRotation θ y)).im) x =
    (0 : Space →L[ℝ] ℝ).comp (fderiv ℝ (batemanAxialRotation θ) x) at hd
  rw [funext hLabel, fderiv_fun_neg, ContinuousLinearMap.zero_comp] at hd
  exact fderiv_batemanRealLabel_ne_zero hp hq t x hRe hI (neg_eq_zero.mp hd)

/-- A smooth real label with nonzero differential admits smooth local
coordinates whose first component is the original label. The second
component takes values in the kernel of the differential at the point. -/
theorem realLabel_localCoordinates {f : Space → ℝ} {x : Space}
    (hf : ContDiffAt ℝ ⊤ f x) (hL : fderiv ℝ f x ≠ 0) :
    let K := (fderiv ℝ f x).ker
    ∃ e : OpenPartialHomeomorph Space (ℝ × K), x ∈ e.source ∧
      (∀ y, (e y).1 = f y) ∧ ContDiffAt ℝ ⊤ e x ∧ ContDiffAt ℝ ⊤ e.symm (e x) := by
  let L := fderiv ℝ f x
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext (fun y => h y))
  let J := (ContinuousLinearMap.id ℝ ℝ).smulRight ((L v)⁻¹ • v)
  have hJ : Function.RightInverse J L := by
    intro r
    change L (r • ((L v)⁻¹ • v)) = r
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hv, mul_one]
  let P := L.projKerOfRightInverse J hJ
  let E := ContinuousLinearEquiv.equivOfRightInverse L J hJ
  let F (y : Space) : ℝ × L.ker := (f y, P y)
  have hF : ContDiffAt ℝ ⊤ F x := hf.prodMk P.contDiff.contDiffAt
  have hF' : HasFDerivAt F (E : Space →L[ℝ] ℝ × L.ker) x :=
    (hf.differentiableAt (by simp)).hasFDerivAt.prodMk P.hasFDerivAt
  let e := hF.toOpenPartialHomeomorph F hF' (by simp)
  exact ⟨e, hF.mem_toOpenPartialHomeomorph_source hF' (by simp), fun _ => rfl,
    hF, hF.to_localInverse hF' (by simp)⟩

/-- Every strictly intermediate nonzero magnetic level has smooth local
coordinates in which the magnetic label is the first coordinate. -/
theorem batemanRealLabel_localCoordinates {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) (s : Space)
    (hn : (batemanPoweredLabel p q t s).re ≠ 0)
    (hc : |(batemanPoweredLabel p q t s).re| < poweredPeakAmplitude p q) :
    let f := fun x => (batemanPoweredLabel p q t x).re
    let K := (fderiv ℝ f s).ker
    ∃ e : OpenPartialHomeomorph Space (ℝ × K), s ∈ e.source ∧
      (∀ y, (e y).1 = f y) ∧ ContDiffAt ℝ ⊤ e s ∧ ContDiffAt ℝ ⊤ e.symm (e s) :=
  realLabel_localCoordinates
    (Complex.reCLM.contDiff.comp (contDiff_batemanPoweredLabel p q t)).contDiffAt
    (fderiv_batemanRealLabel_ne_zero hp hq t s hn hc)

/-- Every strictly intermediate nonzero electric level has smooth local
coordinates in which the electric label is the first coordinate. -/
theorem batemanImagLabel_localCoordinates {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) (s : Space)
    (hn : (batemanPoweredLabel p q t s).im ≠ 0)
    (hc : |(batemanPoweredLabel p q t s).im| < poweredPeakAmplitude p q) :
    let f := fun x => (batemanPoweredLabel p q t x).im
    let K := (fderiv ℝ f s).ker
    ∃ e : OpenPartialHomeomorph Space (ℝ × K), s ∈ e.source ∧
      (∀ y, (e y).1 = f y) ∧ ContDiffAt ℝ ⊤ e s ∧ ContDiffAt ℝ ⊤ e.symm (e s) :=
  realLabel_localCoordinates
    (Complex.imCLM.contDiff.comp (contDiff_batemanPoweredLabel p q t)).contDiffAt
    (fderiv_batemanImagLabel_ne_zero hp hq t s hn hc)

end Qatlib.Papers.KnotLight13.TorusFamily
