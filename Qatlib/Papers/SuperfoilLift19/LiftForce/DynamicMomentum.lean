/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.StationaryMadelung

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Local momentum balance of the time-dependent Gross–Pitaevskii wave

[Musser2019Superfoil], equations (1) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
The wave and its actual Cartesian derivatives give the momentum density
and a polynomial form of the stress. The balance retains the time
derivative and the force density of the real potential. The polynomial
form is regular even at zeros of the wave.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Filter Set
open scoped ComplexConjugate Topology

/-- Physical time and the two Cartesian spatial coordinates. -/
abbrev GPESpacetime := ℝ × (ℝ × ℝ)

/-- The unit direction of physical time. -/
def gpeTimeDirection : GPESpacetime := (1, 0, 0)

/-- The spatial coordinate direction, with time held fixed. -/
def gpeSpaceDirection (j : Fin 2) : GPESpacetime :=
  if j = 0 then (0, 1, 0) else (0, 0, 1)

/-- A Cartesian derivative obtained by evaluating the real Fréchet
derivative in a fixed spacetime direction. -/
def gpePartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : GPESpacetime) (f : GPESpacetime → F) (p : GPESpacetime) : F :=
  fderiv ℝ f p d

/-- The spatial Laplacian of a time-dependent wave at fixed time. -/
def gpeLaplacian (ψ : GPESpacetime → ℂ) (p : GPESpacetime) : ℂ :=
  ∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ) p

/-- The particle density, including at zeros of the wave. -/
def gpeDensity (ψ : GPESpacetime → ℂ) (p : GPESpacetime) : ℝ := Complex.normSq (ψ p)

/-- The time-dependent two-dimensional Gross–Pitaevskii equation at
a spacetime point, with a real, potentially time-dependent potential. -/
def GrossPitaevskiiAt (mass gint hbar : ℝ) (V : GPESpacetime → ℝ)
    (ψ : GPESpacetime → ℂ) (p : GPESpacetime) : Prop :=
  (hbar : ℂ) * Complex.I * gpePartial gpeTimeDirection ψ p =
    -((hbar ^ 2 / (2 * mass) : ℝ) : ℂ) * gpeLaplacian ψ p +
      (↑(gint * gpeDensity ψ p + V p) : ℂ) * ψ p

/-- The wave momentum density in one Cartesian direction. -/
def gpeMomentum (hbar : ℝ) (ψ : GPESpacetime → ℂ) (k : Fin 2) (p : GPESpacetime) : ℝ :=
  hbar * (conj (ψ p) * gpePartial (gpeSpaceDirection k) ψ p).im

/-- The polynomial spatial stress of the wave. The mixed derivative
term carries the quantum correction and the diagonal term is the
interaction pressure. -/
def gpeWaveStress (mass gint hbar : ℝ) (ψ : GPESpacetime → ℂ)
    (j k : Fin 2) (p : GPESpacetime) : ℝ :=
  hbar ^ 2 / (2 * mass) *
      (conj (gpePartial (gpeSpaceDirection j) ψ p) * gpePartial (gpeSpaceDirection k) ψ p -
        conj (ψ p) * gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection k) ψ) p).re +
    if j = k then gint / 2 * gpeDensity ψ p ^ 2 else 0

/-- The Fréchet derivative gives the derivative along the affine
line in a chosen direction. -/
theorem hasDerivAt_gpePartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : GPESpacetime → F} {p d : GPESpacetime} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun r : ℝ => f (p + r • d)) (gpePartial d f p) 0 := by
  have hline : HasDerivAt (fun r : ℝ => p + r • d) d 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add p)
  have he : p + (0 : ℝ) • d = p := by simp
  have hp : HasFDerivAt f (fderiv ℝ f p) (p + (0 : ℝ) • d) := by
    rw [he]
    exact hf.hasFDerivAt
  change HasDerivAt (f ∘ (fun r : ℝ => p + r • d)) ((fderiv ℝ f p) d) 0
  exact hp.comp_hasDerivAt 0 hline

/-- Taking one directional derivative loses one derivative of regularity. -/
theorem contDiff_gpePartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : GPESpacetime → F} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hm : m + 1 ≤ n)
    (d : GPESpacetime) : ContDiff ℝ m (gpePartial d f) :=
  (hf.fderiv_right hm).clm_apply contDiff_const

/-- A twice continuously differentiable function has commuting
Cartesian partials in any two fixed directions. -/
private theorem gpePartial_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : GPESpacetime → F} (hf : ContDiff ℝ 2 f) (a b : GPESpacetime) :
    gpePartial a (gpePartial b f) = gpePartial b (gpePartial a f) := by
  have hdiff := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  funext p
  have hsym : IsSymmSndFDerivAt ℝ f p := hf.contDiffAt.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ 2)
  have hev (v w : GPESpacetime) : gpePartial v (gpePartial w f) p =
      (fderiv ℝ (fderiv ℝ f) p v) w := by
    change fderiv ℝ (fun x => fderiv ℝ f x w) p v = _
    rw [fderiv_clm_apply (hdiff p) (differentiableAt_const w)]
    simp
  rw [hev a b, hev b a]
  exact hsym.eq a b

/-- Spatial derivatives on the fixed-time slice agree with the
Cartesian axis lines used by the stationary formulation. -/
theorem gpePartial_space_eq_axisLine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : GPESpacetime → F} (p : GPESpacetime) (j : Fin 2) (hf : DifferentiableAt ℝ f p) :
    gpePartial (gpeSpaceDirection j) f p =
      deriv (fun r => f (p.1, axisLine p.2 j r)) 0 := by
  have hh := (hasDerivAt_gpePartial (d := gpeSpaceDirection j) hf).deriv
  have he (r : ℝ) : p + r • gpeSpaceDirection j = (p.1, axisLine p.2 j r) := by
    rcases p with ⟨t, x, y⟩
    fin_cases j <;> simp [gpeSpaceDirection, axisLine]
  simpa only [he] using hh.symm

/-- The time derivative is the ordinary derivative with the spatial
point fixed. -/
theorem gpePartial_time_eq_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : GPESpacetime → F} (p : GPESpacetime) (hf : DifferentiableAt ℝ f p) :
    gpePartial gpeTimeDirection f p = deriv (fun s => f (p.1 + s, p.2)) 0 := by
  have hh := (hasDerivAt_gpePartial (d := gpeTimeDirection) hf).deriv
  have he (r : ℝ) : p + r • gpeTimeDirection = (p.1 + r, p.2) := by
    rcases p with ⟨t, x, y⟩
    simp [gpeTimeDirection]
  simpa only [he] using hh.symm

/-- The spatial Laplacian agrees with the original fixed-time model. -/
theorem gpeLaplacian_eq_waveLaplacian (ψ : GPESpacetime → ℂ)
    (hψ : ContDiff ℝ 2 ψ) (p : GPESpacetime) :
    gpeLaplacian ψ p = waveLaplacian (fun q => ψ (p.1, q)) p.2 := by
  have h1 := hψ.differentiable (by norm_num)
  unfold gpeLaplacian waveLaplacian
  apply Finset.sum_congr rfl
  intro j _
  have hd := (contDiff_gpePartial hψ (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    (gpeSpaceDirection j)).differentiable (by norm_num)
  rw [gpePartial_space_eq_axisLine p j (hd p)]
  congr 1
  funext s
  rw [gpePartial_space_eq_axisLine (p.1, axisLine p.2 j s) j (h1 _)]

/-- Complex conjugation can be differentiated over the real line. -/
private theorem hasDerivAt_conj {f : ℝ → ℂ} {f' : ℂ} {r : ℝ} (hf : HasDerivAt f f' r) :
    HasDerivAt (fun s => conj (f s)) (conj f') r :=
  Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hf

/-- The real part can be differentiated over the real line. -/
private theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {r : ℝ} (hf : HasDerivAt f f' r) :
    HasDerivAt (fun s => (f s).re) f'.re r :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hf

/-- The imaginary part can be differentiated over the real line. -/
private theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {r : ℝ} (hf : HasDerivAt f f' r) :
    HasDerivAt (fun s => (f s).im) f'.im r :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hf

/-- The squared density has the regularity of the complex wave even
at an amplitude zero. -/
private theorem contDiff_gpeDensity {n : WithTop ℕ∞} {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ n ψ) : ContDiff ℝ n (gpeDensity ψ) := by
  have hr : ContDiff ℝ n (fun p => (ψ p).re) := Complex.reCLM.contDiff.comp hψ
  have hi : ContDiff ℝ n (fun p => (ψ p).im) := Complex.imCLM.contDiff.comp hψ
  have he : gpeDensity ψ = fun p => (ψ p).re * (ψ p).re + (ψ p).im * (ψ p).im :=
    funext fun p => Complex.normSq_apply (ψ p)
  rw [he]
  exact (hr.mul hr).add (hi.mul hi)

/-- A twice continuously differentiable wave has a continuously
differentiable momentum density. -/
theorem contDiff_gpeMomentum (hbar : ℝ) (k : Fin 2) {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 2 ψ) : ContDiff ℝ 1 (gpeMomentum hbar ψ k) := by
  have hc : ContDiff ℝ 1 (fun p => conj (ψ p)) :=
    Complex.conjCLE.contDiff.comp (hψ.of_le (by norm_num))
  have h1 : ContDiff ℝ 1 (gpePartial (gpeSpaceDirection k) ψ) :=
    contDiff_gpePartial hψ (by norm_num) _
  have hi : ContDiff ℝ 1 (fun p => (conj (ψ p) * gpePartial (gpeSpaceDirection k) ψ p).im) :=
    Complex.imCLM.contDiff.comp (hc.mul h1)
  exact contDiff_const.mul hi

/-- The stress of a three-times continuously differentiable wave
is continuously differentiable, including at zeros of the wave. -/
theorem contDiff_gpeWaveStress (mass gint hbar : ℝ) (j k : Fin 2)
    {ψ : GPESpacetime → ℂ} (hψ : ContDiff ℝ 3 ψ) :
    ContDiff ℝ 1 (gpeWaveStress mass gint hbar ψ j k) := by
  let d := gpeSpaceDirection j
  let e := gpeSpaceDirection k
  let K := hbar ^ 2 / (2 * mass)
  have h1d : ContDiff ℝ 2 (gpePartial d ψ) := contDiff_gpePartial hψ (by norm_num) _
  have h1e : ContDiff ℝ 2 (gpePartial e ψ) := contDiff_gpePartial hψ (by norm_num) _
  have h2 : ContDiff ℝ 1 (gpePartial d (gpePartial e ψ)) :=
    contDiff_gpePartial h1e (by norm_num) _
  have hρ : ContDiff ℝ 1 (gpeDensity ψ) := contDiff_gpeDensity (hψ.of_le (by norm_num))
  have hconj {f : GPESpacetime → ℂ} (hf : ContDiff ℝ 1 f) :
      ContDiff ℝ 1 (fun p => conj (f p)) := Complex.conjCLE.contDiff.comp hf
  have hf : ContDiff ℝ 1 (fun q =>
      conj (gpePartial d ψ q) * gpePartial e ψ q -
        conj (ψ q) * gpePartial d (gpePartial e ψ) q) :=
    ((hconj (h1d.of_le (by norm_num))).mul (h1e.of_le (by norm_num))).sub
      ((hconj (hψ.of_le (by norm_num))).mul h2)
  have hr : ContDiff ℝ 1 (fun q => K * (conj (gpePartial d ψ q) * gpePartial e ψ q -
        conj (ψ q) * gpePartial d (gpePartial e ψ) q).re) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp hf)
  have hp : ContDiff ℝ 1 (fun q => if j = k then gint / 2 * gpeDensity ψ q ^ 2 else 0) := by
    by_cases hEq : j = k
    · simp only [hEq, ite_true]
      exact contDiff_const.mul (hρ.pow 2)
    · simpa only [hEq, ite_false] using (contDiff_const :
        ContDiff ℝ 1 (fun _ : GPESpacetime => (0 : ℝ)))
  exact hr.add hp

/-- The differentiated spatial Laplacian uses the actual third
Fréchet derivatives of the wave. -/
private theorem hasDerivAt_gpeLaplacian_line {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 3 ψ) (p d : GPESpacetime) :
    HasDerivAt (fun r : ℝ => gpeLaplacian ψ (p + r • d))
      (∑ j : Fin 2, gpePartial d
        (gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ)) p) 0 := by
  unfold gpeLaplacian
  apply HasDerivAt.fun_sum
  intro j _
  have h1 : ContDiff ℝ 2 (gpePartial (gpeSpaceDirection j) ψ) :=
    contDiff_gpePartial hψ (by norm_num) _
  have h2 : ContDiff ℝ 1
      (gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ)) :=
    contDiff_gpePartial h1 (by norm_num) _
  exact hasDerivAt_gpePartial ((h2.differentiable (by norm_num)) p)

/-- The spatial derivative of the wave equation follows on the open
fluid region by differentiating along a short coordinate line. -/
private theorem gpe_spatial_equation_derivative (mass gint hbar : ℝ)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hU : IsOpen U)
    (hEq : ∀ x ∈ U, GrossPitaevskiiAt mass gint hbar V ψ x)
    (p : GPESpacetime) (hp : p ∈ U) (d : GPESpacetime) :
    (hbar : ℂ) * Complex.I * gpePartial d (gpePartial gpeTimeDirection ψ) p =
      -((hbar ^ 2 / (2 * mass) : ℝ) : ℂ) *
        (∑ j : Fin 2, gpePartial d
          (gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ)) p) +
      (↑(gint * gpePartial d (gpeDensity ψ) p + gpePartial d V p) : ℂ) * ψ p +
      (↑(gint * gpeDensity ψ p + V p) : ℂ) * gpePartial d ψ p := by
  let W (q : GPESpacetime) := gint * gpeDensity ψ q + V q
  let K := (hbar ^ 2 / (2 * mass) : ℝ)
  let q (r : ℝ) := p + r • d
  have hq0 : q 0 = p := by simp [q]
  have hq : Continuous q := by dsimp only [q]; fun_prop
  have hn : ∀ᶠ r : ℝ in 𝓝 0, q r ∈ U :=
    hq.continuousAt (hU.mem_nhds (by simpa only [hq0] using hp))
  have hdψ := hψ.differentiable (by norm_num)
  have htψ : ContDiff ℝ 2 (gpePartial gpeTimeDirection ψ) :=
    contDiff_gpePartial hψ (by norm_num) _
  have hT := hasDerivAt_gpePartial (d := d) (htψ.differentiable (by norm_num) p)
  have hP := hasDerivAt_gpePartial (d := d) (hdψ p)
  have hρ := hasDerivAt_gpePartial (d := d) ((contDiff_gpeDensity hψ).differentiable (by norm_num) p)
  have hV' := hasDerivAt_gpePartial (d := d) (hV.differentiable (by norm_num) p)
  have hW : HasDerivAt (fun r => W (q r))
      (gint * gpePartial d (gpeDensity ψ) p + gpePartial d V p) 0 :=
    (hρ.const_mul gint).fun_add hV'
  have hLap := hasDerivAt_gpeLaplacian_line hψ p d
  have hL := hT.const_mul ((hbar : ℂ) * Complex.I)
  have hR := (hLap.const_mul (-(K : ℂ))).fun_add (hW.ofReal_comp.fun_mul hP)
  have he : (fun r => (hbar : ℂ) * Complex.I * gpePartial gpeTimeDirection ψ (q r)) =ᶠ[𝓝 0]
      (fun r => -(K : ℂ) * gpeLaplacian ψ (q r) + (W (q r) : ℂ) * ψ (q r)) := by
    filter_upwards [hn] with r hr
    exact hEq _ hr
  have h := hL.deriv.symm.trans (he.deriv_eq.trans hR.deriv)
  simpa only [q, zero_smul, add_zero, ← add_assoc] using h

/-- The wave equation and its spatial derivative give the exact
imaginary-product cancellation in the momentum time derivative. -/
private theorem gpe_momentum_algebra (h K W W' : ℝ) (a b T L U M : ℂ)
    (he : (h : ℂ) * Complex.I * T = -(K : ℂ) * L + (W : ℂ) * a)
    (hd : (h : ℂ) * Complex.I * U = -(K : ℂ) * M + (W' : ℂ) * a + (W : ℂ) * b) :
    h * (conj T * b + conj a * U).im =
      K * (conj a * M - conj L * b).re - W' * Complex.normSq a := by
  have heR := congrArg Complex.re he
  have heI := congrArg Complex.im he
  have hdR := congrArg Complex.re hd
  have hdI := congrArg Complex.im hd
  simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply] at heR heI hdR hdI ⊢
  linear_combination b.re * heR + b.im * heI - a.re * hdR - a.im * hdI

/-- The time derivative of the true wave momentum uses the wave
equation and its spatial derivative, with the mixed partials commuted. -/
private theorem gpePartial_time_momentum (mass gint hbar : ℝ)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hU : IsOpen U)
    (hEq : ∀ x ∈ U, GrossPitaevskiiAt mass gint hbar V ψ x)
    (p : GPESpacetime) (hp : p ∈ U) (k : Fin 2) :
    gpePartial gpeTimeDirection (gpeMomentum hbar ψ k) p =
      hbar ^ 2 / (2 * mass) *
        (conj (ψ p) * (∑ j : Fin 2, gpePartial (gpeSpaceDirection k)
          (gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ)) p) -
          conj (gpeLaplacian ψ p) * gpePartial (gpeSpaceDirection k) ψ p).re -
      (gint * gpePartial (gpeSpaceDirection k) (gpeDensity ψ) p +
        gpePartial (gpeSpaceDirection k) V p) * gpeDensity ψ p := by
  let d := gpeSpaceDirection k
  let τ := gpeTimeDirection
  have h1 : ContDiff ℝ 2 (gpePartial d ψ) := contDiff_gpePartial hψ (by norm_num) _
  have hP := hasDerivAt_gpePartial (d := τ) (hψ.differentiable (by norm_num) p)
  have hD := hasDerivAt_gpePartial (d := τ) (h1.differentiable (by norm_num) p)
  have hM := contDiff_gpeMomentum hbar k (hψ.of_le (by norm_num))
  have hm := (hasDerivAt_im ((hasDerivAt_conj hP).fun_mul hD)).const_mul hbar
  have hdir := hasDerivAt_gpePartial (d := τ) (hM.differentiable (by norm_num) p)
  have hm' : HasDerivAt (fun r : ℝ => gpeMomentum hbar ψ k (p + r • τ))
      (hbar * (conj (gpePartial τ ψ p) * gpePartial d ψ p +
        conj (ψ p) * gpePartial τ (gpePartial d ψ) p).im) 0 := by
    simpa only [gpeMomentum, d, τ, zero_smul, add_zero] using hm
  rw [hdir.unique hm', gpePartial_comm (hψ.of_le (by norm_num)) τ d]
  exact gpe_momentum_algebra hbar (hbar ^ 2 / (2 * mass))
    (gint * gpeDensity ψ p + V p)
    (gint * gpePartial d (gpeDensity ψ) p + gpePartial d V p)
    (ψ p) (gpePartial d ψ p) (gpePartial τ ψ p) (gpeLaplacian ψ p) _ _
    (hEq p hp) (gpe_spatial_equation_derivative mass gint hbar hV hψ hU hEq p hp d)

/-- The flux through coordinate direction j differentiates to the
uncancelled two kinetic terms and the diagonal pressure derivative. -/
private theorem gpePartial_waveStress (mass gint hbar : ℝ) {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 3 ψ) (p : GPESpacetime) (j k : Fin 2) :
    gpePartial (gpeSpaceDirection j) (gpeWaveStress mass gint hbar ψ j k) p =
      hbar ^ 2 / (2 * mass) *
        (conj (gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ) p) *
            gpePartial (gpeSpaceDirection k) ψ p -
          conj (ψ p) * gpePartial (gpeSpaceDirection k)
            (gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ)) p).re +
      if j = k then gint * gpeDensity ψ p * gpePartial (gpeSpaceDirection j) (gpeDensity ψ) p
        else 0 := by
  let d := gpeSpaceDirection j
  let e := gpeSpaceDirection k
  let K := hbar ^ 2 / (2 * mass)
  have h1d : ContDiff ℝ 2 (gpePartial d ψ) := contDiff_gpePartial hψ (by norm_num) _
  have h1e : ContDiff ℝ 2 (gpePartial e ψ) := contDiff_gpePartial hψ (by norm_num) _
  have h2 : ContDiff ℝ 1 (gpePartial d (gpePartial e ψ)) :=
    contDiff_gpePartial h1e (by norm_num) _
  have hρ : ContDiff ℝ 1 (gpeDensity ψ) := contDiff_gpeDensity (hψ.of_le (by norm_num))
  have hj := hasDerivAt_gpePartial (d := d) (h1d.differentiable (by norm_num) p)
  have hk := hasDerivAt_gpePartial (d := d) (h1e.differentiable (by norm_num) p)
  have hψ' := hasDerivAt_gpePartial (d := d) (hψ.differentiable (by norm_num) p)
  have h2' := hasDerivAt_gpePartial (d := d) (h2.differentiable (by norm_num) p)
  have hh := ((hasDerivAt_conj hj).fun_mul hk).fun_sub
    ((hasDerivAt_conj hψ').fun_mul h2')
  have hpress : HasDerivAt
      (fun r : ℝ => if j = k then gint / 2 * gpeDensity ψ (p + r • d) ^ 2 else 0)
      (if j = k then gint * gpeDensity ψ p * gpePartial d (gpeDensity ψ) p else 0) 0 := by
    by_cases hEq : j = k
    · simp only [hEq, ite_true]
      have h := hasDerivAt_gpePartial (d := d) (hρ.differentiable (by norm_num) p)
      refine ((h.fun_pow 2).const_mul (gint / 2)).congr_deriv ?_
      simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    · simp only [hEq, ite_false]
      exact hasDerivAt_const 0 (0 : ℝ)
  have hstress := (contDiff_gpeWaveStress mass gint hbar j k hψ).differentiable (by norm_num) p
  have ht := hasDerivAt_gpePartial (d := d) hstress
  have hcalc := ((hasDerivAt_re hh).const_mul K).fun_add hpress
  rw [ht.unique hcalc]
  simp only [zero_smul, add_zero]
  change K * (conj (gpePartial d (gpePartial d ψ) p) * gpePartial e ψ p +
      conj (gpePartial d ψ p) * gpePartial d (gpePartial e ψ) p -
      (conj (gpePartial d ψ p) * gpePartial d (gpePartial e ψ) p +
        conj (ψ p) * gpePartial d (gpePartial d (gpePartial e ψ)) p)).re + _ = _
  have h3 : gpePartial d (gpePartial d (gpePartial e ψ)) p =
      gpePartial e (gpePartial d (gpePartial d ψ)) p := by
    rw [gpePartial_comm (hψ.of_le (by norm_num)) d e,
      gpePartial_comm h1d d e]
  rw [h3]
  have he (a b c : ℂ) : a + b - (b + c) = a - c := by ring
  rw [he]

/-- Local momentum balance for a smooth time-dependent two-dimensional
Gross–Pitaevskii wave. It includes the real potential's force density
and remains valid at a node of the wave. -/
theorem gpe_local_momentum_balance (mass gint hbar : ℝ)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ} {U : Set GPESpacetime}
    (hV : ContDiff ℝ 1 V) (hψ : ContDiff ℝ 3 ψ) (hU : IsOpen U)
    (hEq : ∀ x ∈ U, GrossPitaevskiiAt mass gint hbar V ψ x)
    (p : GPESpacetime) (hp : p ∈ U) (k : Fin 2) :
    gpePartial gpeTimeDirection (gpeMomentum hbar ψ k) p +
      (∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (gpeWaveStress mass gint hbar ψ j k) p) =
        -gpeDensity ψ p * gpePartial (gpeSpaceDirection k) V p := by
  rw [gpePartial_time_momentum mass gint hbar hV hψ hU hEq p hp k]
  simp only [gpePartial_waveStress mass gint hbar hψ, gpeLaplacian, Fin.sum_univ_two]
  fin_cases k <;> simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] <;> ring

end Qatlib.Papers.SuperfoilLift19.LiftForce
