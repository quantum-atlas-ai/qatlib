/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.DynamicMomentum

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Mass continuity of the Gross–Pitaevskii wave

[Musser2019Superfoil], equations (1) and (2),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
The real interaction and potential terms cancel from the continuity
equation. This gives the mass balance for the actual current without
dividing by the amplitude or introducing a phase at a node.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open scoped ComplexConjugate

/-- The density changes by twice the real conjugate product of the
wave and its directional derivative. -/
private theorem gpePartial_density_eq {ψ : GPESpacetime → ℂ} {p : GPESpacetime}
    (hψ : DifferentiableAt ℝ ψ p) (d : GPESpacetime) :
    gpePartial d (gpeDensity ψ) p = 2 * (conj (ψ p) * gpePartial d ψ p).re := by
  have he : gpeDensity ψ = fun q => (ψ q).re * (ψ q).re + (ψ q).im * (ψ q).im :=
    funext fun q => Complex.normSq_apply (ψ q)
  rw [he]
  have hRe : DifferentiableAt ℝ (fun q => (ψ q).re) p :=
    Complex.reCLM.differentiableAt.comp p hψ
  have hIm : DifferentiableAt ℝ (fun q => (ψ q).im) p :=
    Complex.imCLM.differentiableAt.comp p hψ
  have hρ := hasDerivAt_gpePartial (d := d) ((hRe.mul hRe).add (hIm.mul hIm))
  have hψ' := hasDerivAt_gpePartial (d := d) hψ
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hψ'
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hψ'
  refine hρ.unique (((hr.fun_mul hr).fun_add (hi.fun_mul hi)).congr_deriv ?_)
  simp [Function.comp_apply, zero_smul, Complex.mul_re]
  ring

/-- The current's spatial divergence is the imaginary conjugate
product with the actual spatial Laplacian. -/
private theorem gpe_divergence_momentum_eq (hbar : ℝ) {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 2 ψ) (p : GPESpacetime) :
    (∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (gpeMomentum hbar ψ j) p) =
      hbar * (conj (ψ p) * gpeLaplacian ψ p).im := by
  have ht (j : Fin 2) :
      gpePartial (gpeSpaceDirection j) (gpeMomentum hbar ψ j) p =
        hbar * (conj (ψ p) *
          gpePartial (gpeSpaceDirection j) (gpePartial (gpeSpaceDirection j) ψ) p).im := by
    let d := gpeSpaceDirection j
    have h1 : ContDiff ℝ 1 (gpePartial d ψ) := contDiff_gpePartial hψ (by norm_num) _
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
    have hψ' := hasDerivAt_gpePartial (d := d) (hψ1.differentiable (by norm_num) p)
    have hd := hasDerivAt_gpePartial (d := d) (h1.differentiable (by norm_num) p)
    have hM := contDiff_gpeMomentum hbar j hψ
    have hdir := hasDerivAt_gpePartial (d := d) (hM.differentiable (by norm_num) p)
    have hB : HasDerivAt (fun r : ℝ => conj (ψ (p + r • d))) (conj (gpePartial d ψ p)) 0 :=
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hψ'
    have him : HasDerivAt
        (fun r : ℝ => (conj (ψ (p + r • d)) * gpePartial d ψ (p + r • d)).im)
        (conj (gpePartial d ψ p) * gpePartial d ψ (p + (0 : ℝ) • d) +
          conj (ψ (p + (0 : ℝ) • d)) * gpePartial d (gpePartial d ψ) p).im 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (hB.fun_mul hd)
    refine hdir.unique ((him.const_mul hbar).congr_deriv ?_)
    simp only [zero_smul, add_zero, Complex.add_im, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, d]
    ring
  simp only [ht, gpeLaplacian, Fin.sum_univ_two, Complex.add_re, Complex.add_im, Complex.mul_im]
  ring

/-- The time-dependent Gross–Pitaevskii equation gives the exact
density continuity equation, including at zeros of the wave. -/
theorem gpe_local_mass_balance (mass gint hbar : ℝ) (hm : mass ≠ 0) (hh : hbar ≠ 0)
    {V : GPESpacetime → ℝ} {ψ : GPESpacetime → ℂ}
    (hψ : ContDiff ℝ 2 ψ) (p : GPESpacetime)
    (he : GrossPitaevskiiAt mass gint hbar V ψ p) :
    gpePartial gpeTimeDirection (gpeDensity ψ) p +
      (1 / mass) * (∑ j : Fin 2, gpePartial (gpeSpaceDirection j) (gpeMomentum hbar ψ j) p) = 0 := by
  let a := ψ p
  let T := gpePartial gpeTimeDirection ψ p
  let L := gpeLaplacian ψ p
  let K := hbar ^ 2 / (2 * mass)
  let W := gint * gpeDensity ψ p + V p
  change (hbar : ℂ) * Complex.I * T = -(K : ℂ) * L + (W : ℂ) * a at he
  have hR := congrArg Complex.re he
  have hI := congrArg Complex.im he
  have hcross : hbar * (conj a * T).re + K * (conj a * L).im = 0 := by
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hR hI ⊢
    linear_combination a.re * hI - a.im * hR
  have hsolve : (conj a * T).re = (-K * (conj a * L).im) / hbar := by
    exact (eq_div_iff hh).2 (by linarith only [hcross])
  rw [gpePartial_density_eq (hψ.differentiable (by norm_num) p),
    gpe_divergence_momentum_eq hbar hψ p]
  change 2 * (conj a * T).re + (1 / mass) * (hbar * (conj a * L).im) = 0
  rw [hsolve]
  dsimp only [K]
  field_simp [hm, hh]
  ring

end Qatlib.Papers.SuperfoilLift19.LiftForce
