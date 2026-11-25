/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.DynamicMomentum

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Identification with the polar Gross–Pitaevskii stress

[Musser2019Superfoil], equations (2) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
On a polar chart the regular wave momentum is mass times the density
and velocity. The polynomial wave stress agrees with the paper's
convective, pressure, and quantum-stress terms.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Qatlib.Papers.SuperfoilLift19.QuantumCirc (polarWave phaseFactor polar_wave_density phase_factor_norm)
open Qatlib.Papers.SuperfoilLift19.QuantumCirc (phaseFactor_comp_hasDerivAt)
open scoped ComplexConjugate

/-- The polar wave built from smooth amplitude and phase is smooth. -/
private theorem contDiff_polarWave_spacetime {n : WithTop ℕ∞}
    {A φ : GPESpacetime → ℝ} (hA : ContDiff ℝ n A) (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (fun p => polarWave (A p) (φ p)) := by
  have ha : ContDiff ℝ n (fun p => (A p : ℂ)) := Complex.ofRealCLM.contDiff.comp hA
  have hp : ContDiff ℝ n (fun p => (φ p : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  exact ha.mul (hp.mul contDiff_const).cexp

/-- The Cartesian derivative of a polar wave factors into the unit
phase and the usual amplitude and phase derivatives. -/
theorem gpePartial_polarWave {A φ : GPESpacetime → ℝ}
    (hA : ContDiff ℝ 1 A) (hφ : ContDiff ℝ 1 φ) (p d : GPESpacetime) :
    gpePartial d (fun q => polarWave (A q) (φ q)) p =
      ((↑(gpePartial (F := ℝ) d A p) : ℂ) + Complex.I * (A p : ℂ) * (↑(gpePartial (F := ℝ) d φ p) : ℂ)) *
        phaseFactor (φ p) := by
  have ha := hasDerivAt_gpePartial (d := d) (hA.differentiable (by norm_num) p)
  have hp := hasDerivAt_gpePartial (d := d) (hφ.differentiable (by norm_num) p)
  have hw := hasDerivAt_gpePartial (d := d)
    ((contDiff_polarWave_spacetime hA hφ).differentiable (by norm_num) p)
  refine hw.unique ((ha.ofReal_comp.fun_mul (phaseFactor_comp_hasDerivAt hp)).congr_deriv ?_)
  simp only [zero_smul, add_zero]
  ring

/-- The second Cartesian derivative has the differentiated
amplitude and phase coefficients and the product of phase gradients. -/
private theorem gpePartial_polarWave_mixed {A φ : GPESpacetime → ℝ}
    (hA : ContDiff ℝ 2 A) (hφ : ContDiff ℝ 2 φ) (p d e : GPESpacetime) :
    gpePartial d (gpePartial e (fun q => polarWave (A q) (φ q))) p =
      ((↑(gpePartial (F := ℝ) d (gpePartial e A) p) : ℂ) +
        Complex.I * ((↑(gpePartial (F := ℝ) d A p) : ℂ) * (↑(gpePartial (F := ℝ) e φ p) : ℂ) +
          (A p : ℂ) * (↑(gpePartial (F := ℝ) d (gpePartial e φ) p) : ℂ)) +
        ((↑(gpePartial (F := ℝ) e A p) : ℂ) + Complex.I * (A p : ℂ) * (↑(gpePartial (F := ℝ) e φ p) : ℂ)) *
          ((↑(gpePartial (F := ℝ) d φ p) : ℂ) * Complex.I)) * phaseFactor (φ p) := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hdA : ContDiff ℝ 1 (gpePartial e A) := contDiff_gpePartial hA (by norm_num) _
  have hdφ : ContDiff ℝ 1 (gpePartial e φ) := contDiff_gpePartial hφ (by norm_num) _
  have ha := hasDerivAt_gpePartial (d := d) (hA1.differentiable (by norm_num) p)
  have hp := hasDerivAt_gpePartial (d := d) (hφ1.differentiable (by norm_num) p)
  have hea := hasDerivAt_gpePartial (d := d) (hdA.differentiable (by norm_num) p)
  have hep := hasDerivAt_gpePartial (d := d) (hdφ.differentiable (by norm_num) p)
  have hfirst : gpePartial e (fun q => polarWave (A q) (φ q)) = fun q =>
      ((↑(gpePartial (F := ℝ) e A q) : ℂ) + Complex.I * (A q : ℂ) * (↑(gpePartial (F := ℝ) e φ q) : ℂ)) *
        phaseFactor (φ q) := funext fun q => gpePartial_polarWave hA1 hφ1 q e
  have hW := contDiff_gpePartial (contDiff_polarWave_spacetime hA hφ)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2) e
  have hw := hasDerivAt_gpePartial (d := d) (hW.differentiable (by norm_num) p)
  have hC := hea.ofReal_comp.fun_add
    ((ha.ofReal_comp.const_mul Complex.I).fun_mul hep.ofReal_comp)
  have hh := hC.fun_mul (phaseFactor_comp_hasDerivAt hp)
  apply hw.unique
  rw [hfirst]
  refine hh.congr_deriv ?_
  simp only [zero_smul, add_zero]
  ring

/-- Multiplying both factors of a conjugate product by the unit polar
phase leaves the product unchanged. -/
private theorem polarPhase_cancels (θ : ℝ) (a b : ℂ) :
    conj (a * phaseFactor θ) * (b * phaseFactor θ) = conj a * b := by
  have h : phaseFactor θ * conj (phaseFactor θ) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, phase_factor_norm]
    norm_num
  calc
    _ = (conj a * b) * (phaseFactor θ * conj (phaseFactor θ)) := by rw [map_mul]; ring
    _ = _ := by rw [h, mul_one]

/-- The wave momentum is the Madelung density times the phase gradient
and the Planck constant. -/
theorem gpeMomentum_polarWave (hbar : ℝ) {A φ : GPESpacetime → ℝ}
    (hA : ContDiff ℝ 1 A) (hφ : ContDiff ℝ 1 φ) (p : GPESpacetime) (k : Fin 2) :
    gpeMomentum hbar (fun q => polarWave (A q) (φ q)) k p =
      hbar * A p ^ 2 * gpePartial (gpeSpaceDirection k) φ p := by
  unfold gpeMomentum
  rw [gpePartial_polarWave hA hφ]
  simp only [polarWave, polarPhase_cancels]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- The regular wave stress is the paper's stress tensor in a polar
chart, with its quantum density expressed by the amplitude partials. -/
theorem gpeWaveStress_eq_polar (mass gint hbar : ℝ) (hmass : mass ≠ 0)
    {A φ : GPESpacetime → ℝ} (hA : ContDiff ℝ 2 A) (hφ : ContDiff ℝ 2 φ)
    (p : GPESpacetime) (j k : Fin 2) :
    gpeWaveStress mass gint hbar (fun q => polarWave (A q) (φ q)) j k p =
      stressTensor mass gint hbar (fun x => A (p.1, x) ^ 2)
        (fun x i => hbar / mass * gpePartial (gpeSpaceDirection i) φ (p.1, x))
        (amplitudeQuantumStress (fun x => A (p.1, x))
          (fun x i => gpePartial (gpeSpaceDirection i) A (p.1, x))
          (fun x i l => gpePartial (gpeSpaceDirection i) (gpePartial (gpeSpaceDirection l) A)
            (p.1, x))) p.2 j k := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hρ : gpeDensity (fun q => polarWave (A q) (φ q)) p = A p ^ 2 := by
    unfold gpeDensity
    rw [← Complex.sq_norm, polar_wave_density]
  unfold gpeWaveStress
  rw [hρ, gpePartial_polarWave_mixed hA hφ, gpePartial_polarWave hA1 hφ1,
    gpePartial_polarWave hA1 hφ1]
  simp only [polarWave, polarPhase_cancels, stressTensor, amplitudeQuantumStress]
  simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.mul_re, Complex.mul_im]
  field_simp [hmass]
  ring

end Qatlib.Papers.SuperfoilLift19.LiftForce
