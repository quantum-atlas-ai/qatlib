/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.RotatingBell
import Qatlib.Concepts.SpinorSampling.Retained.LowSpinLossBridge

set_option backward.isDefEq.respectTransparency false

/-!
# Phased Alternative

The actual slow-rotation input keeps one complete hidden fourth-root assignment fixed for both supplied copies.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The actual slow-rotation input keeps one complete hidden fourth-root assignment fixed for both supplied copies. -/
def phasedRotatingField (d N : ℕ) [NeZero N] (j : Fin d) (α : ℂ)
    (ω : (Fin d → Fin N) → Fin 4) (x : Fin d → Fin N) (s : Bool) : ℂ :=
  fourthPhase (ω x)*rotatingField d N j α x s

/-- Every individual physical slow-rotation input is pointwise normalized in the source's original four real coordinates. -/
theorem phasedRotatingField_source_normalization (d N : ℕ) [NeZero N] (j : Fin d)
    (α : ℂ) (hα : Complex.normSq α = 1)
    (ω : (Fin d → Fin N) → Fin 4) (x : Fin d → Fin N) :
    real0 (phasedRotatingField d N j α ω) x^2+
      imag0 (phasedRotatingField d N j α ω) x^2+
      real1 (phasedRotatingField d N j α ω) x^2+
      imag1 (phasedRotatingField d N j α ω) x^2 = 1 := by
  have hm : qubitMass (phasedRotatingField d N j α ω x) = 1 := by
    change qubitMass (fun s => fourthPhase (ω x)*rotatingField d N j α x s) = 1
    rw [qubitMass_scale, fourthPhase_normSq, rotatingField_mass d N j α hα, one_mul]
  simpa only [qubitMass, real0, imag0, real1, imag1, Complex.normSq_apply,
    pow_two, add_assoc] using hm

/-- Every individual shared-phase slow-rotation input has zero actual global source Bloch vector. -/
theorem phasedRotatingField_global_bloch_zero (d N : ℕ) [NeZero N] [Fact (1 < N)]
    (j : Fin d) (α : ℂ) (hα : Complex.normSq α = 1)
    (ω : (Fin d → Fin N) → Fin 4) (i : Fin 3) :
    (∑ x, qubitBloch (phasedRotatingField d N j α ω x) i) = 0 := by
  change (∑ x, qubitBloch (fun s => fourthPhase (ω x)*rotatingField d N j α x s) i) = 0
  simp_rw [qubitBloch_scale, fourthPhase_normSq, one_mul]
  exact rotatingField_global_bloch_zero d N j α hα i

/-- The physical singlet determinant scales by the actual two local amplitudes. -/
theorem determinant_scale (z w : ℂ) (u v : Bool → ℂ) :
    determinant (fun s => z*u s) (fun s => w*v s) = z*w*determinant u v := by
  simp only [determinant]
  ring

/-- The actual double-shift Bell probabilities of the phased alternative retain the exact sin²(h)/2 value and zero unused directions for every fixed hidden assignment. -/
theorem phasedRotatingField_double_bell (d N : ℕ) [NeZero N] (j k : Fin d)
    (α : ℂ) (hα : Complex.normSq α = 1)
    (ω : (Fin d → Fin N) → Fin 4) (x : Fin d → Fin N) :
    bellProbability (phasedRotatingField d N j α ω x)
      (phasedRotatingField d N j α ω (periodicDoubleShift d N k x)) =
      if k=j then (Real.sin (2*Real.pi/N))^2/2 else 0 := by
  have hp : bellProbability (phasedRotatingField d N j α ω x)
      (phasedRotatingField d N j α ω (periodicDoubleShift d N k x)) =
      bellProbability (rotatingField d N j α x)
        (rotatingField d N j α (periodicDoubleShift d N k x)) := by
    unfold bellProbability
    change Complex.normSq (determinant (fun s => fourthPhase (ω x)*rotatingField d N j α x s)
      (fun s => fourthPhase (ω (periodicDoubleShift d N k x))*
        rotatingField d N j α (periodicDoubleShift d N k x) s))/2 = _
    rw [determinant_scale, Complex.normSq_mul, Complex.normSq_mul,
      fourthPhase_normSq, fourthPhase_normSq, one_mul, one_mul]
  rw [hp, rotatingField_double_bell_probability d N j k α hα]

/-- The actual Bell mean on each physical double shift is the exact claimed probability. -/
theorem phasedRotatingField_bellMean (d N : ℕ) [NeZero N] (j k : Fin d)
    (α : ℂ) (hα : Complex.normSq α = 1)
    (ω : (Fin d → Fin N) → Fin 4) :
    bellMean (real0 (phasedRotatingField d N j α ω))
      (imag0 (phasedRotatingField d N j α ω))
      (real1 (phasedRotatingField d N j α ω))
      (imag1 (phasedRotatingField d N j α ω)) (periodicDoubleShift d N k) =
      if k=j then (Real.sin (2*Real.pi/N))^2/2 else 0 := by
  unfold bellMean
  simp_rw [complexSpinor_parts, phasedRotatingField_double_bell d N j k α hα ω]
  exact site_mean_const _

/-- The complete physical alternative obeys the promised original full-loss gap; its actual nonnegative current residual is retained rather than replaced by a spin-only objective. -/
theorem phasedRotatingField_full_original_loss_gap (d N : ℕ) [NeZero N]
    (j : Fin d) (α : ℂ) (hα : Complex.normSq α = 1)
    (ω : (Fin d → Fin N) → Fin 4) (lam : ℝ) :
    lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2 ≤
      spinorDiscreteLoss (real0 (phasedRotatingField d N j α ω))
        (imag0 (phasedRotatingField d N j α ω))
        (real1 (phasedRotatingField d N j α ω))
        (imag1 (phasedRotatingField d N j α ω))
        (fun _ _ => 0) (periodicUnitShift d N) (2*Real.pi/N) 1 lam := by
  let ψ := phasedRotatingField d N j α ω
  have hn := phasedRotatingField_source_normalization d N j α hα ω
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hh : (2*Real.pi/N : ℝ) ≠ 0 := (div_pos (by positivity) hN).ne'
  rw [spinor_discrete_loss_eq _ _ _ _ hn _ _ _ _ _ hh (by norm_num),
    implemented_loss_bell_form _ _ _ _ _ _ hn]
  simp_rw [periodic_unit_shift_square]
  have hs : (∑ k : Fin d, bellMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (periodicDoubleShift d N k)) = (Real.sin (2*Real.pi/N))^2/2 := by
    simp only [ψ, phasedRotatingField_bellMean d N j _ α hα ω, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  rw [hs]
  have hv : 0 ≤ ∑ k : Fin d, siteMean (fun x =>
      ((1/(2*Real.pi/N))*spinorCurrentMean (real0 ψ) (imag0 ψ) (real1 ψ)
        (imag1 ψ) (periodicUnitShift d N) k x-(1/(1:ℝ))*(0:ℝ))^2) := by
    exact Finset.sum_nonneg fun _ _ => site_mean_nonneg _ fun _ => sq_nonneg _
  have he : lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2 =
      4*(lam^2/(2*(2*Real.pi/N)^2))*((Real.sin (2*Real.pi/N))^2/2) := by ring
  rw [he]
  exact le_add_of_nonneg_left hv

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
