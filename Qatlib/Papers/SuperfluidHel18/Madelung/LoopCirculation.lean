/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.PolarCurrent
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Quantized circulation away from the vortex core

[Kedia2018SuperfluidHelicity], Section II,
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
On a smooth parametrized loop, the Madelung velocity paired with the
loop tangent is the normalized probability current of the pulled-back
wavefunction. The complex logarithmic derivative supplies the phase
increment directly along the loop.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

open MeasureTheory
open scoped ComplexConjugate

/-- The Madelung velocity paired with the loop tangent, in terms of the
pullback of the wavefunction. -/
noncomputable def madelungLoopVelocity (ℏ m : ℝ) (ψ : ℝ → ℂ) (t : ℝ) : ℝ :=
  (ℏ / m) * (deriv ψ t / ψ t).im

/-- The imaginary logarithmic derivative is exactly the probability
current divided by density where the wavefunction has no zero. -/
theorem madelungLoopVelocity_eq_current (ℏ m : ℝ) (ψ : ℝ → ℂ) {t : ℝ}
    (ht : ψ t ≠ 0) :
    madelungLoopVelocity ℏ m ψ t =
      (ℏ / m) * ((conj (ψ t) * deriv ψ t).im / Complex.normSq (ψ t)) := by
  have hq : deriv ψ t / ψ t =
      (conj (ψ t) * deriv ψ t) / (Complex.normSq (ψ t) : ℂ) := by
    rw [← Complex.mul_conj]
    field_simp [ht]
  rw [madelungLoopVelocity, hq]
  congr 1
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add]

/-- Pulling back a spatial wavefunction along a differentiable curve pairs
its normalized probability current with the actual curve tangent. -/
theorem madelungLoopVelocity_pullback (ℏ m : ℝ) (Ψ : (Fin 3 → ℝ) → ℂ)
    (γ : ℝ → Fin 3 → ℝ) (t : ℝ) (hΨ : DifferentiableAt ℝ Ψ (γ t))
    (hγ : DifferentiableAt ℝ γ t) (hne : Ψ (γ t) ≠ 0) :
    madelungLoopVelocity ℏ m (Ψ ∘ γ) t =
      (ℏ / m) * ((conj (Ψ (γ t)) * fderiv ℝ Ψ (γ t) (deriv γ t)).im /
        Complex.normSq (Ψ (γ t))) := by
  rw [madelungLoopVelocity_eq_current ℏ m (Ψ ∘ γ) hne,
    (hΨ.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt).deriv]
  simp only [Function.comp_apply]

/-- Integrating the logarithmic derivative reconstructs the relative
wavefunction at the endpoints of any nonvanishing smooth pullback. -/
theorem exp_integral_logDeriv_mul_eq {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hne : ∀ t, ψ t ≠ 0) (a b : ℝ) :
    Complex.exp (∫ t in a..b, deriv ψ t / ψ t) * ψ a = ψ b := by
  let d := fun t => deriv ψ t / ψ t
  let D := fun s => ∫ t in a..s, d t
  have hd : Continuous d := hψ.continuous_deriv_one.div hψ.continuous hne
  have hD (s : ℝ) : HasDerivAt D (d s) s :=
    intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable _ _)
      hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
  have hconst (s : ℝ) : HasDerivAt (fun t => Complex.exp (-D t) * ψ t) 0 s := by
    have hψ' := (hψ.differentiable (by norm_num) s).hasDerivAt
    refine ((hD s).neg.cexp.mul hψ').congr_deriv ?_
    dsimp only [d]
    field_simp [hne s]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun s _ => hconst s) (intervalIntegrable_const (c := (0 : ℂ)))
  have hval : Complex.exp (-D b) * ψ b = ψ a := by
    apply sub_eq_zero.mp
    simpa only [D, intervalIntegral.integral_const, smul_zero, intervalIntegral.integral_same,
      neg_zero, Complex.exp_zero, one_mul] using hFTC.symm
  calc
    _ = Complex.exp (D b) * (Complex.exp (-D b) * ψ b) := by rw [hval]
    _ = ψ b := by rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- A closed nonvanishing wavefunction pullback has circulation an
integer multiple of the circulation quantum `2πℏ/m`. -/
theorem exists_int_madelungLoopCirculation (ℏ m : ℝ) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hne : ∀ t, ψ t ≠ 0) {a b : ℝ} (hclose : ψ a = ψ b) :
    ∃ n : ℤ, (∫ t in a..b, madelungLoopVelocity ℏ m ψ t) =
      (2 * Real.pi * ℏ / m) * (n : ℝ) := by
  let d := fun t => deriv ψ t / ψ t
  have hd : Continuous d := hψ.continuous_deriv_one.div hψ.continuous hne
  have he : Complex.exp (∫ t in a..b, d t) = 1 := by
    apply mul_right_cancel₀ (hne a)
    calc
      _ = ψ b := exp_integral_logDeriv_mul_eq hψ hne a b
      _ = 1 * ψ a := by rw [hclose, one_mul]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, ?_⟩
  simp only [madelungLoopVelocity, intervalIntegral.integral_const_mul]
  change ℏ / m * (∫ t in a..b, Complex.im (d t)) = _
  have hIm : (∫ t in a..b, (d t).im) = (∫ t in a..b, d t).im :=
    Complex.imCLM.intervalIntegral_comp_comm (hd.intervalIntegrable a b)
  rw [hIm, hn]
  simp [Complex.mul_im, Complex.mul_re, div_eq_mul_inv]
  ring

end Qatlib.Papers.SuperfluidHel18.Madelung
