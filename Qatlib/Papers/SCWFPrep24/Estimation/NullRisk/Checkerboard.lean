/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedSpinInstrument
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Checkerboard

Real coordinates of the first physical spin component.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- Real coordinates of the first physical spin component. -/
def real0 {A : Type*} (ψ : A → Bool → ℂ) (x : A) : ℝ := (ψ x false).re
/-- Imaginary coordinates of the first physical spin component. -/
def imag0 {A : Type*} (ψ : A → Bool → ℂ) (x : A) : ℝ := (ψ x false).im
/-- Real coordinates of the second physical spin component. -/
def real1 {A : Type*} (ψ : A → Bool → ℂ) (x : A) : ℝ := (ψ x true).re
/-- Imaginary coordinates of the second physical spin component. -/
def imag1 {A : Type*} (ψ : A → Bool → ℂ) (x : A) : ℝ := (ψ x true).im

/-- The finite null-family spinor retains one fixed hidden phase at every address. -/
def checkerboardSpinor {A : Type*} (parity : A → Bool) (ζ : A → ℂ)
    (basis : Bool → Bool → ℂ) (x : A) (b : Bool) : ℂ := ζ x*basis (parity x) b

/-- The source real-coordinate spinor is exactly the original physical complex spinor. -/
theorem complexSpinor_parts {A : Type*} (ψ : A → Bool → ℂ) (x : A) :
    complexSpinor (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) x = ψ x := by
  funext b
  cases b <;> rfl

/-- The source current's imaginary inner product is exactly the physical overlap imaginary part. -/
theorem spinorInnerIm_parts {A : Type*} (ψ : A → Bool → ℂ) (x y : A) :
    spinorInnerIm (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) x y =
      (overlap (ψ x) (ψ y)).im := by
  simp only [spinorInnerIm, real0, imag0, real1, imag1, overlap,
    Complex.add_im, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Local phase multiplication preserves the actual physical overlap, with its full two-site phase factor. -/
theorem overlap_scale (z w : ℂ) (u v : Bool → ℂ) :
    overlap (fun b => z*u b) (fun b => w*v b) = star z*w*overlap u v := by
  simp only [overlap, star_mul]
  ring

/-- Multiplying a qubit by a complex phase scales its literal mass by the phase norm square. -/
theorem qubitMass_scale (z : ℂ) (u : Bool → ℂ) :
    qubitMass (fun b => z*u b) = Complex.normSq z*qubitMass u := by
  simp only [qubitMass, Complex.normSq_mul]
  ring

/-- The actual source Pauli coordinates scale by the phase norm square. -/
theorem qubitBloch_scale (z : ℂ) (u : Bool → ℂ) (i : Fin 3) :
    qubitBloch (fun b => z*u b) i = Complex.normSq z*qubitBloch u i := by
  fin_cases i <;>
    simp [qubitBloch, pauliField, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- Every hidden-phase checkerboard input is pointwise normalized. -/
theorem checkerboard_normalized {A : Type*} (parity : A → Bool) (ζ : A → ℂ)
    (basis : Bool → Bool → ℂ) (hζ : ∀ x, Complex.normSq (ζ x) = 1)
    (hb : ∀ b, qubitMass (basis b) = 1) (x : A) :
    qubitMass (checkerboardSpinor parity ζ basis x) = 1 := by
  change qubitMass (fun b => ζ x*basis (parity x) b) = 1
  rw [qubitMass_scale, hζ, hb, one_mul]

/-- A bijective unit shift which flips parity also flips parity under its inverse, including wrap edges. -/
theorem inverse_parity_flip {A : Type*} (parity : A → Bool) (e : A ≃ A)
    (he : ∀ x, parity (e x) = !(parity x)) (x : A) :
    parity (e.symm x) = !(parity x) := by
  have h := he (e.symm x)
  simp only [e.apply_symm_apply] at h
  rw [h, Bool.not_not]

/-- Both physical unit neighbors are orthogonal to the input spin, regardless of the shared hidden phases. -/
theorem checkerboard_neighbor_overlap {A : Type*} (parity : A → Bool) (ζ : A → ℂ)
    (basis : Bool → Bool → ℂ) (e : A ≃ A)
    (hb : ∀ b, overlap (basis b) (basis (!b)) = 0)
    (he : ∀ x, parity (e x) = !(parity x)) (x : A) :
    overlap (checkerboardSpinor parity ζ basis x)
      (checkerboardSpinor parity ζ basis (e x)) = 0 ∧
    overlap (checkerboardSpinor parity ζ basis x)
      (checkerboardSpinor parity ζ basis (e.symm x)) = 0 := by
  constructor
  · change overlap (fun b => ζ x*basis (parity x) b)
      (fun b => ζ (e x)*basis (parity (e x)) b) = 0
    rw [overlap_scale, he, hb, mul_zero]
  · change overlap (fun b => ζ x*basis (parity x) b)
      (fun b => ζ (e.symm x)*basis (parity (e.symm x)) b) = 0
    rw [overlap_scale, inverse_parity_flip parity e he x, hb, mul_zero]

/-- The full original current is zero on every member of the null family, not merely on average over the prior. -/
theorem checkerboard_current_zero {A : Type*} {d : ℕ}
    (parity : A → Bool) (ζ : A → ℂ) (basis : Bool → Bool → ℂ)
    (e : Fin d → A ≃ A) (hb : ∀ b, overlap (basis b) (basis (!b)) = 0)
    (he : ∀ j x, parity (e j x) = !(parity x)) (j : Fin d) (x : A) :
    spinorCurrentMean (real0 (checkerboardSpinor parity ζ basis))
      (imag0 (checkerboardSpinor parity ζ basis))
      (real1 (checkerboardSpinor parity ζ basis))
      (imag1 (checkerboardSpinor parity ζ basis)) e j x = 0 := by
  obtain ⟨hp, hm⟩ := checkerboard_neighbor_overlap parity ζ basis (e j) hb (he j) x
  simp only [spinorCurrentMean, spinorInnerIm_parts, hp, hm, Complex.zero_im,
    sub_self, zero_div]

/-- The forward and inverse physical unit neighbors have equal actual source Pauli vectors; local hidden phases do not change them. -/
theorem checkerboard_neighbor_bloch {A : Type*} (parity : A → Bool) (ζ : A → ℂ)
    (basis : Bool → Bool → ℂ) (e : A ≃ A) (hζ : ∀ x, Complex.normSq (ζ x) = 1)
    (he : ∀ x, parity (e x) = !(parity x)) (x : A) (i : Fin 3) :
    qubitBloch (checkerboardSpinor parity ζ basis (e x)) i =
      qubitBloch (checkerboardSpinor parity ζ basis (e.symm x)) i := by
  change qubitBloch (fun b => ζ (e x)*basis (parity (e x)) b) i =
    qubitBloch (fun b => ζ (e.symm x)*basis (parity (e.symm x)) b) i
  rw [qubitBloch_scale, qubitBloch_scale, hζ, hζ, one_mul, one_mul,
    he, inverse_parity_flip parity e he x]

/-- The actual source's four real coordinate fields are pointwise normalized on every null-family input. -/
theorem checkerboard_source_normalization {A : Type*} (parity : A → Bool)
    (ζ : A → ℂ) (basis : Bool → Bool → ℂ)
    (hζ : ∀ x, Complex.normSq (ζ x) = 1) (hb : ∀ b, qubitMass (basis b) = 1) (x : A) :
    real0 (checkerboardSpinor parity ζ basis) x^2 +
      imag0 (checkerboardSpinor parity ζ basis) x^2 +
        real1 (checkerboardSpinor parity ζ basis) x^2 +
          imag1 (checkerboardSpinor parity ζ basis) x^2 = 1 := by
  have h := checkerboard_normalized parity ζ basis hζ hb x
  simpa only [qubitMass, real0, imag0, real1, imag1, Complex.normSq_apply,
    pow_two, add_assoc] using h

/-- Every member of the legal checkerboard family has zero FULL original loss: the current square and all central-spin terms both vanish pointwise. -/
theorem checkerboard_full_original_loss_zero {A : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] {d : ℕ} (parity : A → Bool) (ζ : A → ℂ)
    (basis : Bool → Bool → ℂ) (e : Fin d → A ≃ A)
    (hζ : ∀ x, Complex.normSq (ζ x) = 1)
    (hb : ∀ b, overlap (basis b) (basis (!b)) = 0)
    (he : ∀ j x, parity (e j x) = !(parity x)) (h lam : ℝ) :
    spinorDiscreteLoss (real0 (checkerboardSpinor parity ζ basis))
      (imag0 (checkerboardSpinor parity ζ basis))
      (real1 (checkerboardSpinor parity ζ basis))
      (imag1 (checkerboardSpinor parity ζ basis)) (fun _ _ => 0) e h 1 lam = 0 := by
  let ψ := checkerboardSpinor parity ζ basis
  have hcurrent (j : Fin d) (x : A) :
      spinorCurrentMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) e j x = 0 :=
    checkerboard_current_zero parity ζ basis e hb he j x
  have hpauli (j : Fin d) (x : A) (i : Fin 3) :
      pauliField (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) i (e j x) =
        pauliField (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) i ((e j).symm x) := by
    change qubitBloch (ψ (e j x)) i = qubitBloch (ψ ((e j).symm x)) i
    exact checkerboard_neighbor_bloch parity ζ basis (e j) hζ (he j) x i
  have hspin (j : Fin d) (x : A) (i : Fin 3) :
      sourceSpinOfPauli (pauliField (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)) i (e j x) =
        sourceSpinOfPauli (pauliField (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)) i ((e j).symm x) := by
    unfold sourceSpinOfPauli
    split_ifs <;> rw [hpauli]
  change spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
    (fun _ _ => 0) e h 1 lam = 0
  simp [spinorDiscreteLoss, hcurrent, hspin, siteMean]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
