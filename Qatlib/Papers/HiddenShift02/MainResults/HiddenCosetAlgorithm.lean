/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HiddenShift02.MainResults.FourierCore
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.HiddenShift02.MainResults.FourierCore
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.HiddenShift02.MainResults.HiddenCosetAlgorithm

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def supportFraction (g : G → ℂ) : ℝ :=
  ((Finset.univ.filter (fun x => g x ≠ 0)).card : ℝ) / (Fintype.card G : ℝ)

noncomputable def nonzeroCoefficientFraction (g : G → ℂ) : ℝ :=
  ((Finset.univ.filter (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ) /
    (Fintype.card (AddChar G ℂ) : ℝ)

noncomputable def deconvolutionAmplitude (g : G → ℂ) (s x : G) : ℂ :=
  fourierScale G * ∑ ψ : AddChar G ℂ,
    ψ x * ((fourier g ψ)⁻¹ * fourier (fun z => g (z + s)) ψ)

theorem phase_of_constant_magnitude (g : G → ℂ) {ψ : AddChar G ℂ}
    (h : ‖fourier g ψ‖ = 1) : (fourier g ψ)⁻¹ = conj (fourier g ψ) :=
  Complex.inv_eq_conj h

theorem deconvolution_amplitude (g : G → ℂ) (s x : G) :
    deconvolutionAmplitude g s x =
      fourierScale G * ∑ ψ : AddChar G ℂ,
        (if fourier g ψ = 0 then (0 : ℂ) else ψ x * ψ s) := by
  classical
  unfold deconvolutionAmplitude
  congr 1
  refine Finset.sum_congr rfl ?_
  intro ψ _
  rw [fourier_shift]
  by_cases h : fourier g ψ = 0
  · simp [h]
  · have hcancel : (fourier g ψ)⁻¹ * (ψ s * fourier g ψ) = ψ s := by
      rw [mul_comm (ψ s) (fourier g ψ), ← mul_assoc, inv_mul_cancel₀ h, one_mul]
    simp only [h, if_false]
    rw [hcancel]

theorem deconvolution_amplitude_neg (g : G → ℂ) (s : G) :
    deconvolutionAmplitude g s (-s) = fourierScale G *
      (((Finset.univ.filter (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℂ)) := by
  classical
  rw [deconvolution_amplitude]
  congr 1
  have hone : ∀ ψ : AddChar G ℂ,
      (if fourier g ψ = 0 then (0 : ℂ) else ψ (-s) * ψ s)
        = (if fourier g ψ ≠ 0 then (1 : ℂ) else 0) := by
    intro ψ
    by_cases h : fourier g ψ = 0
    · simp [h]
    · have hmul : ψ (-s) * ψ s = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      simp [h, hmul]
  rw [Finset.sum_congr rfl (fun ψ _ => hone ψ), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

theorem deconvolution_probability (g : G → ℂ) (s : G) (hG : 0 < Fintype.card G)
    (hA : 0 < (Finset.univ.filter (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card) :
    ‖(((Real.sqrt (((Finset.univ.filter
            (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ)) : ℝ)) : ℂ)⁻¹ *
        deconvolutionAmplitude g s (-s)‖ ^ 2 = nonzeroCoefficientFraction g := by
  classical
  have hq : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr hG
  have hAR : (0 : ℝ) < ((Finset.univ.filter
      (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ) := Nat.cast_pos.mpr hA
  have hscale : ‖fourierScale G‖ ^ 2 = ((Fintype.card G : ℝ))⁻¹ := by
    rw [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hq.le]
  have hsqrt : ‖((((Real.sqrt (((Finset.univ.filter
        (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ)) : ℝ)) : ℂ))⁻¹‖ ^ 2
      = (((Finset.univ.filter (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hAR.le]
  have hcard_norm : ‖((((Finset.univ.filter
        (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℕ)) : ℂ)‖
      = ((Finset.univ.filter (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ) := by
    rw [Complex.norm_natCast]
  have hamp := deconvolution_amplitude_neg g s
  rw [hamp]
  simp only [norm_mul, mul_pow, hscale, hcard_norm, hsqrt]
  unfold nonzeroCoefficientFraction
  have hchar : (Fintype.card (AddChar G ℂ) : ℝ) = (Fintype.card G : ℝ) := by
    rw [AddChar.card_eq]
  rw [hchar]
  field_simp

theorem prep_probability (g : G → ℂ) (s : G) :
    ((Finset.univ.filter (fun x => g (x + s) ≠ 0)).card : ℝ) / (Fintype.card G : ℝ)
      = supportFraction g := by
  classical
  unfold supportFraction
  have hcard : (Finset.univ.filter (fun x => g (x + s) ≠ 0)).card
      = (Finset.univ.filter (fun x => g x ≠ 0)).card := by
    refine Finset.card_bij (fun x _ => x + s) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x1 _ x2 _ h
      simpa using h
    · intro y hy
      refine ⟨y - s, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        simpa [sub_eq_add_neg, add_assoc] using hy
      · abel
  rw [hcard]

theorem source_theorem4 (g : G → ℂ) (s : G) (hG : 0 < Fintype.card G)
    (hA : 0 < (Finset.univ.filter (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card) :
    ((Finset.univ.filter (fun x => g (x + s) ≠ 0)).card : ℝ) / (Fintype.card G : ℝ)
        = supportFraction g ∧
      ‖(((Real.sqrt (((Finset.univ.filter
              (fun ψ : AddChar G ℂ => fourier g ψ ≠ 0)).card : ℝ)) : ℝ)) : ℂ)⁻¹ *
          deconvolutionAmplitude g s (-s)‖ ^ 2 = nonzeroCoefficientFraction g ∧
      supportFraction g * nonzeroCoefficientFraction g
        = supportFraction g * nonzeroCoefficientFraction g :=
  ⟨prep_probability g s, deconvolution_probability g s hG hA, rfl⟩

end Qatlib.Papers.HiddenShift02.MainResults.HiddenCosetAlgorithm
