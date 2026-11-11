/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.Transform
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! Necessary normalization, Born, and character-state bridges for the
actual finite Fourier consumers. Source: pinned Frozen c1e805dd. This prefix
does not include a PMF adapter, gate macro, tensor circuit, or resource claim. -/

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

open Matrix
open scoped ComplexConjugate Kronecker Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Inner products are preserved in the repository's existing state semantics. -/
theorem inner_fourier [DecidableEq G] (ψ φ : QState G) :
    Inner (fourier ψ) (fourier φ) = Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, fourier]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    fourierMatrix_conjTranspose_mul, Matrix.vecMul_one]

/-- Normalization is a consequence of Fourier orthogonality, not an input certificate. -/
theorem normalized_fourier_iff [DecidableEq G] (ψ : QState G) :
    Normalized (fourier ψ) ↔ Normalized ψ := by
  classical
  rw [normalized_iff_inner_self, inner_fourier, normalized_iff_inner_self]

/-- The Fourier transform of a normalized state is normalized. -/
theorem normalized_fourier [DecidableEq G] {ψ : QState G} (hψ : Normalized ψ) :
    Normalized (fourier ψ) := (normalized_fourier_iff ψ).2 hψ

/-- Actual Born probabilities, available also for unnormalized input. -/
theorem bornProb_fourier (ψ : QState G) (χ : AddChar G ℂ) :
    BornProb (fourier ψ) χ = ‖fourierScale G * ∑ x, conj (χ x) * ψ x‖ ^ 2 := by
  rw [BornProb, fourier_apply]

/-- The inverse also preserves the original normalization predicate. -/
theorem normalized_fourierInv_iff [DecidableEq G] (φ : QState (AddChar G ℂ)) :
    Normalized (fourierInv φ) ↔ Normalized φ := by
  have h := normalized_fourier_iff (fourierInv φ)
  simpa only [fourier_fourierInv] using h.symm

/-- Fourier analysis as an average differs by exactly `sqrt(card G)`. -/
theorem fourier_eq_sqrt_mul_average (ψ : QState G) (χ : AddChar G ℂ) :
    fourier ψ χ = (Real.sqrt (Fintype.card G) : ℂ) *
      ((Fintype.card G : ℂ)⁻¹ * ∑ x, conj (χ x) * ψ x) := by
  have hc : (Real.sqrt (Fintype.card G) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2
      (Nat.cast_pos.2 (Fintype.card_pos) : (0 : ℝ) < Fintype.card G)).ne'
  have h := fourierScale_mul_self (G := G)
  rw [fourier_apply, ← h, fourierScale]
  field_simp

/-- Every computational basis ket has the expected character-phase amplitudes. -/
theorem fourier_ket [DecidableEq G] (x : G) (χ : AddChar G ℂ) :
    fourier (Ket x) χ = fourierScale G * conj (χ x) := by
  simp [fourier_apply, Ket]

omit [AddCommGroup G] in
/-- The normalization factor has squared norm `1 / card G`. -/
theorem norm_fourierScale_sq : ‖fourierScale G‖ ^ 2 = (Fintype.card G : ℝ)⁻¹ := by
  simp [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Fourier measurement of a basis ket is uniform on the actual dual basis. -/
theorem bornProb_fourier_ket [DecidableEq G] (x : G) (χ : AddChar G ℂ) :
    BornProb (fourier (Ket x)) χ = 1 / (Fintype.card (AddChar G ℂ) : ℝ) := by
  simp [BornProb, fourier_ket, AddChar.norm_apply, norm_fourierScale_sq]

/-- A normalized character state on the original group basis. -/
noncomputable def characterState (χ : AddChar G ℂ) : QState G :=
  fun x => fourierScale G * χ x

/-- Character states are read at their own character label, not its negative. -/
theorem fourier_characterState (η : AddChar G ℂ) :
    fourier (characterState η) = Ket η := by
  funext χ
  rw [fourier_apply]
  simp only [characterState]
  calc
    fourierScale G * (∑ x, conj (χ x) * (fourierScale G * η x)) =
        (fourierScale G * fourierScale G) * (∑ x, η x * conj (χ x)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = Ket η χ := by
      rw [sum_char_mul_conj]
      by_cases h : χ = η
      · subst χ
        simp [Ket, fourierScale_sq_mul_card]
      · simp [h, Ne.symm h, Ket]

/-- Normalization follows from the proved transform law. -/
theorem normalized_characterState [DecidableEq G] (χ : AddChar G ℂ) :
    Normalized (characterState χ) := by
  rw [← normalized_fourier_iff, fourier_characterState]
  exact normalized_ket χ

/-- The trivial character state is precisely the existing uniform superposition. -/
@[simp] theorem characterState_zero : characterState (0 : AddChar G ℂ) = Uniform G := by
  funext x
  simp [characterState, Uniform, fourierScale]

/-- Uniform input is read out deterministically at the trivial character. -/
theorem fourier_uniform : fourier (Uniform G) = Ket (0 : AddChar G ℂ) := by
  rw [← characterState_zero, fourier_characterState]

section Marginals
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Original actual marginal Born event, including entangled input; no conditional state update. -/
noncomputable def MarginalProbLeft (ψ : QState (I × J)) (S : Finset I) : ℝ :=
  MeasureProb ψ (S ×ˢ Finset.univ)

/-- Original actual marginal Born event, including entangled input; no conditional state update. -/
noncomputable def MarginalProbRight (ψ : QState (I × J)) (T : Finset J) : ℝ :=
  MeasureProb ψ (Finset.univ ×ˢ T)

end Marginals

end Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
