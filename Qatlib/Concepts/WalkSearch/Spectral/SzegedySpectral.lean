/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Szegedy frames and the spectral rotation map

This module defines the swapped frame `SzegedyIsometryB` and the real `SzegedyDiscriminant`, and
identifies the cross Gram matrix of the two Szegedy frames with that discriminant. It expresses
`SzegedyWalk` as the product of their range reflections.

`twoReflection_rotation` constructs an orthonormal invariant plane from a normalized cross-Gram
eigenvector. Its specialization `szegedy_spectral_map` transfers a discriminant eigenvalue `cos
θ` to the walk's double-angle rotation action, as in [Szegedy2004].

## Main statements

* `szegedy_gram_eq_discriminant`: frame overlap equals the discriminant.
* `szegedyWalk_eq_twoReflections`: reflection-product representation.
* `szegedy_spectral_map`: the double-angle spectral rotation map.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.WalkSearch.Spectral

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The second Szegedy frame, obtained by applying the register swap to `SzegedyIsometry P`. -/
noncomputable def SzegedyIsometryB (P : I → I → ℝ) : Matrix (I × I) I ℂ :=
  SwapGate * SzegedyIsometry P

/-- Applying the register swap twice is the identity. -/
theorem swapGate_mul_self :
    SwapGate * SwapGate = (1 : Matrix (I × I) (I × I) ℂ) :=
  permMatrix_mul_self Prod.swap_swap

/-- The register swap matrix equals its adjoint. -/
theorem swapGate_hermitian : (SwapGate : Matrix (I × I) (I × I) ℂ)ᴴ = SwapGate :=
  permMatrix_conjTranspose Prod.swap_swap

/-- Left multiplication by the swap gate exchanges the two components of a row index. -/
theorem swapGate_mul_apply (M : Matrix (I × I) I ℂ) (p : I × I) (y : I) :
    (SwapGate * M : Matrix (I × I) I ℂ) p y = M (Prod.swap p) y := by
  show (∑ r : I × I, (SwapGate : Matrix (I × I) (I × I) ℂ) p r * M r y) = _
  rw [Finset.sum_eq_single (Prod.swap p)]
  · rw [SwapGate, permMatrix, Matrix.of_apply, if_pos (Prod.swap_swap p).symm, one_mul]
  · intro r _ hr
    rw [SwapGate, permMatrix, Matrix.of_apply,
      if_neg (fun h => hr (((congrArg Prod.swap h).trans (Prod.swap_swap r)).symm)),
      zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- The Szegedy row frame has entry `sqrt (P x b)` when the first register equals its column
index, and zero otherwise. -/
theorem szegedyIsometry_apply_pair (P : I → I → ℝ) (a b : I) (x : I) :
    SzegedyIsometry P (a, b) x = if a = x then ((Real.sqrt (P x b) : ℂ)) else 0 := rfl

/-- The swapped Szegedy frame has entry `sqrt (P y a)` when the second register equals its
column index, and zero otherwise. -/
theorem szegedyIsometryB_apply (P : I → I → ℝ) (a b : I) (y : I) :
    SzegedyIsometryB P (a, b) y = if b = y then ((Real.sqrt (P y a) : ℂ)) else 0 := by
  rw [SzegedyIsometryB]
  show (SwapGate * SzegedyIsometry P : Matrix (I × I) I ℂ) (a, b) y = _
  rw [swapGate_mul_apply]
  rfl

/-- For a transition matrix, the swapped Szegedy frame has orthonormal columns. -/
theorem szegedyIsometryB_conjTranspose_mul (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    (SzegedyIsometryB P)ᴴ * SzegedyIsometryB P = 1 := by
  ext x y
  show (∑ p : I × I, (starRingEnd ℂ) (SzegedyIsometryB P p x) * SzegedyIsometryB P p y)
      = (1 : Matrix I I ℂ) x y
  rw [Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Fintype.sum_prod_type]
    have hinner : ∀ a : I, (∑ b : I, (starRingEnd ℂ) (SzegedyIsometryB P (a, b) x)
        * SzegedyIsometryB P (a, b) x) = ((P x a : ℂ)) := by
      intro a
      rw [Finset.sum_eq_single x]
      · rw [szegedyIsometryB_apply, if_pos rfl, starRingEnd_ofReal,
          ← Complex.ofReal_mul, ← sq, Real.sq_sqrt (hP.1 x a)]
      · intro b _ hb
        rw [szegedyIsometryB_apply, if_neg hb, map_zero, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ x) hcon
    rw [Finset.sum_congr rfl fun a _ => hinner a, ← Complex.ofReal_sum, hP.2 x,
      Complex.ofReal_one]
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨a, b⟩ := p
    by_cases hbx : b = x
    · rw [szegedyIsometryB_apply, szegedyIsometryB_apply, if_pos hbx,
        starRingEnd_ofReal, if_neg (fun h => hxy (hbx.symm.trans h)), mul_zero]
    · rw [szegedyIsometryB_apply, if_neg hbx, map_zero, zero_mul]

/-- The real discriminant matrix with entries `sqrt (P x y * P y x)`. -/
noncomputable def SzegedyDiscriminant (P : I → I → ℝ) : Matrix I I ℝ :=
  Matrix.of fun x y => Real.sqrt (P x y * P y x)

/-- Evaluate an entry of the Szegedy discriminant as the square root of the product of the two
opposite transition probabilities. -/
theorem szegedyDiscriminant_apply (P : I → I → ℝ) (x y : I) :
    SzegedyDiscriminant P x y = Real.sqrt (P x y * P y x) := rfl

/-- The cross Gram matrix of the two Szegedy frames is the complexification of the real
discriminant. -/
theorem szegedy_gram_eq_discriminant (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    (SzegedyIsometry P)ᴴ * SzegedyIsometryB P
      = (SzegedyDiscriminant P).map Complex.ofReal := by
  ext x y
  show (∑ p : I × I, (starRingEnd ℂ) (SzegedyIsometry P p x) * SzegedyIsometryB P p y)
      = (SzegedyDiscriminant P).map Complex.ofReal x y
  rw [Fintype.sum_prod_type]
  simp only [szegedyIsometry_apply_pair, szegedyIsometryB_apply, Matrix.map_apply,
    szegedyDiscriminant_apply]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · rw [if_pos rfl, if_pos rfl, starRingEnd_ofReal, ← Complex.ofReal_mul,
        ← Real.sqrt_mul (hP.1 x y)]
    · intro b _ hb
      rw [if_neg hb, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ y) hcon
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg ha, map_zero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ x) hcon

/-- The cross Gram matrix of the Szegedy frames is Hermitian for a transition matrix. -/
theorem szegedy_gram_hermitian (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P)ᴴ
      = (SzegedyIsometry P)ᴴ * SzegedyIsometryB P := by
  rw [szegedy_gram_eq_discriminant P hP]
  ext x y
  rw [Matrix.conjTranspose_apply]
  simp only [Matrix.map_apply, szegedyDiscriminant_apply, RCLike.star_def,
    starRingEnd_ofReal, mul_comm (P y x) (P x y)]

/-- Conjugation by the swap gate exchanges the two components of both matrix indices. -/
theorem swapGate_mul_mul_swapGate (X : Matrix (I × I) (I × I) ℂ) (p q : I × I) :
    ((SwapGate * X) * SwapGate : Matrix (I × I) (I × I) ℂ) p q
      = X (Prod.swap p) (Prod.swap q) := by
  show (∑ r : I × I, (SwapGate * X : Matrix (I × I) (I × I) ℂ) p r
      * (SwapGate : Matrix (I × I) (I × I) ℂ) r q) = _
  rw [Finset.sum_eq_single (Prod.swap q)]
  · rw [SwapGate, permMatrix, Matrix.of_apply, if_pos rfl, mul_one]
    show (∑ s : I × I, (SwapGate : Matrix (I × I) (I × I) ℂ) p s
        * X s (Prod.swap q)) = _
    rw [Finset.sum_eq_single (Prod.swap p)]
    · rw [SwapGate, permMatrix, Matrix.of_apply, if_pos (Prod.swap_swap p).symm,
        one_mul]
    · intro s _ hs
      rw [SwapGate, permMatrix, Matrix.of_apply,
        if_neg (fun h => hs (((congrArg Prod.swap h).trans (Prod.swap_swap s)).symm)),
        zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · intro r _ hr
    rw [SwapGate, permMatrix, Matrix.of_apply, if_neg (fun h => hr h), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- The Szegedy walk is the product of reflections about the ranges of its swapped and original
frames [Szegedy2004]. -/
theorem szegedyWalk_eq_twoReflections (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    SzegedyWalk P = ReflectionAbout (SzegedyIsometryB P * (SzegedyIsometryB P)ᴴ) *
      ReflectionAbout (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) := by
  have hconj : SwapGate * (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) * SwapGate
      = SzegedyIsometryB P * (SzegedyIsometryB P)ᴴ := by
    ext ⟨a, i⟩ ⟨b, i'⟩
    rw [show (SwapGate * (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) * SwapGate)
        = (SwapGate * (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)) * SwapGate from rfl,
      swapGate_mul_mul_swapGate, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Prod.swap_prod_mk, Matrix.conjTranspose_apply, szegedyIsometry_apply_pair,
      szegedyIsometryB_apply]
  have hBR : SwapGate * SzegedyReflection P * SwapGate
      = ReflectionAbout (SzegedyIsometryB P * (SzegedyIsometryB P)ᴴ) := by
    rw [SzegedyReflection, ReflectionAbout, ReflectionAbout]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul,
      Matrix.smul_mul, swapGate_mul_self, hconj]
  rw [SzegedyWalk, hBR, SzegedyReflection]

/-- A normalized eigenvector of a Hermitian cross Gram matrix with eigenvalue `cos θ` and
nonzero `sin θ` yields an orthonormal two-dimensional frame on which the reflection product
has the stated double-angle rotation action. -/
theorem twoReflection_rotation {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    [DecidableEq K] (A B : Matrix K I ℂ) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hGram : (Aᴴ * B)ᴴ = Aᴴ * B)
    (v : QState I) (hv : Normalized v) (θ : ℝ) (hs : Real.sin θ ≠ 0)
    (hvD : (Aᴴ * B) *ᵥ v = ((Real.cos θ : ℝ) : ℂ) • v) :
    ∃ (w₀ w₁ : QState K), Normalized w₀ ∧ Normalized w₁ ∧ Inner w₀ w₁ = 0 ∧
      (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ w₀
        = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ + (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ ∧
      (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ w₁
        = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ + (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁ := by
  have hsℂ : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hs2c : ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 - ((Real.cos θ : ℝ) : ℂ) ^ 2 := by
    have h : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    linear_combination h
  set w₀ : QState K := A *ᵥ v with hw₀def
  set w₂ : QState K := B *ᵥ v with hw₂def
  set φ : QState K := w₂ - ((Real.cos θ : ℝ) : ℂ) • w₀ with hφdef
  set w₁ : QState K := (((Real.sin θ : ℝ) : ℂ))⁻¹ • φ with hw₁def
  have hv00 : Inner v v = 1 := inner_self_eq_one hv

  have hBdA : (Bᴴ * A) *ᵥ v = ((Real.cos θ : ℝ) : ℂ) • v := by
    have hBA : Bᴴ * A = Aᴴ * B := by
      rw [← hGram, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hBA]
    exact hvD

  have hw₀norm : Normalized w₀ := by
    rw [normalized_iff_inner_self, hw₀def, inner_mulVec_left_rect, Matrix.mulVec_mulVec,
      hA, Matrix.one_mulVec]
    exact hv00
  have hw₂norm : Normalized w₂ := by
    rw [normalized_iff_inner_self, hw₂def, inner_mulVec_left_rect, Matrix.mulVec_mulVec,
      hB, Matrix.one_mulVec]
    exact hv00
  have hw₀00 : Inner w₀ w₀ = 1 := (normalized_iff_inner_self _).mp hw₀norm
  have hw₂00 : Inner w₂ w₂ = 1 := (normalized_iff_inner_self _).mp hw₂norm
  have h0₂ : Inner w₀ w₂ = ((Real.cos θ : ℝ) : ℂ) := by
    rw [hw₀def, hw₂def, inner_mulVec_left_rect, Matrix.mulVec_mulVec, hvD,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, hv00, mul_one]
  have h₂0 : Inner w₂ w₀ = ((Real.cos θ : ℝ) : ℂ) := by
    rw [hw₀def, hw₂def, inner_mulVec_left_rect, Matrix.mulVec_mulVec, hBdA,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, hv00, mul_one]

  have hφφ : Inner φ φ = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by
    have hs2r : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      linarith [Real.cos_sq_add_sin_sq θ]
    rw [hφdef, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right, hw₂00,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, h₂0, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, h0₂, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      hw₀00, starRingEnd_ofReal, hs2r]
    push_cast
    ring
  have horth : Inner w₀ w₁ = 0 := by
    rw [hw₁def, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, hφdef,
        Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right, h0₂, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, hw₀00]
    simp
  have hw₁norm : Normalized w₁ := by
    rw [normalized_iff_inner_self, hw₁def, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, ← Complex.ofReal_inv,
      starRingEnd_ofReal, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, hφφ]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast hs)

  have hPAw₀ : (A * Aᴴ) *ᵥ w₀ = w₀ := by
    have hAAhA : A * Aᴴ * A = A := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
    rw [hw₀def, Matrix.mulVec_mulVec, hAAhA]
  have hPBw₀ : (B * Bᴴ) *ᵥ w₀ = ((Real.cos θ : ℝ) : ℂ) • w₂ := by
    rw [hw₀def, hw₂def, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, hBdA, Matrix.mulVec_smul]
  have hPAw₂ : (A * Aᴴ) *ᵥ w₂ = ((Real.cos θ : ℝ) : ℂ) • w₀ := by
    rw [hw₀def, hw₂def, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, hvD, Matrix.mulVec_smul]
  have hPBw₂ : (B * Bᴴ) *ᵥ w₂ = w₂ := by
    have hBBhB : B * Bᴴ * B = B := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [hw₂def, Matrix.mulVec_mulVec, hBBhB]
  have hPAφ : (A * Aᴴ) *ᵥ φ = 0 := by
    rw [hφdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hPAw₂, hPAw₀, sub_self]
  have hPBφ : (B * Bᴴ) *ᵥ φ = (1 - ((Real.cos θ : ℝ) : ℂ) ^ 2) • w₂ := by
    rw [hφdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hPBw₂, hPBw₀, smul_smul]
    module
  have hφeq : φ = ((Real.sin θ : ℝ) : ℂ) • w₁ := by
    rw [hw₁def, smul_smul, mul_inv_cancel₀ hsℂ, one_smul]
  have hw₂eq : w₂ = ((Real.cos θ : ℝ) : ℂ) • w₀ + ((Real.sin θ : ℝ) : ℂ) • w₁ := by
    rw [show w₂ = ((Real.cos θ : ℝ) : ℂ) • w₀ + φ from by
      rw [hφdef]; exact (add_sub_cancel _ _).symm, hφeq]
  have hPAw₁ : (A * Aᴴ) *ᵥ w₁ = 0 := by
    rw [hw₁def, Matrix.mulVec_smul, hPAφ, smul_zero]
  have hPBw₁ : (B * Bᴴ) *ᵥ w₁ = ((Real.sin θ : ℝ) : ℂ) • w₂ := by
    rw [hw₁def, Matrix.mulVec_smul, hPBφ, smul_smul,
      show (((Real.sin θ : ℝ) : ℂ))⁻¹ * (1 - ((Real.cos θ : ℝ) : ℂ) ^ 2)
          = ((Real.sin θ : ℝ) : ℂ) from by rw [← hs2c]; field_simp]

  have hRAw₀ : ReflectionAbout (A * Aᴴ) *ᵥ w₀ = w₀ := by
    rw [reflectionAbout_mulVec, hPAw₀]
    module
  have hRAw₁ : ReflectionAbout (A * Aᴴ) *ᵥ w₁ = -w₁ := by
    rw [reflectionAbout_mulVec, hPAw₁, smul_zero, zero_sub]

  have walk₀ : (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ w₀
      = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ + (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ := by
    rw [← Matrix.mulVec_mulVec, hRAw₀, reflectionAbout_mulVec, hPBw₀, hw₂eq]
    rw [show (((Real.cos (2 * θ) : ℝ)) : ℂ) = 2 * ((Real.cos θ : ℝ) : ℂ) ^ 2 - 1 from by
        rw [Real.cos_two_mul]; push_cast; ring,
      show (((Real.sin (2 * θ) : ℝ)) : ℂ)
          = 2 * ((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ) from by
        rw [Real.sin_two_mul]; push_cast; ring]
    module
  have walk₁ : (ReflectionAbout (B * Bᴴ) * ReflectionAbout (A * Aᴴ)) *ᵥ w₁
      = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ + (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁ := by
    rw [← Matrix.mulVec_mulVec, hRAw₁, Matrix.mulVec_neg, reflectionAbout_mulVec, hPBw₁,
      hw₂eq]
    rw [show -(((Real.sin (2 * θ) : ℝ)) : ℂ)
        = -(2 * ((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) from by
        rw [Real.sin_two_mul]; push_cast; ring,
      show (((Real.cos (2 * θ) : ℝ)) : ℂ) = 1 - 2 * ((Real.sin θ : ℝ) : ℂ) ^ 2 from by
        have h1 : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
          rw [Real.cos_two_mul']
          linarith [Real.cos_sq_add_sin_sq θ]
        rw [h1]
        push_cast
        ring]
    module
  exact ⟨w₀, w₁, hw₀norm, hw₁norm, horth, walk₀, walk₁⟩

/-- A real discriminant eigenvector at `cos θ` becomes an eigenvector of the complex cross Gram
matrix with the same eigenvalue. -/
theorem szegedyDiscriminant_mulVec_complex (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (v : I → ℝ) (θ : ℝ) (hvD : SzegedyDiscriminant P *ᵥ v = (Real.cos θ) • v) :
    ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P) *ᵥ (fun x => ((v x : ℂ)))
      = ((Real.cos θ : ℝ) : ℂ) • (fun x => ((v x : ℂ))) := by
  rw [szegedy_gram_eq_discriminant P hP]
  funext x
  have hsum : ((SzegedyDiscriminant P).map Complex.ofReal *ᵥ (fun y => ((v y : ℂ)))) x
      = ((∑ y, SzegedyDiscriminant P x y * v y : ℝ) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [Finset.sum_congr rfl fun y _ => (Complex.ofReal_mul _ _).symm,
      ← Complex.ofReal_sum]
  rw [hsum, show (∑ y, SzegedyDiscriminant P x y * v y)
      = (SzegedyDiscriminant P *ᵥ v) x from rfl, hvD]
  simp [Pi.smul_apply, smul_eq_mul]

/-- A normalized real discriminant eigenvector with eigenvalue `cos θ` and nonzero `sin θ` gives
an orthonormal plane on which the Szegedy walk has the stated rotation action at angle `2 *
θ` [Szegedy2004]. -/
theorem szegedy_spectral_map (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (v : I → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    (θ : ℝ) (hs : Real.sin θ ≠ 0)
    (hvD : SzegedyDiscriminant P *ᵥ v = (Real.cos θ) • v) :
    ∃ (w₀ w₁ : QState (I × I)), Normalized w₀ ∧ Normalized w₁ ∧ Inner w₀ w₁ = 0 ∧
      SzegedyWalk P *ᵥ w₀
        = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ + (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ ∧
      SzegedyWalk P *ᵥ w₁
        = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ + (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁ := by
  have hvℂ : Normalized (fun x => ((v x : ℂ))) := by
    have hsq : ∀ x, ‖((v x : ℂ))‖ ^ 2 = (v x) ^ 2 := fun x => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    unfold Normalized
    rw [Finset.sum_congr rfl fun x _ => hsq x]
    exact hv
  obtain ⟨w₀, w₁, h0, h1, horth, walk₀, walk₁⟩ := twoReflection_rotation
    (SzegedyIsometry P) (SzegedyIsometryB P)
    (szegedyIsometry_conjTranspose_mul P hP) (szegedyIsometryB_conjTranspose_mul P hP)
    (szegedy_gram_hermitian P hP) _ hvℂ θ hs
    (szegedyDiscriminant_mulVec_complex P hP v θ hvD)
  rw [szegedyWalk_eq_twoReflections P hP]
  exact ⟨w₀, w₁, h0, h1, horth, walk₀, walk₁⟩

end Qatlib.Concepts.WalkSearch.Spectral
