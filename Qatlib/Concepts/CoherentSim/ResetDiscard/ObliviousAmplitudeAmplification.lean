/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.NoncommRing
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

variable {R : Type*} [Ring R] [StarRing R]

def ObliviousAmplitudeAmplification (p w : R) : R :=
  -(w * (1 - 2 * p) * star w * (1 - 2 * p) * w)

theorem obliviousAmplitudeAmplification_mem_unitary (p w : R)
    (hp : IsStarProjection p) (hw : w ∈ unitary R) :
    ObliviousAmplitudeAmplification p w ∈ unitary R := by
  have hreflection : 1 - 2 * p ∈ unitary R := by
    rw [show 1 - 2 * p = 2 * (1 - p) - 1 by noncomm_ring]
    exact hp.one_sub.two_mul_sub_one_mem_unitary
  have hproduct := (unitary R).mul_mem
    ((unitary R).mul_mem
      ((unitary R).mul_mem ((unitary R).mul_mem hw hreflection) (Unitary.star_mem hw))
      hreflection) hw
  rw [ObliviousAmplitudeAmplification, Unitary.mem_iff]
  simpa only [star_neg, neg_mul_neg] using (Unitary.mem_iff.mp hproduct)

theorem projected_obliviousAmplitudeAmplification_of_idempotent (p w : R)
    (hp : IsIdempotentElem p) (hw : w ∈ unitary R) :
    p * ObliviousAmplitudeAmplification p w * p =
      3 * (p * w * p) - 4 * (p * w * p * star w * p * w * p) := by
  change p * (-(w * (1 - 2 * p) * star w * (1 - 2 * p) * w)) * p = _
  have hleft := Unitary.star_mul_self_of_mem hw
  have hright := Unitary.mul_star_self_of_mem hw
  have h₁ : p * w * star w * w * p = p * w * p := by
    calc
      _ = p * w * (star w * w) * p := by noncomm_ring
      _ = _ := by rw [hleft, mul_one]
  have h₂ : p * w * p * star w * w * p = p * w * p := by
    calc
      _ = p * w * p * (star w * w) * p := by noncomm_ring
      _ = p * w * (p * p) := by rw [hleft, mul_one, mul_assoc]
      _ = _ := by rw [hp.eq]
  have h₃ : p * w * star w * p * w * p = p * w * p := by
    calc
      _ = p * (w * star w) * p * w * p := by noncomm_ring
      _ = _ := by rw [hright, mul_one, hp.eq]
  calc
    _ = -(p * w * star w * w * p) + 2 * (p * w * p * star w * w * p) +
        2 * (p * w * star w * p * w * p) -
        4 * (p * w * p * star w * p * w * p) := by noncomm_ring
    _ = _ := by rw [h₁, h₂, h₃]; noncomm_ring

theorem projected_obliviousAmplitudeAmplification (p w : R)
    (hp : IsStarProjection p) (hw : w ∈ unitary R) :
    p * ObliviousAmplitudeAmplification p w * p =
      3 * (p * w * p) - 4 * ((p * w * p) * star (p * w * p) * (p * w * p)) := by
  rw [projected_obliviousAmplitudeAmplification_of_idempotent p w hp.isIdempotentElem hw]
  congr 1
  simp only [star_mul, hp.isSelfAdjoint.star_eq]
  simp only [mul_assoc, ← mul_assoc p p, hp.isIdempotentElem.eq]

open Matrix
open scoped ComplexOrder

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

private theorem oaa_embed_smul (j₀ : J) (c : ℂ) (A : Matrix I I ℂ) :
    FiberEmbed j₀ (c • A) = c • FiberEmbed j₀ A := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases h : a = j₀ ∧ b = j₀ <;> simp [fiberEmbed_apply, h]

omit [DecidableEq I] in

private theorem oaa_embed_sub (j₀ : J) (A B : Matrix I I ℂ) :
    FiberEmbed j₀ (A - B) = FiberEmbed j₀ A - FiberEmbed j₀ B := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases h : a = j₀ ∧ b = j₀ <;> simp [fiberEmbed_apply, h]

private theorem oaa_nat_matrix_mul (n : ℕ) (A : Matrix I I ℂ) :
    (n : Matrix I I ℂ) * A = (n : ℂ) • A := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem projected_obliviousAmplitudeAmplification_blockEncoding
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ) (s : ℝ)
    (hW : IsBlockEncoding W j₀ U s) :
    FiberProjector j₀ * ObliviousAmplitudeAmplification (FiberProjector j₀) W *
      FiberProjector j₀ =
      FiberEmbed j₀ ((((3 / s : ℝ) : ℂ) • U) -
        (((4 / s ^ 3 : ℝ) : ℂ) • (U * Uᴴ * U))) := by
  let C : Matrix I I ℂ := ((s⁻¹ : ℝ) : ℂ) • U
  have hblock : FiberProjector j₀ * W * FiberProjector j₀ = FiberEmbed j₀ C := by
    rw [Matrix.mul_assoc, fiberProjector_mul_mul_corner, hW.2.2]
  have h := projected_obliviousAmplitudeAmplification (FiberProjector j₀) W
    (isOrthogonalProjector_fiberProjector j₀) hW.1
  have h3 (A : Matrix (J × I) (J × I) ℂ) : 3 * A = (3 : ℂ) • A := by
    simpa using oaa_nat_matrix_mul 3 A
  have h4 (A : Matrix (J × I) (J × I) ℂ) : 4 * A = (4 : ℂ) • A := by
    simpa using oaa_nat_matrix_mul 4 A
  rw [hblock, Matrix.star_eq_conjTranspose, fiberEmbed_conjTranspose,
    fiberEmbed_mul, fiberEmbed_mul, h3, h4,
    ← oaa_embed_smul, ← oaa_embed_smul, ← oaa_embed_sub] at h
  have hpoly : (3 : ℂ) • C - (4 : ℂ) • (C * Cᴴ * C) =
      (((3 / s : ℝ) : ℂ) • U) - (((4 / s ^ 3 : ℝ) : ℂ) • (U * Uᴴ * U)) := by
    dsimp [C]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
      star_trivial, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_ofNat, div_eq_mul_inv]
    ring
  rw [hpoly] at h
  exact h

theorem unitary_preserves_projector_of_compressed_isometry
    (P U : Matrix I I ℂ) (hP : IsStarProjection P)
    (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (hblock : (P * U * P)ᴴ * (P * U * P) = P) :
    U * P = P * U * P := by
  apply sub_eq_zero.mp
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hPs : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hUU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  calc
    _ = P * (Uᴴ * U) * P - (P * U * P)ᴴ * (P * U * P) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPs,
        mul_sub, sub_mul]
      simp only [mul_assoc, ← mul_assoc P P, hPP]
      noncomm_ring
    _ = 0 := by rw [hUU, mul_one, hPP, hblock, sub_self]

end Qatlib.Concepts.CoherentSim.ResetDiscard
