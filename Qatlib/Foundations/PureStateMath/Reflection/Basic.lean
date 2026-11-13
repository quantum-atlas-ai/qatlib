/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Diffusion and two-amplitude states

This module defines `AverageProjection`, Grover diffusion `Diffusion`, and states `MarkedVector`
with constant amplitudes on marked and unmarked outcomes. It proves the reflection formula for
diffusion and computes the normalization and measurement weights of these states, as used in
quantum search [Grover1996].

## Main statements

* `diffusion_unitary`: diffusion is unitary for a nonempty finite basis.
* `diffusion_eq_hadamardN_zeroPhaseReflection`: realize register diffusion by Hadamard
  conjugation.
* `normalized_markedVector_iff`: characterize normalization by two amplitudes.

## References

* [Grover, 1996][Grover1996]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.PureStateMath.Reflection

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The constant matrix with every entry equal to the reciprocal of the basis cardinality. -/
noncomputable def AverageProjection (I : Type*) [Fintype I] : Matrix I I ℂ :=
  Matrix.of fun _ _ => (Fintype.card I : ℂ)⁻¹

omit [DecidableEq I] in

/-- For a basis of positive cardinality, the averaging matrix is idempotent. -/
theorem averageProjection_mul_self (hN : 0 < Fintype.card I) :
    AverageProjection I * AverageProjection I = AverageProjection I := by
  have hc : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  ext i j
  simp only [AverageProjection, Matrix.mul_apply, Matrix.of_apply, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

omit [DecidableEq I] in

/-- Applying the averaging matrix replaces every amplitude by the arithmetic mean of all
amplitudes. -/
theorem applyGate_averageProjection (ψ : QState I) (i : I) :
    ApplyGate (AverageProjection I) ψ i = (∑ j, ψ j) / (Fintype.card I : ℂ) := by
  simp only [ApplyGate, AverageProjection, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

/-- The diffusion matrix `2 * AverageProjection I - 1` implementing reflection about the mean. -/
noncomputable def Diffusion (I : Type*) [Fintype I] [DecidableEq I] : Matrix I I ℂ :=
  (2 : ℂ) • AverageProjection I - 1

/-- For a basis of positive cardinality, the diffusion matrix squares to the identity. -/
theorem diffusion_mul_self (hN : 0 < Fintype.card I) : Diffusion I * Diffusion I = 1 := by
  have hP := averageProjection_mul_self (I := I) hN
  simp only [Diffusion, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hP]
  module

/-- The diffusion matrix equals its conjugate transpose. -/
theorem diffusion_conjTranspose : (Diffusion I)ᴴ = Diffusion I := by
  ext i j
  simp [Diffusion, AverageProjection, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

/-- For a basis of positive cardinality, the diffusion matrix is unitary. -/
theorem diffusion_unitary (hN : 0 < Fintype.card I) : Diffusion I ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, diffusion_conjTranspose]
  exact diffusion_mul_self hN

/-- Diffusion sends each amplitude to twice the mean amplitude minus its original value. -/
theorem applyGate_diffusion (ψ : QState I) (i : I) :
    ApplyGate (Diffusion I) ψ i = -ψ i + 2 * ((∑ j, ψ j) / (Fintype.card I : ℂ)) := by
  have hp := applyGate_averageProjection ψ i
  change ((2 : ℂ) • AverageProjection I - 1).mulVec ψ i = _
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  change 2 * ApplyGate (AverageProjection I) ψ i - ψ i = _
  rw [hp]
  ring

/-- The diagonal register matrix that fixes the all-zero basis vector and negates all other
basis vectors. -/
noncomputable def ZeroPhaseReflection (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if x = ZeroStr n then 1 else -1

/-- Register diffusion is the conjugation of the all-zero phase reflection by the register
Hadamard transform. -/
theorem diffusion_eq_hadamardN_zeroPhaseReflection (n : ℕ) :
    Diffusion (Reg n) = HadamardN n * ZeroPhaseReflection n * HadamardN n := by
  classical
  let P0 : Matrix (Reg n) (Reg n) ℂ :=
    Matrix.diagonal fun x => if x = ZeroStr n then 1 else 0
  have hR : ZeroPhaseReflection n = (2 : ℂ) • P0 - 1 := by
    ext i j
    simp only [ZeroPhaseReflection, P0, Matrix.diagonal_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> ring
  have hsymm (i j : Reg n) : HadamardN n i j = HadamardN n j i := by
    simp [HadamardN, Hadamard, and_comm]
  have hHerm : (HadamardN n)ᴴ = HadamardN n := by
    ext i j
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, hadamardN_conj]
    exact hsymm j i
  have hWW : HadamardN n * HadamardN n = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp (hadamardN_unitary n)
    simpa only [Matrix.star_eq_conjTranspose, hHerm] using h
  have hP : HadamardN n * P0 * HadamardN n = AverageProjection (Reg n) := by
    change (HadamardN n * Matrix.diagonal (fun x => if x = ZeroStr n then (1 : ℂ) else 0)) *
      HadamardN n = _
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rw [Finset.sum_eq_single (ZeroStr n)]
    · simp only [ite_true, mul_one]
      rw [hadamardN_apply_zero_right, hadamardN_apply_zero_left, ← mul_pow,
        inv_sqrt2_mul_self]
      simp [AverageProjection]
    · intro x _ hx
      simp [hx]
    · simp
  rw [hR, mul_sub, sub_mul, mul_one, mul_smul_comm, smul_mul_assoc, hP, hWW]
  rfl

/-- The amplitude vector taking value `a` on the marked set `A` and value `b` elsewhere. -/
noncomputable def MarkedVector (A : Finset I) (a b : ℂ) : QState I :=
  fun i => if i ∈ A then a else b

omit [Fintype I] in

/-- Evaluate a two-amplitude marked vector by membership in the marked set. -/
theorem markedVector_apply (A : Finset I) (a b : ℂ) (i : I) :
    MarkedVector A a b i = if i ∈ A then a else b := rfl

/-- The sum of marked-vector amplitudes is the marked cardinality times `a` plus the
complementary cardinality times `b`. -/
theorem sum_markedVector (A : Finset I) (a b : ℂ) :
    (∑ i, MarkedVector A a b i) = (A.card : ℂ) * a + ((Fintype.card I : ℂ) - A.card) * b := by
  have hv (i : I) : MarkedVector A a b i = (if i ∈ A then a - b else 0) + b := by
    simp only [MarkedVector]
    split_ifs <;> ring
  simp_rw [hv]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The squared norm sum of a marked vector is the cardinality-weighted sum of the two squared
amplitude norms. -/
theorem sum_normSq_markedVector (A : Finset I) (a b : ℂ) :
    (∑ i, Complex.normSq (MarkedVector A a b i)) =
      (A.card : ℝ) * Complex.normSq a +
        ((Fintype.card I : ℝ) - A.card) * Complex.normSq b := by
  have hv (i : I) : Complex.normSq (MarkedVector A a b i) =
      (if i ∈ A then Complex.normSq a - Complex.normSq b else 0) + Complex.normSq b := by
    by_cases hi : i ∈ A <;> simp [MarkedVector, hi]
  simp_rw [hv]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- A marked vector is normalized exactly when its cardinality-weighted squared amplitude norms
sum to one. -/
theorem normalized_markedVector_iff (A : Finset I) (a b : ℂ) :
    Normalized (MarkedVector A a b) ↔
      (A.card : ℝ) * Complex.normSq a +
        ((Fintype.card I : ℝ) - A.card) * Complex.normSq b = 1 := by
  unfold Normalized
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [sum_normSq_markedVector]

omit [Fintype I] in

/-- The Born weight on the marked set is its cardinality times the squared norm of the marked
amplitude. -/
theorem measureProb_markedVector (A : Finset I) (a b : ℂ) :
    MeasureProb (MarkedVector A a b) A = (A.card : ℝ) * Complex.normSq a := by
  unfold MeasureProb
  calc
    _ = ∑ _i ∈ A, Complex.normSq a := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [BornProb, MarkedVector, hi, Complex.normSq_eq_norm_sq]
    _ = _ := by simp

/-- The uniform state is a marked vector with both amplitudes equal to the reciprocal square
root of the basis cardinality. -/
theorem uniform_eq_markedVector (A : Finset I) :
    Uniform I = MarkedVector A (Real.sqrt (Fintype.card I) : ℂ)⁻¹
      (Real.sqrt (Fintype.card I) : ℂ)⁻¹ := by
  funext i
  simp only [Uniform, MarkedVector]
  split_ifs <;> rfl

end Qatlib.Foundations.PureStateMath.Reflection
