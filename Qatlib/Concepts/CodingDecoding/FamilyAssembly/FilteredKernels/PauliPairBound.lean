/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels.Definitions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The check associated with a Hermitian involution is a self-adjoint projection. -/
theorem involutionCheck_isStarProjection (S : Matrix n n ℂ)
    (hS : S.IsHermitian) (hSS : S * S = 1) :
    IsStarProjection (involutionCheck S) := by
  constructor
  · change involutionCheck S * involutionCheck S = involutionCheck S
    simp only [involutionCheck, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hSS]
    module
  · exact ((Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian).sub hS).smul
      (IsSelfAdjoint.all (1 / 2 : ℝ))

/-- For anticommuting Hermitian involutions, the sum of their checks minus
`anticommutingPairGap` times the identity is a positive scalar multiple of the Gram matrix
of `anticommutingPairGram`. -/
theorem anticommutingPair_gram_identity
    (S T : Matrix n n ℂ)
    (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hSS : S * S = 1) (hTT : T * T = 1)
    (hAnti : S * T + T * S = 0) :
    involutionCheck S + involutionCheck T -
        anticommutingPairGap • (1 : Matrix n n ℂ) =
      (Real.sqrt 2 / 8 : ℝ) •
        ((anticommutingPairGram S T)ᴴ *
          anticommutingPairGram S T) := by
  let q : ℝ := Real.sqrt 2
  let A : Matrix n n ℂ := S + T
  let B : Matrix n n ℂ := anticommutingPairGram S T
  have hq : q * q = 2 := by
    dsimp [q]
    exact Real.mul_self_sqrt (by norm_num)
  have hA : A * A = (2 : ℝ) • (1 : Matrix n n ℂ) := by
    change (S + T) * (S + T) = _
    calc
      (S + T) * (S + T) =
          (S * S + T * T) + (S * T + T * S) := by
        simp only [Matrix.add_mul, Matrix.mul_add]
        module
      _ = (1 : Matrix n n ℂ) + 1 + 0 := by
        rw [hSS, hTT, hAnti]
      _ = (2 : ℝ) • (1 : Matrix n n ℂ) := by
        simp only [two_smul, add_zero]
  have hBH : B.IsHermitian := by
    dsimp [B, anticommutingPairGram]
    exact (((Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian).smul
      (IsSelfAdjoint.all (Real.sqrt 2))).sub hS).sub hT
  have hBeq : B = q • (1 : Matrix n n ℂ) - A := by
    dsimp [B, A, q, anticommutingPairGram]
    module
  have hBsq :
      Bᴴ * B = (4 : ℝ) • (1 : Matrix n n ℂ) - (2 * q) • A := by
    calc
      Bᴴ * B = (2 + q * q) • (1 : Matrix n n ℂ) - (2 * q) • A := by
        rw [hBH.eq]
        simp only [hBeq, Matrix.sub_mul, Matrix.mul_sub,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hA]
        module
      _ = (4 : ℝ) • (1 : Matrix n n ℂ) - (2 * q) • A := by
        rw [hq]
        norm_num
  have hcI : q / 8 * 4 = q / 2 := by ring
  have hcA : q / 8 * (2 * q) = (1 / 2 : ℝ) := by
    calc
      q / 8 * (2 * q) = (q * q) / 4 := by ring
      _ = 1 / 2 := by rw [hq]; norm_num
  change involutionCheck S + involutionCheck T -
      anticommutingPairGap • (1 : Matrix n n ℂ) =
    (q / 8 : ℝ) • (Bᴴ * B)
  calc
    involutionCheck S + involutionCheck T -
        anticommutingPairGap • (1 : Matrix n n ℂ) =
      (q / 2) • (1 : Matrix n n ℂ) - (1 / 2 : ℝ) • A := by
        dsimp [involutionCheck, anticommutingPairGap, A, q]
        module
    _ = (q / 8 : ℝ) • (Bᴴ * B) := by
      simp only [hBsq, smul_sub, smul_smul, hcI, hcA]

/-- For anticommuting Hermitian involutions, the sum of their checks minus
`anticommutingPairGap` times the identity is positive semidefinite. -/
theorem anticommutingPair_posSemidef
    (S T : Matrix n n ℂ)
    (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hSS : S * S = 1) (hTT : T * T = 1)
    (hAnti : S * T + T * S = 0) :
    (involutionCheck S + involutionCheck T -
      anticommutingPairGap • (1 : Matrix n n ℂ)).PosSemidef := by
  rw [anticommutingPair_gram_identity S T hS hT hSS hTT hAnti]
  exact (Matrix.posSemidef_conjTranspose_mul_self
    (anticommutingPairGram S T)).smul
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num))

/-- The total check energy of two anticommuting Hermitian involutions is at least
`anticommutingPairGap` in every positive semidefinite state of trace one. -/
theorem anticommutingPair_traceEnergy_lower
    (S T ρ : Matrix n n ℂ)
    (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hSS : S * S = 1) (hTT : T * T = 1)
    (hAnti : S * T + T * S = 0)
    (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ = 1) :
    anticommutingPairGap ≤
      traceEnergy (involutionCheck S) ρ +
      traceEnergy (involutionCheck T) ρ := by
  let B : Matrix n n ℂ := anticommutingPairGram S T
  have hRe : 0 ≤ (Matrix.trace (Bᴴ * B * ρ)).re := by
    have ht : 0 ≤ Matrix.trace (B * ρ * Bᴴ) :=
      (hρ.mul_mul_conjTranspose_same B).trace_nonneg
    rw [Matrix.trace_mul_cycle B ρ Bᴴ] at ht
    exact (Complex.nonneg_iff.mp ht).1
  have hNonneg :
      0 ≤ traceEnergy
        (involutionCheck S + involutionCheck T -
          anticommutingPairGap • (1 : Matrix n n ℂ)) ρ := by
    unfold traceEnergy
    rw [anticommutingPair_gram_identity S T hS hT hSS hTT hAnti]
    simp only [Matrix.smul_mul, Matrix.trace_smul,
      Complex.smul_re, smul_eq_mul]
    exact mul_nonneg
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hRe
  have hEnergy :
      traceEnergy
        (involutionCheck S + involutionCheck T -
          anticommutingPairGap • (1 : Matrix n n ℂ)) ρ =
      traceEnergy (involutionCheck S) ρ +
        traceEnergy (involutionCheck T) ρ - anticommutingPairGap := by
    simp only [traceEnergy, Matrix.sub_mul, Matrix.add_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
      Matrix.trace_add, Matrix.trace_smul, Complex.sub_re,
      Complex.add_re, Complex.smul_re, htr, Complex.one_re,
      smul_eq_mul, mul_one]
  rw [hEnergy] at hNonneg
  exact sub_nonneg.mp hNonneg

end Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels
