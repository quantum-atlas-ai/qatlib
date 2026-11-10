/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.Polynomial.TensorGradient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QGradient20.DressedUpdate
variable {I : Type} [Fintype I]

def homogeneousInput (x : I → ℝ) : Option I → ℝ := fun i => i.elim 1 x

def squaredInput (x : I → ℝ) : ℝ := 1 + ∑ i, x i ^ 2

def normalizer (x : I → ℝ) : ℝ := (Real.sqrt (squaredInput x))⁻¹

theorem squaredInput_pos (x : I → ℝ) : 0 < squaredInput x := by
  have h : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold squaredInput
  linarith

theorem normalizer_pos (x : I → ℝ) : 0 < normalizer x :=
  inv_pos.mpr (Real.sqrt_pos.mpr (squaredInput_pos x))

theorem homogeneousInput_squared (x : I → ℝ) :
    (∑ i : Option I, homogeneousInput x i ^ 2) = squaredInput x := by
  simp [homogeneousInput, squaredInput]

theorem normalizer_squared (x : I → ℝ) : normalizer x ^ 2 * squaredInput x = 1 := by
  have h := Real.sq_sqrt (squaredInput_pos x).le
  rw [normalizer, inv_pow, h]
  exact inv_mul_cancel₀ (squaredInput_pos x).ne'

def dressed (x : I → ℝ) : Option I → ℝ := fun i => normalizer x * homogeneousInput x i

theorem dressed_squared (x : I → ℝ) : ∑ i, dressed x i ^ 2 = 1 := by
  simp only [dressed, mul_pow, ← Finset.mul_sum]
  rw [homogeneousInput_squared, normalizer_squared]

def encoded (x : I → ℝ) : EuclideanSpace ℂ (Option I) := WithLp.toLp 2 (fun i => (dressed x i : ℂ))

theorem encoded_none (x : I → ℝ) : encoded x none = (normalizer x : ℂ) := by
  simp [encoded, dressed, homogeneousInput]

theorem encoded_some (x : I → ℝ) (i : I) : encoded x (some i) = (normalizer x * x i : ℝ) := by
  simp [encoded, dressed, homogeneousInput]

theorem encoded_norm (x : I → ℝ) : ‖encoded x‖ = 1 := by
  have he : ‖encoded x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [encoded, WithLp.ofLp_toLp, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        dressed_squared x
  nlinarith [norm_nonneg (encoded x)]

theorem encoded_decode (x : I → ℝ) (i : I) : encoded x (some i) / encoded x none = (x i : ℂ) := by
  rw [encoded_none, encoded_some, Complex.ofReal_mul]
  have hc : (normalizer x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normalizer_pos x).ne'
  field_simp

end Qatlib.Papers.QGradient20.DressedUpdate
