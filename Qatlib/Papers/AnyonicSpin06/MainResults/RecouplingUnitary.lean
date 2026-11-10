/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AnyonicSpin06.MainResults.RecouplingUnitary

open Matrix

def rootOfUnity (r : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ))

theorem norm_rootOfUnity (r : ℕ) : ‖rootOfUnity r‖ = 1 := by
  unfold rootOfUnity
  rw [Complex.norm_exp]
  have h : (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ)).re
      = - ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h, Complex.ofReal_im]
  simp

theorem modified_vertex_factor_pos {r m n p : ℕ} (hr : 2 ≤ r) (h : m + n + p ≤ r - 2) :
    0 < Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity.vertexFactor r m n p :=
  Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity.vertexFactor_pos hr h

theorem recoupling_orthogonal_of_transpose_inverse
    {N : Type*} [Fintype N] [DecidableEq N]
    (M Mswap : Matrix N N ℝ) (hT : Mᵀ = Mswap) (hinv : Mswap * M = 1) :
    Mᵀ * M = 1 := by
  rw [hT, hinv]

theorem recoupling_real_orthogonal
    {N : Type*} [Fintype N] [DecidableEq N]
    (M Mswap : Matrix N N ℝ) (hT : Mᵀ = Mswap) (hinv : Mswap * M = 1) :
    Mᵀ * M = 1 :=
  recoupling_orthogonal_of_transpose_inverse M Mswap hT hinv

theorem recoupling_unitary
    {N : Type*} [Fintype N] [DecidableEq N]
    (M Mswap : Matrix N N ℂ) (hreal : ∀ i j, (M i j).im = 0)
    (hT : Mᴴ = Mswap) (hinv : Mswap * M = 1) :
    Mᴴ * M = 1 := by

  have htrans : Mᴴ = Mᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    apply Complex.ext <;> simp [hreal j i]
  rw [hT, hinv]

theorem rootOfUnity_pow_four_mul (r : ℕ) (hr : 1 ≤ r) :
    rootOfUnity r ^ (4 * r) = 1 := by
  unfold rootOfUnity
  rw [← Complex.exp_nat_mul]
  have h : (((4 * r : ℕ)) : ℂ) * (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ))
      = (2 : ℕ) * (Complex.I * ((Real.pi : ℝ) : ℂ)) := by
    have hr0 : (r : ℂ) ≠ 0 := by
      have : (r : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    push_cast
    field_simp
    ring
  rw [h, Complex.exp_nat_mul]
  have hpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    have hI : Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by ring
    rw [hI, Complex.exp_pi_mul_I]
  rw [hpi]
  norm_num

theorem star_rootOfUnity (r : ℕ) : star (rootOfUnity r) = (rootOfUnity r)⁻¹ := by
  have hnorm : ‖rootOfUnity r‖ = 1 := norm_rootOfUnity r
  have h : star (rootOfUnity r) * rootOfUnity r = 1 := by
    have h2 : star (rootOfUnity r) * rootOfUnity r
        = (Complex.normSq (rootOfUnity r) : ℂ) := by
      simpa [Complex.star_def] using
        (Complex.normSq_eq_conj_mul_self (z := rootOfUnity r)).symm
    rw [h2, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hz : rootOfUnity r ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  calc star (rootOfUnity r)
      = star (rootOfUnity r) * rootOfUnity r * (rootOfUnity r)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]
    _ = 1 * (rootOfUnity r)⁻¹ := by rw [h]
    _ = (rootOfUnity r)⁻¹ := one_mul _

def quantumInt (r n : ℕ) : ℂ :=
  (rootOfUnity r ^ (2 * n) - (rootOfUnity r ^ (2 * n))⁻¹) /
    (rootOfUnity r ^ 2 - (rootOfUnity r ^ 2)⁻¹)

theorem quantumInt_real (r n : ℕ) : star (quantumInt r n) = quantumInt r n := by
  unfold quantumInt
  have hstar_inv : ∀ z : ℂ, star (z⁻¹) = (star z)⁻¹ :=
    fun z => map_inv₀ (starRingEnd ℂ) z
  have hstar_div : ∀ z w : ℂ, star (z / w) = star z / star w :=
    fun z w => map_div₀ (starRingEnd ℂ) z w
  have h1 : star (rootOfUnity r ^ (2 * n)) = (rootOfUnity r ^ (2 * n))⁻¹ := by
    rw [star_pow, star_rootOfUnity, inv_pow]
  have h3 : star (rootOfUnity r ^ 2) = (rootOfUnity r ^ 2)⁻¹ := by
    rw [star_pow, star_rootOfUnity, inv_pow]
  rw [hstar_div, star_sub, star_sub, hstar_inv, hstar_inv, h1, h3, inv_inv, inv_inv]
  have hu : (rootOfUnity r ^ (2 * n))⁻¹ - rootOfUnity r ^ (2 * n)
      = -(rootOfUnity r ^ (2 * n) - (rootOfUnity r ^ (2 * n))⁻¹) := by ring
  have hv : (rootOfUnity r ^ 2)⁻¹ - rootOfUnity r ^ 2
      = -(rootOfUnity r ^ 2 - (rootOfUnity r ^ 2)⁻¹) := by ring
  rw [hu, hv, neg_div_neg_eq]

theorem orthogonal_real_unitary {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hreal : ∀ i j, (M i j).im = 0) (horth : Mᵀ * M = 1) :
    Mᴴ * M = 1 := by
  have htrans : Mᴴ = Mᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    apply Complex.ext <;> simp [hreal j i]
  rw [htrans]
  exact horth

end Qatlib.Papers.AnyonicSpin06.MainResults.RecouplingUnitary
