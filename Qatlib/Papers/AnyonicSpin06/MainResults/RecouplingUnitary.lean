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

/-!
# Root parameters and recoupling unitarity identities

This module defines the root parameter `rootOfUnity` and complex quantum integers, proving the
phase's finite-power identity and the reality of the quantum integers. It imports positivity of
the modified vertex factor and derives transpose or conjugate-transpose identities from stated
inverse relations, including the conversion from real orthogonality to unitarity
[KauffmanLomonaco2006].

## Main statements

* `modified_vertex_factor_pos`: provides positivity in the admissible range.
* `rootOfUnity_pow_four_mul`: establishes the `4 * r` power identity for positive `r`.
* `quantumInt_real`: proves conjugation invariance of the quantum integers.
* `orthogonal_real_unitary`: converts a real two-dimensional orthogonality identity into a
  unitarity identity.

## References

* [Kauffman and Lomonaco, 2006][KauffmanLomonaco2006]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AnyonicSpin06.MainResults.RecouplingUnitary

open Matrix

/-- The complex phase `exp (I * π / (2 * r))`. -/
def rootOfUnity (r : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ))

/-- The phase `rootOfUnity r` has complex norm one for every natural `r`. -/
theorem norm_rootOfUnity (r : ℕ) : ‖rootOfUnity r‖ = 1 := by
  unfold rootOfUnity
  rw [Complex.norm_exp]
  have h : (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ)).re
      = - ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h, Complex.ofReal_im]
  simp

/-- For `r ≥ 2` and `m + n + p ≤ r - 2`, the modified vertex factor is positive
[KauffmanLomonaco2006]. -/
theorem modified_vertex_factor_pos {r m n p : ℕ} (hr : 2 ≤ r) (h : m + n + p ≤ r - 2) :
    0 < Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity.vertexFactor r m n p :=
  Qatlib.Papers.AnyonicSpin06.MainResults.VertexPositivity.vertexFactor_pos hr h

/-- If `Mswap` equals the transpose of a real matrix `M` and `Mswap * M = 1`, then `Mᵀ * M = 1`. -/
theorem recoupling_orthogonal_of_transpose_inverse
    {N : Type*} [Fintype N] [DecidableEq N]
    (M Mswap : Matrix N N ℝ) (hT : Mᵀ = Mswap) (hinv : Mswap * M = 1) :
    Mᵀ * M = 1 := by
  rw [hT, hinv]

/-- A real recoupling matrix satisfies `Mᵀ * M = 1` when its transpose equals the specified left
inverse `Mswap` [KauffmanLomonaco2006]. -/
theorem recoupling_real_orthogonal
    {N : Type*} [Fintype N] [DecidableEq N]
    (M Mswap : Matrix N N ℝ) (hT : Mᵀ = Mswap) (hinv : Mswap * M = 1) :
    Mᵀ * M = 1 :=
  recoupling_orthogonal_of_transpose_inverse M Mswap hT hinv

/-- A complex matrix with real entries satisfies `Mᴴ * M = 1` when its conjugate transpose
equals a specified left inverse `Mswap`. -/
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

/-- For `r ≥ 1`, the phase `rootOfUnity r` raised to `4 * r` equals one [KauffmanLomonaco2006]. -/
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

/-- The complex conjugate of `rootOfUnity r` equals its inverse [KauffmanLomonaco2006]. -/
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

/-- The quantum integer given by the quotient of the differences between `rootOfUnity r ^ (2 *
n)` and its inverse, and between `rootOfUnity r ^ 2` and its inverse. -/
def quantumInt (r n : ℕ) : ℂ :=
  (rootOfUnity r ^ (2 * n) - (rootOfUnity r ^ (2 * n))⁻¹) /
    (rootOfUnity r ^ 2 - (rootOfUnity r ^ 2)⁻¹)

/-- Each complex quantum integer is fixed by conjugation [KauffmanLomonaco2006]. -/
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

/-- For a complex two-by-two matrix with real entries, the identity `Mᵀ * M = 1` implies `Mᴴ * M
= 1` [KauffmanLomonaco2006]. -/
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
