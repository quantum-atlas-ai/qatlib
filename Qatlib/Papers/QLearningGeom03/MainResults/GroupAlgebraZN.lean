/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Papers.QLearningGeom03.MainResults.GroupAlgebra

/-!
# Fourier diagonalization of cyclic group algebras

This module defines the cyclic character pairing `chiN` and normalized Fourier matrix `fourier`.
Character orthogonality gives unitarity, and Fourier conjugation diagonalizes `groupAlgebraElem`
with eigenvalues given by the Fourier coefficients of its first column.

These statements provide the cyclic group-algebra description in Proposition 5.2 of
[HunzikerEtAl2003].

## Main statements

* `fourier_mul_conjTranspose`: Unitarity of the cyclic Fourier matrix.
* `fourier_conj_groupAlgebraElem`: Diagonalization of cyclic group-algebra matrices.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {N : ℕ} [NeZero N]

/-- The standard additive character of `ZMod N` evaluated at the product of the two arguments. -/
noncomputable def chiN (j k : ZMod N) : ℂ := ZMod.stdAddChar (N := N) (j * k)

/-- The cyclic character pairing sends addition in its first argument to multiplication. -/
lemma chiN_add_left (j j' k : ZMod N) : chiN (j + j') k = chiN j k * chiN j' k := by
  unfold chiN
  rw [add_mul, AddChar.map_add_eq_mul]

/-- The cyclic character pairing sends addition in its second argument to multiplication. -/
lemma chiN_add_right (j k k' : ZMod N) : chiN j (k + k') = chiN j k * chiN j k' := by
  unfold chiN
  rw [mul_add, AddChar.map_add_eq_mul]

/-- The cyclic character pairing equals 1 when its second argument is zero. -/
lemma chiN_zero_right (j : ZMod N) : chiN j 0 = 1 := by
  unfold chiN
  rw [mul_zero, AddChar.map_zero_eq_one]

/-- Complex conjugation of the standard cyclic additive character corresponds to negating its
argument. -/
lemma stdAddChar_star (a : ZMod N) :
    star (ZMod.stdAddChar (N := N) a) = ZMod.stdAddChar (N := N) (-a) := by
  have hR : 0 < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne N)
  have h := AddChar.starComp_eq_inv (R := ZMod N) hR (φ := ZMod.stdAddChar (N := N))
  have h' := DFunLike.congr_fun h a
  simp only [AddChar.inv_apply] at h'
  simpa using h'

/-- Multiplying a cyclic character by the conjugate of another gives the character of the
frequency difference. -/
lemma chiN_mul_star (j k x : ZMod N) : chiN j x * star (chiN k x) = chiN x (j - k) := by
  unfold chiN
  rw [stdAddChar_star, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The sum of `chiN x b` over all residues is the group cardinality for b = 0 and zero
otherwise. -/
lemma chiN_sum (b : ZMod N) : ∑ x : ZMod N, chiN x b
    = ((if b = 0 then Fintype.card (ZMod N) else 0 : ℕ) : ℂ) := by
  unfold chiN
  exact AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)

omit [NeZero N] in

/-- For positive N, the square of the complex embedding of 1/√N, multiplied by N, is 1. -/
lemma sqrt_inv_mul_self (hN : 0 < N) :
    (((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹) * ((N : ℕ) : ℂ) = 1 := by
  have h2 : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = ((N : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hN.le)]
    norm_num
  have hc2 : (((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹)
      = (((N : ℕ) : ℂ))⁻¹ := by
    rw [← mul_inv, h2]
  rw [hc2, inv_mul_cancel₀]
  exact_mod_cast Nat.pos_iff_ne_zero.mp hN

/-- The normalized cyclic Fourier matrix with entries `chiN j k` divided by √N. -/
noncomputable def fourier (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun j k => (((Real.sqrt N : ℝ) : ℂ)⁻¹) * chiN j k

/-- The Fourier matrix intertwines a cyclic shift with the diagonal matrix of its character
values. -/
lemma fourier_mul_shift (g : ZMod N) :
    fourier N * shift g = Matrix.diagonal (fun j => chiN j g) * fourier N := by
  ext j z
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (z + g)]
  · rw [Matrix.diagonal_mul]
    unfold fourier shift
    rw [ite_eq_left rfl, mul_one, chiN_add_right]
    ring
  · intro w _ hw
    unfold fourier shift
    rw [ite_eq_right hw, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- For positive N, the normalized cyclic Fourier matrix times its conjugate transpose is the
identity. -/
lemma fourier_mul_conjTranspose (hN : 0 < N) : fourier N * (fourier N)ᴴ = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : star ((((Real.sqrt N : ℝ) : ℂ)⁻¹)) = (((Real.sqrt N : ℝ) : ℂ)⁻¹) := by simp
  have hterm : ∀ x : ZMod N, fourier N j x * (fourier N)ᴴ x k
      = ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹)) * chiN x (j - k) := by
    intro x
    rw [Matrix.conjTranspose_apply]
    unfold fourier
    rw [star_mul, hstar]
    calc (((Real.sqrt N : ℝ) : ℂ)⁻¹) * chiN j x * (star (chiN k x) * (((Real.sqrt N : ℝ) : ℂ)⁻¹))
        = ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹))
          * (chiN j x * star (chiN k x)) := by ring
      _ = ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹))
          * chiN x (j - k) := by rw [chiN_mul_star]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  have hcard : Fintype.card (ZMod N) = N := ZMod.card N
  rw [show (∑ x : ZMod N, chiN x (j - k))
      = ((if j - k = 0 then N else 0 : ℕ) : ℂ) from by
    rw [chiN_sum]
    rw [hcard]]
  by_cases hjk : j - k = 0
  · have hjk' : j = k := sub_eq_zero.mp hjk
    rw [ite_eq_left hjk, ite_eq_left hjk', sqrt_inv_mul_self hN]
  · have hjk' : j ≠ k := fun hcontra => hjk (by rw [hcontra]; abel)
    rw [ite_eq_right hjk, ite_eq_right hjk']
    simp

/-- The first column of `groupAlgebraElem v` is `v`, as in [Hunziker et al., Proposition
5.2][HunzikerEtAl2003]. -/
lemma cyclic_first_column (v : ZMod N → ℂ) (j : ZMod N) :
    groupAlgebraElem v j 0 = v j := by
  rw [groupAlgebraElem_apply, sub_zero]

/-- Every diagonal entry of a cyclic group-algebra matrix is `v 0`, as in [Hunziker et al.,
Proposition 5.2][HunzikerEtAl2003]. -/
lemma cyclic_diag (v : ZMod N → ℂ) (j : ZMod N) :
    groupAlgebraElem v j j = v 0 := by
  rw [groupAlgebraElem_apply, sub_self]

/-- Fourier conjugation diagonalizes a cyclic group-algebra matrix with diagonal entries ∑ x,
v(x)χ(j, x). This is the spectral description in [Hunziker et al., Proposition
5.2][HunzikerEtAl2003]. -/
theorem fourier_conj_groupAlgebraElem (hN : 0 < N) (v : ZMod N → ℂ) :
    fourier N * groupAlgebraElem v * (fourier N)ᴴ
      = Matrix.diagonal (fun j => ∑ x, v x * chiN j x) := by
  rw [groupAlgebraElem, Finset.mul_sum, Finset.sum_mul]
  have hdiag : (∑ x : ZMod N, v x • Matrix.diagonal (fun j => chiN j x))
      = Matrix.diagonal (fun j => ∑ x, v x * chiN j x) := by
    ext j k
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hjk : j = k
    · rw [ite_eq_left hjk]
      rw [Finset.sum_congr rfl (fun x _ => by
        rw [Matrix.smul_apply, Matrix.diagonal_apply, ite_eq_left hjk, smul_eq_mul])]
    · rw [ite_eq_right hjk]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Matrix.smul_apply, Matrix.diagonal_apply, ite_eq_right hjk, smul_zero]
  refine Eq.trans ?_ hdiag
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, fourier_mul_shift, Matrix.mul_assoc,
    fourier_mul_conjTranspose hN, Matrix.mul_one]

end Qatlib.Papers.QLearningGeom03.MainResults
