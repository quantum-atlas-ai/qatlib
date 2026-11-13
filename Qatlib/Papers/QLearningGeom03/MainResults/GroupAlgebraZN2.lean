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
# Hadamard diagonalization of binary group algebras

This module defines binary strings `Bits`, their character pairing `chi`, and the normalized
Walsh–Hadamard matrix `hadamard`. It proves character orthogonality, the involutivity of the
transform, and diagonalization of the group algebra of binary strings.

The first-column, symmetry, and spectral descriptions formalize the binary group-algebra setting
of Proposition 5.1 in [HunzikerEtAl2003].

## Main statements

* `hadamard_mul_self`: The Walsh–Hadamard transform is an involution.
* `groupAlgebraElem_symmetric`: Binary group-algebra matrices are symmetric.
* `hadamard_conj_groupAlgebraElem`: Hadamard diagonalization of binary group-algebra matrices.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

/-- The additive group of length-`n` binary strings, represented by functions from `Fin n` to
`ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The binary character pairing, defined as the product of the standard additive characters of
the coordinatewise products. -/
noncomputable def chi {n : ℕ} (y z : Bits n) : ℂ :=
  ∏ i, ZMod.stdAddChar (N := 2) (y i * z i)

/-- The binary character pairing sends addition in its second argument to multiplication. -/
lemma chi_add_right {n : ℕ} (y z w : Bits n) : chi y (z + w) = chi y z * chi y w := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    rw [Pi.add_apply, mul_add, AddChar.map_add_eq_mul]

/-- The binary character pairing is symmetric. -/
lemma chi_comm {n : ℕ} (y z : Bits n) : chi y z = chi z y := by
  unfold chi
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

/-- The product χ(y, x)χ(x, z) equals χ(y + z, x). -/
lemma chi_mul_chi {n : ℕ} (y z x : Bits n) : chi y x * chi x z = chi (y + z) x := by
  rw [chi_comm y x, ← chi_add_right x y z, chi_comm (y + z) x]

/-- The binary character pairing equals 1 when its first argument is zero. -/
lemma chi_zero_left {n : ℕ} (x : Bits n) : chi 0 x = 1 := by
  unfold chi
  simp

/-- The binary character pairing equals 1 when its second argument is zero. -/
lemma chi_zero_right {n : ℕ} (y : Bits n) : chi y 0 = 1 := by
  unfold chi
  simp

/-- The standard additive character of `ZMod 2` takes the value -1 at 1. -/
lemma stdAddChar_two_one : ZMod.stdAddChar (N := 2) (1 : ZMod 2) = -1 := by
  have h1 : (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) := by norm_num
  rw [h1, ZMod.stdAddChar_coe (N := 2) (1 : ℤ)]
  convert Complex.exp_pi_mul_I using 2
  push_cast
  ring

/-- The standard additive character of `ZMod 2` takes the value -1 at every nonzero element. -/
lemma stdAddChar_eq_neg_one {a : ZMod 2} (ha : a ≠ 0) :
    ZMod.stdAddChar (N := 2) a = -1 := by
  have hsq : (ZMod.stdAddChar (N := 2) a : ℂ) * ZMod.stdAddChar (N := 2) a = 1 := by
    rw [← AddChar.map_add_eq_mul]
    have h2 : a + a = 0 := by
      have hh : (2 : ZMod 2) = 0 := by decide
      rw [← two_mul, hh, zero_mul]
    rw [h2, AddChar.map_zero_eq_one]
  have hne : (ZMod.stdAddChar (N := 2) a : ℂ) ≠ 1 := by
    intro h
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := 2))] at h
    exact ha (ZMod.injective_stdAddChar (N := 2) h)
  have hsq' : (ZMod.stdAddChar (N := 2) a : ℂ) ^ 2 = 1 := by
    rw [pow_two]; exact hsq
  rcases sq_eq_one_iff.mp hsq' with h | h
  · exact absurd h hne
  · exact h

/-- A nontrivial binary character sums to zero over all binary strings. -/
lemma chi_sum_eq_zero {n : ℕ} {u : Bits n} (hu : u ≠ 0) : ∑ x, chi u x = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    refine hu (funext fun i => ?_)
    by_contra hi
    exact h ⟨i, hi⟩
  let δ : Bits n := Pi.single i₀ 1
  have hchiδ : chi u δ = -1 := by
    unfold chi
    rw [Finset.prod_eq_single i₀]
    · rw [show δ i₀ = 1 by simp [δ], mul_one]
      exact stdAddChar_eq_neg_one hi₀
    · intro i _ hne
      rw [show δ i = 0 by simp [δ, hne], mul_zero, AddChar.map_zero_eq_one]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  have hflip (x : Bits n) : chi u (x + δ) = -chi u x := by
    rw [chi_add_right, hchiδ, mul_neg, mul_one]
  have hshift : (∑ x : Bits n, chi u (x + δ)) = ∑ x : Bits n, chi u x := by
    refine Finset.sum_bij (fun x _ => x + δ) (fun x _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a _ b _ hab
      exact add_right_cancel hab
    · intro b _
      exact ⟨b - δ, Finset.mem_univ _, by abel⟩
    · intro a _
      rfl
  have hneg : (∑ x : Bits n, chi u (x + δ)) = -∑ x : Bits n, chi u x := by
    rw [Finset.sum_congr rfl (fun x _ => hflip x), Finset.sum_neg_distrib]
  have hS : (∑ x : Bits n, chi u x) = -∑ x : Bits n, chi u x := by
    calc (∑ x : Bits n, chi u x) = ∑ x : Bits n, chi u (x + δ) := hshift.symm
      _ = -∑ x : Bits n, chi u x := hneg
  have hzero : (∑ x : Bits n, chi u x) + (∑ x : Bits n, chi u x) = 0 := by
    nth_rewrite 1 [hS]
    abel
  have h2 : (2 : ℂ) * (∑ x : Bits n, chi u x) = 0 := by
    rw [two_mul]; exact hzero
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- There are 2^n binary strings of length n. -/
lemma card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- The normalized Walsh–Hadamard matrix, with entries 2^(-n/2) times the binary character
pairing. -/
noncomputable def hadamard (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  fun y z => (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * chi y z

/-- The square of the n-th power of 1/√2, multiplied by 2^n, is 1 in the complex numbers. -/
lemma sqrt_inv_pow_mul_self (n : ℕ) :
    ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n) * ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n)
      * ((2 ^ n : ℕ) : ℂ) = 1 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc2 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((2 : ℂ))⁻¹ := by
    rw [← mul_inv, h2]
  calc ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n) * ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n)
        * ((2 ^ n : ℕ) : ℂ)
      = ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)) ^ n
        * (((2 : ℂ)) ^ n) := by
        rw [← mul_pow]
        push_cast
        ring
    _ = (((2 : ℂ))⁻¹) ^ n * (((2 : ℂ)) ^ n) := by rw [hc2]
    _ = (((2 : ℂ))⁻¹ * (2 : ℂ)) ^ n := by rw [← mul_pow]
    _ = 1 := by rw [inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_pow]

/-- The Hadamard matrix intertwines a binary shift with the diagonal matrix of its character
values. -/
lemma hadamard_mul_shift {n : ℕ} (g : Bits n) :
    hadamard n * shift g = Matrix.diagonal (fun y => chi y g) * hadamard n := by
  ext y z
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (z + g)]
  · rw [Matrix.diagonal_mul]
    unfold hadamard shift
    rw [ite_eq_left rfl, mul_one, chi_add_right]
    ring
  · intro w _ hw
    unfold hadamard shift
    rw [ite_eq_right hw, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The normalized Walsh–Hadamard matrix squares to the identity. -/
lemma hadamard_mul_self {n : ℕ} : hadamard n * hadamard n = 1 := by
  ext y z
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ x : Bits n, hadamard n y x * hadamard n x z
      = ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n) * chi (y + z) x := by
    intro x
    calc hadamard n y x * hadamard n x z
        = ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n)
            * (chi y x * chi x z) := by
          unfold hadamard
          ring
      _ = ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n)
            * chi (y + z) x := by rw [chi_mul_chi]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  have hsum : (∑ x : Bits n, chi (y + z) x)
      = if y + z = 0 then ((2 ^ n : ℕ) : ℂ) else 0 := by
    by_cases h : y + z = 0
    · rw [ite_eq_left h]
      have hone : ∀ x : Bits n, chi (y + z) x = 1 := fun x => by rw [h]; exact chi_zero_left x
      rw [Finset.sum_congr rfl (fun x _ => hone x), Finset.sum_const, Finset.card_univ,
        card_bits]
      simp
    · rw [ite_eq_right h, chi_sum_eq_zero h]
  rw [hsum]
  by_cases h : y + z = 0
  · have hyz : y = z := by
      funext i
      have hi : y i + z i = 0 := by simpa using congrFun h i
      have h2 : z i + z i = 0 := by
        have hh : (2 : ZMod 2) = 0 := by decide
        rw [← two_mul, hh, zero_mul]
      calc y i = y i + (z i + z i) := by rw [h2, add_zero]
        _ = y i + z i + z i := by rw [add_assoc]
        _ = z i := by rw [hi, zero_add]
    rw [ite_eq_left h, ite_eq_left hyz, sqrt_inv_pow_mul_self]
  · have hyz : y ≠ z := by
      intro hcontra
      apply h
      rw [hcontra]
      funext i
      have hh : (2 : ZMod 2) = 0 := by decide
      show z i + z i = 0
      rw [← two_mul, hh, zero_mul]
    rw [ite_eq_right h, ite_eq_right hyz, mul_zero]

/-- Every binary string added to itself is zero. -/
lemma bits_add_self {n : ℕ} (g : Bits n) : g + g = 0 := by
  funext i
  have hh : (2 : ZMod 2) = 0 := by decide
  show g i + g i = 0
  rw [← two_mul, hh, zero_mul]

/-- Every translation matrix on binary strings is symmetric. -/
lemma shift_transpose {n : ℕ} (g : Bits n) : (shift g)ᵀ = shift g := by
  ext y z
  rw [Matrix.transpose_apply]
  unfold shift
  by_cases h : y = z + g
  · rw [ite_eq_left h, ite_eq_left (show z = y + g by rw [h, add_assoc, bits_add_self, add_zero])]
  · rw [ite_eq_right h, ite_eq_right]
    intro hcon
    exact h (by rw [hcon, add_assoc, bits_add_self, add_zero])

/-- The first column of a binary group-algebra matrix is its coefficient vector, as in [Hunziker
et al., Proposition 5.1][HunzikerEtAl2003]. -/
lemma groupAlgebraElem_first_column {n : ℕ} (v : Bits n → ℂ) (y : Bits n) :
    groupAlgebraElem v y 0 = v y := by
  rw [groupAlgebraElem_apply, sub_zero]

/-- Every complex group-algebra matrix on binary strings equals its transpose, as in [Hunziker
et al., Proposition 5.1][HunzikerEtAl2003]. -/
lemma groupAlgebraElem_symmetric {n : ℕ} (v : Bits n → ℂ) :
    (groupAlgebraElem v)ᵀ = groupAlgebraElem v := by
  rw [groupAlgebraElem, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [Matrix.transpose_smul, shift_transpose]

/-- Every diagonal entry of a binary group-algebra matrix equals the coefficient at zero, as in
[Hunziker et al., Proposition 5.1][HunzikerEtAl2003]. -/
lemma groupAlgebraElem_diag {n : ℕ} (v : Bits n → ℂ) (y : Bits n) :
    groupAlgebraElem v y y = v 0 := by
  rw [groupAlgebraElem_apply, sub_self]

/-- Hadamard conjugation diagonalizes a binary group-algebra matrix with diagonal entries given
by its character sums, as in [Hunziker et al., Proposition 5.1][HunzikerEtAl2003]. -/
theorem hadamard_conj_groupAlgebraElem {n : ℕ} (v : Bits n → ℂ) :
    hadamard n * groupAlgebraElem v * hadamard n
      = Matrix.diagonal (fun y => ∑ x, v x * chi y x) := by
  rw [groupAlgebraElem, Finset.mul_sum, Finset.sum_mul]
  have hdiag : (∑ x : Bits n, v x • Matrix.diagonal (fun y => chi y x))
      = Matrix.diagonal (fun y => ∑ x, v x * chi y x) := by
    ext y z
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hyz : y = z
    · rw [ite_eq_left hyz]
      rw [Finset.sum_congr rfl (fun x _ => by
        rw [Matrix.smul_apply, Matrix.diagonal_apply, ite_eq_left hyz, smul_eq_mul])]
    · rw [ite_eq_right hyz]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Matrix.smul_apply, Matrix.diagonal_apply, ite_eq_right hyz, smul_zero]
  refine Eq.trans ?_ hdiag
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, hadamard_mul_shift, Matrix.mul_assoc,
    hadamard_mul_self, Matrix.mul_one]

end Qatlib.Papers.QLearningGeom03.MainResults
