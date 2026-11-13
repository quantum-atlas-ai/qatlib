/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.FermionEdge.Defs

/-!
# Relations of fermionic edge generators

This module proves Hermitian, involution, and commutation relations for the fermionic edge
generators. Majorana anticommutation and four-factor rearrangements yield commutation for
disjoint supports and anticommutation for a shared endpoint. See [SetiaWhitfield2018].

## Main statements

* `edgeB_sq`: vertex generators square to the identity.
* `edgeA_sq`: edge generators with distinct endpoints square to the identity.
* `edgeA_commute_disjoint`: disjoint edge generators commute.
* `edgeA_anticommute_shared`: edges sharing one endpoint anticommute.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BKFermion17.FermionEdge

open Matrix
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BKFermion17.FermionEdge

section Swap

variable {R : Type*} [Ring R]

/-- Swap the first two factors of a four-factor product and negate the result when those factors
anticommute. -/
theorem swap12 (a b c d : R) (h : a * b = -(b * a)) :
    a * b * c * d = -(b * a * c * d) := by
  rw [show a * b * c * d = (a * b) * (c * d) by noncomm_ring, h]
  noncomm_ring

/-- Swap the middle two factors of a four-factor product and negate the result when those
factors anticommute. -/
theorem swap23 (a b c d : R) (h : b * c = -(c * b)) :
    a * b * c * d = -(a * c * b * d) := by
  rw [show a * b * c * d = a * (b * c) * d by noncomm_ring, h]
  noncomm_ring

/-- Swap the last two factors of a four-factor product and negate the result when those factors
anticommute. -/
theorem swap34 (a b c d : R) (h : c * d = -(d * c)) :
    a * b * c * d = -(a * b * d * c) := by
  rw [show a * b * c * d = (a * b) * (c * d) by noncomm_ring, h]
  noncomm_ring

end Swap

/-- The even and odd Majorana operators at one mode anticommute, in even-odd order. -/
theorem even_odd_same_neg {n : ℕ} (k : Fin n) :
    majoranaEven k * majoranaOdd k = -(majoranaOdd k * majoranaEven k) :=
  eq_neg_of_add_eq_zero_left (majoranaEven_majoranaOdd_anticommute_same n k)

/-- The odd and even Majorana operators at one mode anticommute, in odd-even order. -/
theorem odd_even_same_neg {n : ℕ} (k : Fin n) :
    majoranaOdd k * majoranaEven k = -(majoranaEven k * majoranaOdd k) := by
  have h : majoranaOdd k * majoranaEven k + majoranaEven k * majoranaOdd k = 0 := by
    rw [add_comm]
    exact majoranaEven_majoranaOdd_anticommute_same n k
  exact eq_neg_of_add_eq_zero_left h

/-- Even Majorana operators at distinct modes anticommute. -/
theorem even_even_neg {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    majoranaEven k * majoranaEven l = -(majoranaEven l * majoranaEven k) :=
  eq_neg_of_add_eq_zero_left (majoranaEven_anticommute n k l hkl)

/-- Odd Majorana operators at distinct modes anticommute. -/
theorem odd_odd_neg {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    majoranaOdd k * majoranaOdd l = -(majoranaOdd l * majoranaOdd k) :=
  eq_neg_of_add_eq_zero_left (majoranaOdd_anticommute k l hkl)

/-- An even Majorana operator and an odd Majorana operator at distinct modes anticommute. -/
theorem even_odd_neg {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    majoranaEven k * majoranaOdd l = -(majoranaOdd l * majoranaEven k) :=
  eq_neg_of_add_eq_zero_left (majoranaEven_majoranaOdd_anticommute k l hkl)

/-- An odd Majorana operator and an even Majorana operator at distinct modes anticommute. -/
theorem odd_even_neg {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    majoranaOdd k * majoranaEven l = -(majoranaEven l * majoranaOdd k) := by
  have h : majoranaOdd k * majoranaEven l + majoranaEven l * majoranaOdd k = 0 := by
    rw [add_comm]
    exact majoranaEven_majoranaOdd_anticommute l k (Ne.symm hkl)
  exact eq_neg_of_add_eq_zero_left h

/-- Each even Majorana operator is Hermitian. -/
theorem majoranaEven_herm {n : ℕ} (k : Fin n) : (majoranaEven k)ᴴ = majoranaEven k := by
  unfold majoranaEven
  rw [Matrix.conjTranspose_add, ← annihilation_eq_creation_conjTranspose,
    ← creation_eq_annihilation_conjTranspose, add_comm]

/-- Each odd Majorana operator is Hermitian. -/
theorem majoranaOdd_herm {n : ℕ} (k : Fin n) : (majoranaOdd k)ᴴ = majoranaOdd k := by
  unfold majoranaOdd
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    ← annihilation_eq_creation_conjTranspose, ← creation_eq_annihilation_conjTranspose]
  have hI : star (Complex.I : ℂ) = -Complex.I := by simp
  rw [hI]
  calc (-Complex.I) • (creation k - annihilation k)
      = -(Complex.I • (creation k - annihilation k)) := by rw [neg_smul]
    _ = Complex.I • (-(creation k - annihilation k)) := by rw [smul_neg]
    _ = Complex.I • (annihilation k - creation k) := by rw [neg_sub]

/-- The product of two scalar multiples of matrices equals the product of the scalars times the
ordered matrix product. -/
theorem smul_mul_smul_eq {n : ℕ} (c d : ℂ) (X Y : Matrix (Reg n) (Reg n) ℂ) :
    (c • X) * (d • Y) = (c * d) • (X * Y) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Each vertex generator `edgeB i` is Hermitian. -/
theorem edgeB_herm {n : ℕ} (i : Fin n) : (edgeB i)ᴴ = edgeB i := by
  unfold edgeB
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, majoranaOdd_herm,
    majoranaEven_herm]
  have hI : star (Complex.I : ℂ) = -Complex.I := by simp
  rw [hI, odd_even_same_neg, smul_neg, neg_smul, neg_neg]

/-- The edge generator `edgeA i j` is Hermitian for distinct endpoints. -/
theorem edgeA_herm {n : ℕ} (i j : Fin n) (hij : i ≠ j) : (edgeA i j)ᴴ = edgeA i j := by
  unfold edgeA
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, majoranaEven_herm,
    majoranaEven_herm]
  have hI : star (-Complex.I : ℂ) = Complex.I := by simp
  rw [hI, even_even_neg (Ne.symm hij), smul_neg, ← neg_smul]

/-- Each vertex generator squares to the identity. See [Setia and Whitfield,
2018][SetiaWhitfield2018]. -/
theorem edgeB_sq {n : ℕ} (i : Fin n) : edgeB i * edgeB i = 1 := by
  unfold edgeB
  rw [smul_mul_smul_eq]
  have key : (majoranaEven i * majoranaOdd i) * (majoranaEven i * majoranaOdd i)
      = -(1 : Matrix (Reg n) (Reg n) ℂ) := by
    calc (majoranaEven i * majoranaOdd i) * (majoranaEven i * majoranaOdd i)
        = majoranaEven i * (majoranaOdd i * majoranaEven i) * majoranaOdd i := by
          noncomm_ring
      _ = -((majoranaEven i * majoranaEven i) *
              (majoranaOdd i * majoranaOdd i)) := by
          rw [odd_even_same_neg i]
          noncomm_ring
      _ = -((1 : Matrix (Reg n) (Reg n) ℂ) * (1 : Matrix (Reg n) (Reg n) ℂ)) := by
          rw [majoranaEven_sq, majoranaOdd_sq]
      _ = -(1 : Matrix (Reg n) (Reg n) ℂ) := by rw [mul_one]
  rw [Complex.I_mul_I, neg_one_smul, key, neg_neg]

/-- Each edge generator with distinct endpoints squares to the identity. -/
theorem edgeA_sq {n : ℕ} (i j : Fin n) (hij : i ≠ j) : edgeA i j * edgeA i j = 1 := by
  unfold edgeA
  rw [smul_mul_smul_eq]
  have hII : ((-Complex.I) * (-Complex.I) : ℂ) = -1 := by
    rw [neg_mul_neg, Complex.I_mul_I]
  have key : (majoranaEven i * majoranaEven j) * (majoranaEven i * majoranaEven j)
      = -(1 : Matrix (Reg n) (Reg n) ℂ) := by
    calc (majoranaEven i * majoranaEven j) * (majoranaEven i * majoranaEven j)
        = majoranaEven i * (majoranaEven j * majoranaEven i) * majoranaEven j := by
          noncomm_ring
      _ = -((majoranaEven i * majoranaEven i) *
              (majoranaEven j * majoranaEven j)) := by
          rw [even_even_neg (Ne.symm hij)]
          noncomm_ring
      _ = -((1 : Matrix (Reg n) (Reg n) ℂ) * (1 : Matrix (Reg n) (Reg n) ℂ)) := by
          rw [majoranaEven_sq, majoranaEven_sq]
      _ = -(1 : Matrix (Reg n) (Reg n) ℂ) := by rw [mul_one]
  rw [hII, neg_one_smul, key, neg_neg]

/-- Any two vertex generators commute. -/
theorem edgeB_comm {n : ℕ} (i j : Fin n) : edgeB i * edgeB j = edgeB j * edgeB i := by
  unfold edgeB
  rw [smul_mul_smul_eq, smul_mul_smul_eq]
  congr 1
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · calc (majoranaEven i * majoranaOdd i) * (majoranaEven j * majoranaOdd j)
        = majoranaEven i * (majoranaOdd i * majoranaEven j) * majoranaOdd j := by
          noncomm_ring
      _ = -((majoranaEven i * majoranaEven j) *
              (majoranaOdd i * majoranaOdd j)) := by
          rw [odd_even_neg hij]
          noncomm_ring
      _ = -((majoranaEven j * majoranaEven i) *
              (majoranaOdd j * majoranaOdd i)) := by
          rw [even_even_neg hij, odd_odd_neg hij]
          noncomm_ring
      _ = (majoranaEven j * majoranaOdd j) * (majoranaEven i * majoranaOdd i) := by
          rw [show (majoranaEven j * majoranaOdd j) * (majoranaEven i * majoranaOdd i)
                = majoranaEven j * (majoranaOdd j * majoranaEven i) * majoranaOdd i from by
              noncomm_ring,
            odd_even_neg (Ne.symm hij)]
          noncomm_ring

/-- Products of two even Majorana operators commute when the modes in one pair are disjoint from
those in the other pair, under the stated distinctness assumptions. -/
theorem even_even_shuffle_disjoint {n : ℕ} (i j k l : Fin n) (_hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (majoranaEven i * majoranaEven j) * (majoranaEven k * majoranaEven l)
      = (majoranaEven k * majoranaEven l) * (majoranaEven i * majoranaEven j) := by
  calc (majoranaEven i * majoranaEven j) * (majoranaEven k * majoranaEven l)
      = majoranaEven i * majoranaEven j * majoranaEven k * majoranaEven l := by
        noncomm_ring
    _ = -(majoranaEven i * majoranaEven k * majoranaEven j * majoranaEven l) := by
        rw [swap23 (majoranaEven i) (majoranaEven j) (majoranaEven k) (majoranaEven l)
          (even_even_neg hjk)]
    _ = majoranaEven k * majoranaEven i * majoranaEven j * majoranaEven l := by
        rw [swap12 (majoranaEven i) (majoranaEven k) (majoranaEven j) (majoranaEven l)
          (even_even_neg hik), neg_neg]
    _ = -(majoranaEven k * majoranaEven i * majoranaEven l * majoranaEven j) := by
        rw [swap34 (majoranaEven k) (majoranaEven i) (majoranaEven j) (majoranaEven l)
          (even_even_neg hjl)]
    _ = majoranaEven k * majoranaEven l * majoranaEven i * majoranaEven j := by
        rw [swap23 (majoranaEven k) (majoranaEven i) (majoranaEven l) (majoranaEven j)
          (even_even_neg hil), neg_neg]
    _ = (majoranaEven k * majoranaEven l) * (majoranaEven i * majoranaEven j) := by
        noncomm_ring

/-- Even-Majorana pair products sharing their first mode anticommute when the three modes are
pairwise distinct. -/
theorem even_even_shuffle_shared {n : ℕ} (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    (majoranaEven i * majoranaEven j) * (majoranaEven i * majoranaEven l)
      = -((majoranaEven i * majoranaEven l) * (majoranaEven i * majoranaEven j)) := by
  have h : (majoranaEven i * majoranaEven l) * (majoranaEven i * majoranaEven j)
      = majoranaEven j * majoranaEven l := by
    calc (majoranaEven i * majoranaEven l) * (majoranaEven i * majoranaEven j)
        = majoranaEven i * majoranaEven l * majoranaEven i * majoranaEven j := by
          noncomm_ring
      _ = -(majoranaEven i * majoranaEven i * majoranaEven l * majoranaEven j) := by
          rw [swap23 (majoranaEven i) (majoranaEven l) (majoranaEven i) (majoranaEven j)
            (even_even_neg (Ne.symm hil))]
      _ = -(majoranaEven l * majoranaEven j) := by
          rw [show majoranaEven i * majoranaEven i * majoranaEven l * majoranaEven j
                = (majoranaEven i * majoranaEven i) * (majoranaEven l * majoranaEven j) from by
              noncomm_ring,
            majoranaEven_sq, one_mul]
      _ = majoranaEven j * majoranaEven l := by
          rw [even_even_neg hjl]
  calc (majoranaEven i * majoranaEven j) * (majoranaEven i * majoranaEven l)
      = majoranaEven i * majoranaEven j * majoranaEven i * majoranaEven l := by
        noncomm_ring
    _ = -(majoranaEven i * majoranaEven i * majoranaEven j * majoranaEven l) := by
        rw [swap23 (majoranaEven i) (majoranaEven j) (majoranaEven i) (majoranaEven l)
          (even_even_neg (Ne.symm hij))]
    _ = -(majoranaEven j * majoranaEven l) := by
        rw [show majoranaEven i * majoranaEven i * majoranaEven j * majoranaEven l
              = (majoranaEven i * majoranaEven i) * (majoranaEven j * majoranaEven l) from by
            noncomm_ring,
          majoranaEven_sq, one_mul]
    _ = -((majoranaEven i * majoranaEven l) * (majoranaEven i * majoranaEven j)) := by
        rw [h]

/-- An even-Majorana pair product commutes with an even-odd product at a mode outside the pair. -/
theorem even_odd_shuffle_disjoint {n : ℕ} (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    (majoranaEven i * majoranaEven j) * (majoranaEven k * majoranaOdd k)
      = (majoranaEven k * majoranaOdd k) * (majoranaEven i * majoranaEven j) := by
  calc (majoranaEven i * majoranaEven j) * (majoranaEven k * majoranaOdd k)
      = majoranaEven i * majoranaEven j * majoranaEven k * majoranaOdd k := by
        noncomm_ring
    _ = -(majoranaEven i * majoranaEven k * majoranaEven j * majoranaOdd k) := by
        rw [swap23 (majoranaEven i) (majoranaEven j) (majoranaEven k) (majoranaOdd k)
          (even_even_neg hjk)]
    _ = majoranaEven i * majoranaEven k * majoranaOdd k * majoranaEven j := by
        rw [swap34 (majoranaEven i) (majoranaEven k) (majoranaEven j) (majoranaOdd k)
          (even_odd_neg hjk), neg_neg]
    _ = -(majoranaEven k * majoranaEven i * majoranaOdd k * majoranaEven j) := by
        rw [swap12 (majoranaEven i) (majoranaEven k) (majoranaOdd k) (majoranaEven j)
          (even_even_neg hik)]
    _ = majoranaEven k * majoranaOdd k * majoranaEven i * majoranaEven j := by
        rw [swap23 (majoranaEven k) (majoranaEven i) (majoranaOdd k) (majoranaEven j)
          (even_odd_neg hik), neg_neg]
    _ = (majoranaEven k * majoranaOdd k) * (majoranaEven i * majoranaEven j) := by
        noncomm_ring

/-- An even-Majorana pair product anticommutes with the even-odd product at its first mode when
its endpoints are distinct. -/
theorem even_odd_shuffle_shared {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (majoranaEven i * majoranaEven j) * (majoranaEven i * majoranaOdd i)
      = -((majoranaEven i * majoranaOdd i) * (majoranaEven i * majoranaEven j)) := by
  have h : (majoranaEven i * majoranaOdd i) * (majoranaEven i * majoranaEven j)
      = -(majoranaOdd i * majoranaEven j) := by
    calc (majoranaEven i * majoranaOdd i) * (majoranaEven i * majoranaEven j)
        = majoranaEven i * majoranaOdd i * majoranaEven i * majoranaEven j := by
          noncomm_ring
      _ = -(majoranaEven i * majoranaEven i * majoranaOdd i * majoranaEven j) := by
          rw [swap23 (majoranaEven i) (majoranaOdd i) (majoranaEven i) (majoranaEven j)
            (odd_even_same_neg i)]
      _ = -(majoranaOdd i * majoranaEven j) := by
          rw [show majoranaEven i * majoranaEven i * majoranaOdd i * majoranaEven j
                = (majoranaEven i * majoranaEven i) * (majoranaOdd i * majoranaEven j) from by
              noncomm_ring,
            majoranaEven_sq, one_mul]
  calc (majoranaEven i * majoranaEven j) * (majoranaEven i * majoranaOdd i)
      = majoranaEven i * majoranaEven j * majoranaEven i * majoranaOdd i := by
        noncomm_ring
    _ = -(majoranaEven i * majoranaEven i * majoranaEven j * majoranaOdd i) := by
        rw [swap23 (majoranaEven i) (majoranaEven j) (majoranaEven i) (majoranaOdd i)
          (even_even_neg (Ne.symm hij))]
    _ = -(majoranaEven j * majoranaOdd i) := by
        rw [show majoranaEven i * majoranaEven i * majoranaEven j * majoranaOdd i
              = (majoranaEven i * majoranaEven i) * (majoranaEven j * majoranaOdd i) from by
            noncomm_ring,
          majoranaEven_sq, one_mul]
    _ = majoranaOdd i * majoranaEven j := by
        rw [even_odd_neg (Ne.symm hij), neg_neg]
    _ = -((majoranaEven i * majoranaOdd i) * (majoranaEven i * majoranaEven j)) := by
        rw [h, neg_neg]

/-- An edge generator commutes with a vertex generator outside its endpoints. -/
theorem edgeA_commute_of_not_endpoint {n : ℕ} (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    edgeA i j * edgeB k = edgeB k * edgeA i j := by
  unfold edgeA edgeB
  rw [smul_mul_smul_eq, smul_mul_smul_eq]
  rw [show ((-Complex.I) * Complex.I : ℂ) = Complex.I * (-Complex.I) by ring,
    even_odd_shuffle_disjoint i j k hik hjk]

/-- An edge generator with distinct endpoints anticommutes with the vertex generator at its left
endpoint. -/
theorem edgeA_anticommute_left {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    edgeA i j * edgeB i = -(edgeB i * edgeA i j) := by
  unfold edgeA edgeB
  rw [smul_mul_smul_eq, smul_mul_smul_eq]
  have hs1 : ((-Complex.I) * Complex.I : ℂ) = 1 := by
    rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hs2 : (Complex.I * (-Complex.I) : ℂ) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [hs1, hs2]
  simp only [one_smul]
  exact even_odd_shuffle_shared i j hij

/-- An edge generator with distinct endpoints anticommutes with the vertex generator at its
right endpoint. -/
theorem edgeA_anticommute_right {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    edgeA i j * edgeB j = -(edgeB j * edgeA i j) := by
  have h1 : edgeA j i * edgeB j = -(edgeB j * edgeA j i) :=
    edgeA_anticommute_left j i (Ne.symm hij)
  have h2 : edgeA j i = -edgeA i j := edgeA_antisym i j hij
  rw [h2] at h1
  rw [neg_mul, mul_neg, neg_neg] at h1
  exact neg_eq_iff_eq_neg.mp h1

/-- Edge generators with disjoint endpoint pairs commute under the stated distinctness
assumptions. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem edgeA_commute_disjoint {n : ℕ} (i j k l : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    edgeA i j * edgeA k l = edgeA k l * edgeA i j := by
  unfold edgeA
  rw [smul_mul_smul_eq, smul_mul_smul_eq]
  rw [even_even_shuffle_disjoint i j k l hij hik hil hjk hjl]

/-- Edge generators sharing their first endpoint anticommute when the three endpoints are
pairwise distinct. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem edgeA_anticommute_shared {n : ℕ} (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) : edgeA i j * edgeA i l = -(edgeA i l * edgeA i j) := by
  unfold edgeA
  rw [smul_mul_smul_eq, smul_mul_smul_eq]
  have hs : ((-Complex.I) * (-Complex.I) : ℂ) = -1 := by
    rw [neg_mul_neg, Complex.I_mul_I]
  rw [hs, neg_one_smul, neg_one_smul, neg_neg,
    even_even_shuffle_shared i j l hij hil hjl, neg_neg]

end Qatlib.Papers.BKFermion17.FermionEdge
