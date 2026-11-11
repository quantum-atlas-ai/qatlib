/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.FermionEdge.Relations

/-!
# Fermionic operators in the edge-generator dictionary

This module rewrites fermionic number, excitation, and pairing expressions using the edge
generators `edgeA` and `edgeB`. Intermediate Majorana identities track scalar factors, operator
order, and the commutation conditions needed for the double-excitation formula. See
[SetiaWhitfield2018].

## Main statements

* `numberOp_eq_half`: expresses occupation through the vertex generator.
* `excitation_eq`: rewrites a symmetric single excitation.
* `doubleExcitation_eq`: rewrites a four-mode double excitation.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BKFermion17.Dictionary

open Matrix
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BKFermion17.FermionEdge
open Qatlib.Papers.BKFermion17.FermionEdge

/-- Twice the creation operator is the even Majorana operator plus `Complex.I` times the odd
Majorana operator. -/
theorem two_smul_creation {n : ℕ} (k : Fin n) :
    (2 : ℂ) • creation k = majoranaEven k + Complex.I • majoranaOdd k := by
  unfold majoranaEven majoranaOdd
  rw [smul_smul, Complex.I_mul_I, neg_one_smul,
    show (2 : ℂ) • creation k = creation k + creation k from two_smul ℂ (creation k)]
  abel

/-- Twice the annihilation operator is the even Majorana operator minus `Complex.I` times the
odd Majorana operator. -/
theorem two_smul_annihilation {n : ℕ} (k : Fin n) :
    (2 : ℂ) • annihilation k = majoranaEven k + (-Complex.I) • majoranaOdd k := by
  unfold majoranaEven majoranaOdd
  rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul,
    show (2 : ℂ) • annihilation k = annihilation k + annihilation k from
      two_smul ℂ (annihilation k)]
  abel

/-- Expand the product of two scalar-weighted matrix sums into four ordered terms. -/
theorem add_mul_add_smul {n : ℕ} (c d : ℂ)
    (A B C D : Matrix (Reg n) (Reg n) ℂ) :
    (A + c • B) * (C + d • D) =
      A * C + d • (A * D) + c • (B * C) + (c * d) • (B * D) := by
  rw [add_mul, mul_add, mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_mul_smul_eq]
  abel

/-- Four times `X * Y` equals the product of twice `X` and twice `Y`. -/
theorem four_smul_mul {n : ℕ} (X Y : Matrix (Reg n) (Reg n) ℂ) :
    (4 : ℂ) • (X * Y) = (2 : ℂ) • X * ((2 : ℂ) • Y) := by
  rw [smul_mul_smul_eq, show (2 : ℂ) * 2 = 4 by norm_num]

/-- The vertex edge generator equals the identity minus twice the occupation operator. -/
theorem edgeB_eq_one_sub_two_numberOp {n : ℕ} (i : Fin n) :
    edgeB i = 1 - (2 : ℂ) • numberOp i := by
  unfold edgeB
  rw [majoranaEven_majoranaOdd, smul_smul]
  have hII : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
  rw [hII, neg_one_smul,
    show (2 : ℂ) • numberOp i = numberOp i + numberOp i from two_smul ℂ (numberOp i)]
  abel

/-- The occupation operator equals one half of `1 - edgeB i`. See [Setia and Whitfield,
2018][SetiaWhitfield2018]. -/
theorem numberOp_eq_half {n : ℕ} (i : Fin n) :
    numberOp i = (2⁻¹ : ℂ) • (1 - edgeB i) := by
  rw [edgeB_eq_one_sub_two_numberOp]
  have h : (1 : Matrix (Reg n) (Reg n) ℂ) - (1 - (2 : ℂ) • numberOp i)
      = (2 : ℂ) • numberOp i := by abel
  rw [h, smul_smul, show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

/-- Rewrite a product of occupation operators as the product of their half-scaled edge-generator
expressions. -/
theorem coulomb_eq {n : ℕ} (i j : Fin n) :
    numberOp i * numberOp j =
      ((2⁻¹ : ℂ) • (1 - edgeB i)) * ((2⁻¹ : ℂ) • (1 - edgeB j)) := by
  rw [← numberOp_eq_half i, ← numberOp_eq_half j]

/-- The product of occupation operators equals one quarter of `(1 - edgeB i) * (1 - edgeB j)`. -/
theorem coulomb_eq_fourth {n : ℕ} (i j : Fin n) :
    numberOp i * numberOp j = (4⁻¹ : ℂ) • ((1 - edgeB i) * (1 - edgeB j)) := by
  rw [coulomb_eq, smul_mul_smul_eq,
    show ((2⁻¹ : ℂ) * 2⁻¹) = 4⁻¹ by norm_num]

/-- The product `edgeA i j * edgeB j` equals the even-odd Majorana product on `i` and `j`. -/
theorem edgeA_mul_edgeB_right {n : ℕ} (i j : Fin n) :
    edgeA i j * edgeB j = majoranaEven i * majoranaOdd j := by
  unfold edgeA edgeB
  rw [smul_mul_smul_eq]
  have hc : ((-Complex.I) * Complex.I : ℂ) = 1 := by
    rw [neg_mul, Complex.I_mul_I, neg_neg]
  rw [hc, one_smul]
  have h : majoranaEven i * majoranaEven j * (majoranaEven j * majoranaOdd j)
      = majoranaEven i * (majoranaEven j * majoranaEven j) * majoranaOdd j := by
    noncomm_ring
  rw [h, majoranaEven_sq, mul_one]

/-- The product `edgeB i * edgeA i j` equals the negative odd-even Majorana product on `i` and
`j`. -/
theorem edgeB_mul_edgeA_left {n : ℕ} (i j : Fin n) :
    edgeB i * edgeA i j = -(majoranaOdd i * majoranaEven j) := by
  unfold edgeB edgeA
  rw [smul_mul_smul_eq]
  have hc : (Complex.I * (-Complex.I) : ℂ) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [hc, one_smul]
  have h : majoranaEven i * majoranaOdd i * (majoranaEven i * majoranaEven j)
      = -(majoranaOdd i * majoranaEven j) := by
    calc majoranaEven i * majoranaOdd i * (majoranaEven i * majoranaEven j)
        = majoranaEven i * (majoranaOdd i * majoranaEven i) * majoranaEven j := by
          noncomm_ring
      _ = majoranaEven i * (-(majoranaEven i * majoranaOdd i)) * majoranaEven j := by
          rw [odd_even_same_neg i]
      _ = -(majoranaEven i * majoranaEven i * majoranaOdd i * majoranaEven j) := by
          noncomm_ring
      _ = -(majoranaEven i * majoranaEven i) * (majoranaOdd i * majoranaEven j) := by
          noncomm_ring
      _ = -(majoranaOdd i * majoranaEven j) := by
          rw [majoranaEven_sq]
          rw [neg_one_mul]
  rw [h]

/-- The indicated sum of edge-generator products equals the difference of the two mixed Majorana
products. -/
theorem edgeA_edgeB_sum {n : ℕ} (i j : Fin n) :
    edgeA i j * edgeB j + edgeB i * edgeA i j
      = majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j := by
  rw [edgeA_mul_edgeB_right, edgeB_mul_edgeA_left, sub_eq_add_neg]

/-- For distinct modes, four times the symmetric single-excitation expression equals `-2 *
Complex.I` times the mixed Majorana difference. -/
theorem four_smul_excitation {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (4 : ℂ) • (creation i * annihilation j + creation j * annihilation i)
      = (-2 * Complex.I) • (majoranaEven i * majoranaOdd j
          - majoranaOdd i * majoranaEven j) := by
  rw [smul_add, four_smul_mul, four_smul_mul]
  rw [two_smul_creation i, two_smul_annihilation j,
    two_smul_creation j, two_smul_annihilation i]
  rw [add_mul_add_smul, add_mul_add_smul]
  have hII : (Complex.I * (-Complex.I) : ℂ) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  simp only [hII, one_smul]
  rw [even_even_neg (Ne.symm hij), odd_odd_neg (Ne.symm hij),
    even_odd_neg (Ne.symm hij), odd_even_neg (Ne.symm hij)]
  simp only [smul_neg]
  module

/-- For distinct modes, the symmetric single excitation equals `-Complex.I / 2` times `edgeA i j
* edgeB j + edgeB i * edgeA i j`. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem excitation_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    creation i * annihilation j + creation j * annihilation i
      = (-(2⁻¹ : ℂ) * Complex.I) • (edgeA i j * edgeB j + edgeB i * edgeA i j) := by
  have h := four_smul_excitation i j hij
  rw [← edgeA_edgeB_sum] at h
  have h' := congrArg (fun X => (4⁻¹ : ℂ) • X) h
  simp only [smul_smul] at h'
  rw [show (4⁻¹ : ℂ) * 4 = 1 by norm_num, one_smul,
    show (4⁻¹ : ℂ) * (-2 * Complex.I) = -(2⁻¹ : ℂ) * Complex.I by
      rw [show (4⁻¹ : ℂ) * (-2 * Complex.I) = ((4⁻¹ : ℂ) * (-2)) * Complex.I by ring,
        show ((4⁻¹ : ℂ) * (-2)) = -(2⁻¹ : ℂ) by norm_num]] at h'
  exact h'

/-- The occupation operator at `i` commutes with annihilation at a distinct mode `j`. -/
theorem numberOp_commute_annihilation_of_ne {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    numberOp i * annihilation j = annihilation j * numberOp i := by
  have haa : annihilation i * annihilation j = -(annihilation j * annihilation i) :=
    eq_neg_of_add_eq_zero_left (car_ann n i j)
  have hcar : annihilation j * creation i + creation i * annihilation j = 0 := by
    have h := car_aa n j i
    rw [if_neg (Ne.symm hij)] at h
    exact h
  have hca : creation i * annihilation j = -(annihilation j * creation i) := by
    have h2 : creation i * annihilation j + annihilation j * creation i = 0 := by
      rw [add_comm]
      exact hcar
    exact eq_neg_of_add_eq_zero_left h2
  calc numberOp i * annihilation j
      = (creation i * annihilation i) * annihilation j := by
          rw [creation_mul_annihilation_eq_numberOp]
    _ = creation i * (annihilation i * annihilation j) := by noncomm_ring
    _ = creation i * (-(annihilation j * annihilation i)) := by rw [haa]
    _ = -(creation i * annihilation j) * annihilation i := by noncomm_ring
    _ = -(-(annihilation j * creation i)) * annihilation i := by rw [hca]
    _ = annihilation j * (creation i * annihilation i) := by noncomm_ring
    _ = annihilation j * numberOp i := by rw [creation_mul_annihilation_eq_numberOp]

/-- The occupation operator at `i` commutes with creation at a distinct mode `j`. -/
theorem numberOp_commute_creation_of_ne {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    numberOp i * creation j = creation j * numberOp i := by
  have hac : annihilation i * creation j = -(creation j * annihilation i) := by
    have h := car_aa n i j
    rw [if_neg hij] at h
    exact eq_neg_of_add_eq_zero_left h
  have hcc : creation i * creation j = -(creation j * creation i) :=
    eq_neg_of_add_eq_zero_left (car_cre n i j)
  calc numberOp i * creation j
      = (creation i * annihilation i) * creation j := by
          rw [creation_mul_annihilation_eq_numberOp]
    _ = creation i * (annihilation i * creation j) := by noncomm_ring
    _ = creation i * (-(creation j * annihilation i)) := by rw [hac]
    _ = -(creation i * creation j) * annihilation i := by noncomm_ring
    _ = -(-(creation j * creation i)) * annihilation i := by rw [hcc]
    _ = creation j * (creation i * annihilation i) := by noncomm_ring
    _ = creation j * numberOp i := by rw [creation_mul_annihilation_eq_numberOp]

/-- For three pairwise distinct modes, the occupation-weighted excitation equals its
edge-generator excitation expression times the occupation expression at the middle mode. See
[Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem numberExcitation_eq {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    creation i * creation j * annihilation j * annihilation k
      + creation k * creation j * annihilation j * annihilation i
      = (-(2⁻¹ : ℂ) * Complex.I) • (edgeA i k * edgeB k + edgeB i * edgeA i k)
          * ((2⁻¹ : ℂ) • (1 - edgeB j)) := by
  have h1 : creation i * creation j * annihilation j * annihilation k
      = creation i * annihilation k * numberOp j := by
    rw [show creation i * creation j * annihilation j * annihilation k
          = creation i * (creation j * annihilation j) * annihilation k by noncomm_ring]
    rw [creation_mul_annihilation_eq_numberOp]
    rw [show creation i * numberOp j * annihilation k
          = creation i * (numberOp j * annihilation k) by noncomm_ring]
    rw [numberOp_commute_annihilation_of_ne j k hjk]
    noncomm_ring
  have h2 : creation k * creation j * annihilation j * annihilation i
      = creation k * annihilation i * numberOp j := by
    rw [show creation k * creation j * annihilation j * annihilation i
          = creation k * (creation j * annihilation j) * annihilation i by noncomm_ring]
    rw [creation_mul_annihilation_eq_numberOp]
    rw [show creation k * numberOp j * annihilation i
          = creation k * (numberOp j * annihilation i) by noncomm_ring]
    rw [numberOp_commute_annihilation_of_ne j i (Ne.symm hij)]
    noncomm_ring
  rw [h1, h2]
  rw [show creation i * annihilation k * numberOp j
        + creation k * annihilation i * numberOp j
        = (creation i * annihilation k + creation k * annihilation i) * numberOp j by
        noncomm_ring]
  rw [numberOp_eq_half j, ← excitation_eq i k hik]

/-- The sum of the ordered creation pair and annihilation pair equals half the difference of the
even-even and odd-odd Majorana products. -/
theorem pairCreation_eq {n : ℕ} (i j : Fin n) :
    creation i * creation j + annihilation i * annihilation j
      = (2⁻¹ : ℂ) • (majoranaEven i * majoranaEven j)
        - (2⁻¹ : ℂ) • (majoranaOdd i * majoranaOdd j) := by
  have key : (4 : ℂ) • (creation i * creation j + annihilation i * annihilation j)
      = (2 : ℂ) • (majoranaEven i * majoranaEven j)
        - (2 : ℂ) • (majoranaOdd i * majoranaOdd j) := by
    rw [smul_add, four_smul_mul, four_smul_mul]
    rw [two_smul_creation i, two_smul_creation j,
      two_smul_annihilation i, two_smul_annihilation j]
    rw [add_mul_add_smul, add_mul_add_smul]
    have hII : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
    have hII' : ((-Complex.I) * (-Complex.I) : ℂ) = -1 := by
      rw [neg_mul_neg, Complex.I_mul_I]
    simp only [hII, hII']
    module
  have h' := congrArg (fun X => (4⁻¹ : ℂ) • X) key
  simp only [smul_sub, smul_smul] at h'
  rw [show (4⁻¹ : ℂ) * 4 = 1 by norm_num, one_smul,
    show (4⁻¹ : ℂ) * 2 = 2⁻¹ by norm_num] at h'
  exact h'

/-- The indicated difference of edge-generator products equals the sum of the two mixed Majorana
products. -/
theorem edgeA_edgeB_sub {n : ℕ} (i j : Fin n) :
    edgeA i j * edgeB j - edgeB i * edgeA i j
      = majoranaEven i * majoranaOdd j + majoranaOdd i * majoranaEven j := by
  rw [edgeA_mul_edgeB_right, edgeB_mul_edgeA_left, sub_neg_eq_add]

/-- The ordered annihilation pair minus the creation pair equals `-Complex.I / 2` times the
specified edge-generator difference. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem pairAnnihilation_sub_creation_eq {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j - creation i * creation j
      = (-(2⁻¹ : ℂ) * Complex.I) • (edgeA i j * edgeB j - edgeB i * edgeA i j) := by
  have key : (4 : ℂ) • (annihilation i * annihilation j - creation i * creation j)
      = (-2 * Complex.I) • (majoranaEven i * majoranaOdd j
          + majoranaOdd i * majoranaEven j) := by
    rw [smul_sub, four_smul_mul, four_smul_mul]
    rw [two_smul_annihilation i, two_smul_annihilation j,
      two_smul_creation i, two_smul_creation j]
    rw [add_mul_add_smul, add_mul_add_smul]
    have hII : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
    have hII' : ((-Complex.I) * (-Complex.I) : ℂ) = -1 := by
      rw [neg_mul_neg, Complex.I_mul_I]
    simp only [hII, hII']
    module
  rw [← edgeA_edgeB_sub] at key
  have h' := congrArg (fun X => (4⁻¹ : ℂ) • X) key
  simp only [smul_smul] at h'
  rw [show (4⁻¹ : ℂ) * 4 = 1 by norm_num, one_smul,
    show (4⁻¹ : ℂ) * (-2 * Complex.I) = -(2⁻¹ : ℂ) * Complex.I by
      rw [show (4⁻¹ : ℂ) * (-2 * Complex.I) = ((4⁻¹ : ℂ) * (-2)) * Complex.I by ring,
        show ((4⁻¹ : ℂ) * (-2)) = -(2⁻¹ : ℂ) by norm_num]] at h'
  exact h'

/-- For distinct modes, the square of the product of their even Majorana operators is negative
identity. -/
theorem even_even_mul_self {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    majoranaEven i * majoranaEven j * (majoranaEven i * majoranaEven j) = -1 := by
  calc majoranaEven i * majoranaEven j * (majoranaEven i * majoranaEven j)
      = majoranaEven i * (majoranaEven j * majoranaEven i) * majoranaEven j := by
        noncomm_ring
    _ = majoranaEven i * (-(majoranaEven i * majoranaEven j)) * majoranaEven j := by
        rw [even_even_neg (Ne.symm hij)]
    _ = -(majoranaEven i * majoranaEven i * (majoranaEven j * majoranaEven j)) := by
        noncomm_ring
    _ = -1 := by
        rw [majoranaEven_sq, majoranaEven_sq]
        norm_num

/-- For distinct modes, the product of vertex generators equals the even-even Majorana product
times the odd-odd Majorana product. -/
theorem edgeB_mul_edgeB {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    edgeB i * edgeB j =
      majoranaEven i * majoranaEven j * (majoranaOdd i * majoranaOdd j) := by
  unfold edgeB
  rw [smul_mul_smul_eq]
  have hII : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
  rw [hII, neg_one_smul]
  have hshuffle : majoranaEven i * majoranaOdd i * (majoranaEven j * majoranaOdd j)
      = -(majoranaEven i * majoranaEven j * (majoranaOdd i * majoranaOdd j)) := by
    calc majoranaEven i * majoranaOdd i * (majoranaEven j * majoranaOdd j)
        = majoranaEven i * (majoranaOdd i * majoranaEven j) * majoranaOdd j := by
          noncomm_ring
      _ = majoranaEven i * (-(majoranaEven j * majoranaOdd i)) * majoranaOdd j := by
          rw [odd_even_neg hij]
      _ = -(majoranaEven i * majoranaEven j * (majoranaOdd i * majoranaOdd j)) := by
          noncomm_ring
  rw [hshuffle, neg_neg]

/-- For distinct modes, `Complex.I` times `edgeA i j * (1 + edgeB i * edgeB j)` equals the
even-even Majorana product minus the odd-odd product. -/
theorem edgeA_mul_one_add_edgeB {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Complex.I • (edgeA i j * (1 + edgeB i * edgeB j)) =
      majoranaEven i * majoranaEven j - majoranaOdd i * majoranaOdd j := by
  unfold edgeA
  rw [edgeB_mul_edgeB i j hij]
  rw [Matrix.smul_mul, smul_smul]
  have hII : (Complex.I * -Complex.I : ℂ) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [hII, one_smul, mul_add, mul_one, ← mul_assoc, even_even_mul_self i j hij,
    neg_one_mul, sub_eq_add_neg]

/-- For distinct modes, the ordered creation-pair plus annihilation-pair expression equals
`Complex.I / 2` times `edgeA i j * (1 + edgeB i * edgeB j)`. See [Setia and Whitfield,
2018][SetiaWhitfield2018]. -/
theorem pairCreation_edge_form {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    creation i * creation j + annihilation i * annihilation j =
      (2⁻¹ : ℂ) • (Complex.I • (edgeA i j * (1 + edgeB i * edgeB j))) := by
  rw [pairCreation_eq i j, edgeA_mul_one_add_edgeB i j hij]
  module

/-- For distinct modes, the specified edge-generator difference factors as `edgeA i j * (edgeB i
+ edgeB j)`. -/
theorem edgeA_mul_edgeB_sum_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    edgeA i j * edgeB j - edgeB i * edgeA i j =
      edgeA i j * (edgeB i + edgeB j) := by
  have h : edgeB i * edgeA i j = -(edgeA i j * edgeB i) := by
    calc edgeB i * edgeA i j = -(-(edgeB i * edgeA i j)) := by rw [neg_neg]
      _ = -(edgeA i j * edgeB i) := by rw [← edgeA_anticommute_left i j hij]
  rw [h]
  noncomm_ring

/-- For distinct modes, the ordered creation pair minus annihilation pair equals `Complex.I / 2`
times `edgeA i j * (edgeB i + edgeB j)`. -/
theorem pairAnnihilation_edge_form {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    creation i * creation j - annihilation i * annihilation j =
      (2⁻¹ : ℂ) • (Complex.I • (edgeA i j * (edgeB i + edgeB j))) := by
  have h := pairAnnihilation_sub_creation_eq i j
  rw [edgeA_mul_edgeB_sum_eq i j hij] at h
  calc creation i * creation j - annihilation i * annihilation j
      = -(annihilation i * annihilation j - creation i * creation j) := by
        noncomm_ring
    _ = -((-(2⁻¹ : ℂ) * Complex.I) •
          (edgeA i j * (edgeB i + edgeB j))) := by rw [h]
    _ = (2⁻¹ : ℂ) • (Complex.I • (edgeA i j * (edgeB i + edgeB j))) := by
        rw [← neg_smul]
        module

/-- An annihilation pair commutes with a creation pair when every mode in the first pair differs
from every mode in the second pair. -/
theorem annihilation_pair_commute_creation_pair {n : ℕ} (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    annihilation i * annihilation j * (creation k * creation l)
      = creation k * creation l * annihilation i * annihilation j := by
  have hik' : annihilation i * creation k = -(creation k * annihilation i) := by
    have h := car_aa n i k
    rw [if_neg hik] at h
    exact eq_neg_of_add_eq_zero_left h
  have hil' : annihilation i * creation l = -(creation l * annihilation i) := by
    have h := car_aa n i l
    rw [if_neg hil] at h
    exact eq_neg_of_add_eq_zero_left h
  have hjk' : annihilation j * creation k = -(creation k * annihilation j) := by
    have h := car_aa n j k
    rw [if_neg hjk] at h
    exact eq_neg_of_add_eq_zero_left h
  have hjl' : annihilation j * creation l = -(creation l * annihilation j) := by
    have h := car_aa n j l
    rw [if_neg hjl] at h
    exact eq_neg_of_add_eq_zero_left h
  calc annihilation i * annihilation j * (creation k * creation l)
      = annihilation i * (annihilation j * creation k) * creation l := by
        noncomm_ring
    _ = annihilation i * (-(creation k * annihilation j)) * creation l := by
        rw [hjk']
    _ = -(annihilation i * creation k * annihilation j * creation l) := by
        noncomm_ring
    _ = -((-(creation k * annihilation i)) * annihilation j * creation l) := by
        rw [hik']
    _ = creation k * annihilation i * annihilation j * creation l := by
        noncomm_ring
    _ = creation k * annihilation i * (annihilation j * creation l) := by
        noncomm_ring
    _ = creation k * annihilation i * (-(creation l * annihilation j)) := by
        rw [hjl']
    _ = -(creation k * annihilation i * creation l * annihilation j) := by
        noncomm_ring
    _ = -(creation k * (annihilation i * creation l) * annihilation j) := by
        noncomm_ring
    _ = -(creation k * (-(creation l * annihilation i)) * annihilation j) := by
        rw [hil']
    _ = creation k * creation l * annihilation i * annihilation j := by
        noncomm_ring

/-- For four pairwise distinct modes, the symmetric double excitation equals one eighth of the
ordered edge-generator product times the displayed polynomial in vertex generators. See
[Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem doubleExcitation_eq {n : ℕ} (i j k l : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    creation i * creation j * annihilation k * annihilation l
      + creation l * creation k * annihilation j * annihilation i
      = (8⁻¹ : ℂ) • (edgeA i j * edgeA k l
          * (-1 - edgeB i * edgeB j + edgeB i * edgeB k + edgeB i * edgeB l
              + edgeB j * edgeB k + edgeB j * edgeB l - edgeB k * edgeB l
              - edgeB i * edgeB j * edgeB k * edgeB l)) := by
  have hsecond : creation l * creation k * annihilation j * annihilation i
      = creation k * creation l * annihilation i * annihilation j := by
    have hc : creation l * creation k = -(creation k * creation l) :=
      eq_neg_of_add_eq_zero_left (car_cre n l k)
    have ha : annihilation j * annihilation i = -(annihilation i * annihilation j) :=
      eq_neg_of_add_eq_zero_left (car_ann n j i)
    calc creation l * creation k * annihilation j * annihilation i
        = (creation l * creation k) * (annihilation j * annihilation i) := by
          noncomm_ring
      _ = (-(creation k * creation l)) * (-(annihilation i * annihilation j)) := by
          rw [hc, ha]
      _ = creation k * creation l * annihilation i * annihilation j := by
          noncomm_ring
  rw [hsecond]
  have hkey : (2 : ℂ) •
        (creation i * creation j * annihilation k * annihilation l
          + creation k * creation l * annihilation i * annihilation j)
      = ((creation i * creation j + annihilation i * annihilation j)
          * (creation k * creation l + annihilation k * annihilation l))
        - ((creation i * creation j - annihilation i * annihilation j)
          * (creation k * creation l - annihilation k * annihilation l)) := by
    rw [show (2 : ℂ) •
        (creation i * creation j * annihilation k * annihilation l
          + creation k * creation l * annihilation i * annihilation j)
        = (creation i * creation j * annihilation k * annihilation l
            + creation k * creation l * annihilation i * annihilation j)
          + (creation i * creation j * annihilation k * annihilation l
            + creation k * creation l * annihilation i * annihilation j)
        from two_smul ℂ _]
    rw [← annihilation_pair_commute_creation_pair i j k l hik hil hjk hjl]
    noncomm_ring
  have h1 := pairCreation_edge_form i j hij
  have h2 := pairCreation_edge_form k l hkl
  have h3 := pairAnnihilation_edge_form i j hij
  have h4 := pairAnnihilation_edge_form k l hkl
  have hAB : ((creation i * creation j + annihilation i * annihilation j)
          * (creation k * creation l + annihilation k * annihilation l))
      = (-(4⁻¹) : ℂ) • (edgeA i j * (1 + edgeB i * edgeB j)
            * (edgeA k l * (1 + edgeB k * edgeB l))) := by
    rw [h1, h2, smul_mul_smul_eq, smul_mul_smul_eq, smul_smul, Complex.I_mul_I]
    congr 1
    ring
  have hCD : ((creation i * creation j - annihilation i * annihilation j)
          * (creation k * creation l - annihilation k * annihilation l))
      = (-(4⁻¹) : ℂ) • (edgeA i j * (edgeB i + edgeB j)
            * (edgeA k l * (edgeB k + edgeB l))) := by
    rw [h3, h4, smul_mul_smul_eq, smul_mul_smul_eq, smul_smul, Complex.I_mul_I]
    congr 1
    ring
  have hmain : (2 : ℂ) •
        (creation i * creation j * annihilation k * annihilation l
          + creation k * creation l * annihilation i * annihilation j)
      = (-(4⁻¹) : ℂ) • (edgeA i j * (1 + edgeB i * edgeB j)
            * (edgeA k l * (1 + edgeB k * edgeB l)))
        - (-(4⁻¹) : ℂ) • (edgeA i j * (edgeB i + edgeB j)
            * (edgeA k l * (edgeB k + edgeB l))) := by
    rw [hkey, hAB, hCD]
  have hAi : edgeA k l * edgeB i = edgeB i * edgeA k l :=
    edgeA_commute_of_not_endpoint k l i (Ne.symm hik) (Ne.symm hil)
  have hAj : edgeA k l * edgeB j = edgeB j * edgeA k l :=
    edgeA_commute_of_not_endpoint k l j (Ne.symm hjk) (Ne.symm hjl)
  have hAij : edgeA k l * (edgeB i * edgeB j) =
      edgeB i * edgeB j * edgeA k l := by
    calc edgeA k l * (edgeB i * edgeB j)
        = edgeA k l * edgeB i * edgeB j := by rw [mul_assoc]
      _ = edgeB i * edgeA k l * edgeB j := by rw [hAi]
      _ = edgeB i * (edgeA k l * edgeB j) := by rw [mul_assoc]
      _ = edgeB i * (edgeB j * edgeA k l) := by rw [hAj]
      _ = edgeB i * edgeB j * edgeA k l := by rw [← mul_assoc]
  have hsum : (edgeB i + edgeB j) * edgeA k l =
      edgeA k l * (edgeB i + edgeB j) := by
    rw [add_mul, mul_add, ← hAi, ← hAj]
  have hone : (1 + edgeB i * edgeB j) * edgeA k l =
      edgeA k l * (1 + edgeB i * edgeB j) := by
    rw [add_mul, one_mul, mul_add, mul_one, hAij]
  have hU : edgeA i j * (edgeB i + edgeB j)
        * (edgeA k l * (edgeB k + edgeB l))
      = edgeA i j * edgeA k l *
          ((edgeB i + edgeB j) * (edgeB k + edgeB l)) := by
    calc edgeA i j * (edgeB i + edgeB j) * (edgeA k l * (edgeB k + edgeB l))
        = edgeA i j * ((edgeB i + edgeB j) * edgeA k l) * (edgeB k + edgeB l) := by
          noncomm_ring
      _ = edgeA i j * (edgeA k l * (edgeB i + edgeB j)) * (edgeB k + edgeB l) := by
          rw [hsum]
      _ = edgeA i j * edgeA k l *
            ((edgeB i + edgeB j) * (edgeB k + edgeB l)) := by
          noncomm_ring
  have hX : edgeA i j * (1 + edgeB i * edgeB j)
        * (edgeA k l * (1 + edgeB k * edgeB l))
      = edgeA i j * edgeA k l *
          ((1 + edgeB i * edgeB j) * (1 + edgeB k * edgeB l)) := by
    calc edgeA i j * (1 + edgeB i * edgeB j) * (edgeA k l * (1 + edgeB k * edgeB l))
        = edgeA i j * ((1 + edgeB i * edgeB j) * edgeA k l) * (1 + edgeB k * edgeB l) := by
          noncomm_ring
      _ = edgeA i j * (edgeA k l * (1 + edgeB i * edgeB j)) * (1 + edgeB k * edgeB l) := by
          rw [hone]
      _ = edgeA i j * edgeA k l *
            ((1 + edgeB i * edgeB j) * (1 + edgeB k * edgeB l)) := by
          noncomm_ring
  have hpoly : (edgeB i + edgeB j) * (edgeB k + edgeB l)
        - (1 + edgeB i * edgeB j) * (1 + edgeB k * edgeB l)
      = -1 - edgeB i * edgeB j + edgeB i * edgeB k + edgeB i * edgeB l
          + edgeB j * edgeB k + edgeB j * edgeB l - edgeB k * edgeB l
          - edgeB i * edgeB j * edgeB k * edgeB l := by
    noncomm_ring
  have htwo : (2 : ℂ) •
        (creation i * creation j * annihilation k * annihilation l
          + creation k * creation l * annihilation i * annihilation j)
      = (4⁻¹ : ℂ) • (edgeA i j * edgeA k l *
          ((edgeB i + edgeB j) * (edgeB k + edgeB l)
            - (1 + edgeB i * edgeB j) * (1 + edgeB k * edgeB l))) := by
    rw [hmain, hU, hX]
    rw [mul_sub]
    module
  calc creation i * creation j * annihilation k * annihilation l
        + creation k * creation l * annihilation i * annihilation j
      = (2⁻¹ : ℂ) • ((2 : ℂ) •
          (creation i * creation j * annihilation k * annihilation l
            + creation k * creation l * annihilation i * annihilation j)) := by
        rw [smul_smul]
        norm_num
    _ = (2⁻¹ : ℂ) • ((4⁻¹ : ℂ) • (edgeA i j * edgeA k l *
          ((edgeB i + edgeB j) * (edgeB k + edgeB l)
            - (1 + edgeB i * edgeB j) * (1 + edgeB k * edgeB l)))) := by
        rw [htwo]
    _ = (8⁻¹ : ℂ) • (edgeA i j * edgeA k l *
          ((edgeB i + edgeB j) * (edgeB k + edgeB l)
            - (1 + edgeB i * edgeB j) * (1 + edgeB k * edgeB l))) := by
        rw [smul_smul]
        norm_num
    _ = (8⁻¹ : ℂ) • (edgeA i j * edgeA k l
          * (-1 - edgeB i * edgeB j + edgeB i * edgeB k + edgeB i * edgeB l
              + edgeB j * edgeB k + edgeB j * edgeB l - edgeB k * edgeB l
              - edgeB i * edgeB j * edgeB k * edgeB l)) := by
        rw [hpoly]

end Qatlib.Papers.BKFermion17.Dictionary
