/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LaurentPolys.FiniteBitCost.FiniteQSPDefs

/-!
# Algebraic identities for the polynomial-to-QSP bridge

The module proves exact two-by-two matrix identities for `rhwQSPBridgePair` and
`rhwQSPBridgeWord`. It relates polynomial-pair recursion to products of normalized factors and
diagonal signal matrices, including the diagonal powers needed for centering. These identities
connect polynomial constructions with the quantum signal processing framework [LowChuang2017].

## Main statements

* `rhw_qsp_bridge_pair_cons`: the polynomial-pair recursion as matrix multiplication.
* `rhw_qsp_bridge_pair_word`: conversion between the pair matrix and factor word.
* `rhw_qsp_bridge_word_pair_nonempty`: the nonempty-word specialization.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.FiniteBitCost
open Polynomial Matrix
open scoped Matrix.Norms.L2Operator

/-- Expands the product of two `rhwQSPBridgeMatrix` matrices into the usual two-by-two entry
formulas. -/
theorem rhw_qsp_bridge_mat_mul (a b c d e f g h : ℂ) :
    rhwQSPBridgeMatrix a b c d*rhwQSPBridgeMatrix e f g h=rhwQSPBridgeMatrix (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h) := by
  ext i j
  cases i <;> cases j <;> simp [rhwQSPBridgeMatrix,Matrix.mul_apply] <;> ring

/-- The bridge matrix with diagonal entries one and off-diagonal entries zero is the identity. -/
theorem rhw_qsp_bridge_mat_one : rhwQSPBridgeMatrix 1 0 0 1=(1:Matrix Bool Bool ℂ) := by
  ext i j
  cases i <;> cases j <;> simp [rhwQSPBridgeMatrix]

/-- For nonzero `w`, the bridge diagonal matrices at `w` and `w⁻¹` are two-sided inverses. -/
theorem rhw_qsp_bridge_diag_cancel (w : ℂ) (hw : w≠0) : rhwQSPBridgeDiagonal w*rhwQSPBridgeDiagonal w⁻¹=1 ∧ rhwQSPBridgeDiagonal w⁻¹*rhwQSPBridgeDiagonal w=1 := by
  constructor <;> rw [rhwQSPBridgeDiagonal,rhwQSPBridgeDiagonal,rhw_qsp_bridge_mat_mul] <;> simp only [inv_inv,zero_mul,mul_zero,add_zero,zero_add,
    mul_inv_cancel₀ hw,inv_mul_cancel₀ hw,rhw_qsp_bridge_mat_one]

/-- The bridge matrix of the empty polynomial-pair list is the identity. -/
theorem rhw_qsp_bridge_pair_nil (z : ℂ) : rhwQSPBridgePair [] z=1 := by
  simp only [rhwQSPBridgePair,nlftSU2,eval_one,eval_zero,star_one,star_zero,neg_zero,rhw_qsp_bridge_mat_one]

/-- For unit-modulus `w`, prepending a coefficient to the polynomial-pair list corresponds to
multiplication by its factor and conjugation of the remaining pair by the bridge diagonal. -/
theorem rhw_qsp_bridge_pair_cons (g : ℂ) (gs : List ℂ) (w : ℂ) (hw : ‖w‖=1) :
    rhwQSPBridgePair (g::gs) (w^2)=rhwQSPBridgeFactor g*rhwQSPBridgeDiagonal w*rhwQSPBridgePair gs (w^2)*rhwQSPBridgeDiagonal w⁻¹ := by
  have hw0 : w≠0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have hstar : star w=w⁻¹ := by
    have h : w*star w=1 := by
      change w*(starRingEnd ℂ) w=1
      rw [Complex.mul_conj']
      simp [hw]
    exact eq_inv_of_mul_eq_one_right h
  have hcn : star (((Real.sqrt (1+Complex.normSq g))⁻¹:ℝ):ℂ)=
      (((Real.sqrt (1+Complex.normSq g))⁻¹:ℝ):ℂ) := by simp
  simp only [rhwQSPBridgePair,nlftSU2,eval_smul,eval_sub,eval_add,eval_mul,eval_X,smul_eq_mul,
    starRingEnd_apply,star_mul,star_sub,star_add,star_star,star_pow,hcn,hstar,
    rhwQSPBridgeFactor,rhwQSPBridgeDiagonal,rhw_qsp_bridge_mat_mul,inv_inv]
  ext i j
  cases i <;> cases j <;> simp only [rhwQSPBridgeMatrix,Bool.false_eq_true,ite_false,ite_true]
  all_goals field_simp
  all_goals ring

/-- For nonzero `w`, the bridge word of an appended list equals the first word, followed by the
bridge diagonal and the second word. -/
theorem rhw_qsp_bridge_word_append (w : ℂ) (hw : w≠0) (xs ys : List ℂ) :
    rhwQSPBridgeWord w (xs++ys)=rhwQSPBridgeWord w xs*rhwQSPBridgeDiagonal w*rhwQSPBridgeWord w ys := by
  induction xs with
  | nil => simp only [List.nil_append,rhwQSPBridgeWord,(rhw_qsp_bridge_diag_cancel w hw).2,one_mul]
  | cons x xs ih => simp only [List.cons_append,rhwQSPBridgeWord,ih,mul_assoc]

/-- For nonzero `w`, the bridge word of a singleton list equals its bridge factor. -/
theorem rhw_qsp_bridge_word_singleton (w : ℂ) (hw : w≠0) (g : ℂ) : rhwQSPBridgeWord w [g]=rhwQSPBridgeFactor g := by
  simp only [rhwQSPBridgeWord,mul_assoc,(rhw_qsp_bridge_diag_cancel w hw).1,mul_one]

/-- For unit-modulus `w`, relates the polynomial-pair matrix at `w^2` times the length-th
diagonal power to the factor word times one diagonal matrix. -/
theorem rhw_qsp_bridge_pair_word (gs : List ℂ) (w : ℂ) (hw : ‖w‖=1) :
    rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^gs.length=rhwQSPBridgeWord w gs*rhwQSPBridgeDiagonal w := by
  have hw0 : w≠0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  induction gs with
  | nil => simp only [rhw_qsp_bridge_pair_nil,List.length_nil,pow_zero,mul_one,rhwQSPBridgeWord,(rhw_qsp_bridge_diag_cancel w hw0).2]
  | cons g gs ih =>
    rw [rhw_qsp_bridge_pair_cons g gs w hw,List.length_cons,pow_succ' (rhwQSPBridgeDiagonal w) gs.length,rhwQSPBridgeWord]
    simp only [mul_assoc]
    rw [← mul_assoc (rhwQSPBridgeDiagonal w⁻¹) (rhwQSPBridgeDiagonal w),
        (rhw_qsp_bridge_diag_cancel w hw0).2,one_mul,ih]

/-- For a nonempty list and unit-modulus `w`, expresses the bridge word as the polynomial-pair
matrix at `w^2` times the diagonal power `gs.length - 1`. -/
theorem rhw_qsp_bridge_word_pair_nonempty (gs : List ℂ) (hgs : gs≠[]) (w : ℂ) (hw : ‖w‖=1) :
    rhwQSPBridgeWord w gs=rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^(gs.length-1) := by
  have hw0 : w≠0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have hn : 1≤gs.length := List.length_pos_iff.mpr hgs
  have h := rhw_qsp_bridge_pair_word gs w hw
  rw [show gs.length=(gs.length-1)+1 by omega,pow_succ (rhwQSPBridgeDiagonal w) (gs.length-1)] at h
  have he := congrArg (fun M : Matrix Bool Bool ℂ => M*rhwQSPBridgeDiagonal w⁻¹) h
  simp only [mul_assoc,(rhw_qsp_bridge_diag_cancel w hw0).1,mul_one] at he
  exact he.symm

/-- Multiplying two bridge diagonal matrices multiplies their complex parameters. -/
theorem rhw_qsp_bridge_diag_mul (x y : ℂ) : rhwQSPBridgeDiagonal x*rhwQSPBridgeDiagonal y=rhwQSPBridgeDiagonal (x*y) := by
  simp only [rhwQSPBridgeDiagonal,rhw_qsp_bridge_mat_mul,zero_mul,mul_zero,add_zero,zero_add,mul_inv]

/-- A natural power of a bridge diagonal matrix equals the bridge diagonal at the corresponding
power of its parameter. -/
theorem rhw_qsp_bridge_diag_pow (w : ℂ) (n : ℕ) : (rhwQSPBridgeDiagonal w)^n=rhwQSPBridgeDiagonal (w^n) := by
  induction n with
  | zero => simp only [pow_zero,rhwQSPBridgeDiagonal,inv_one,rhw_qsp_bridge_mat_one]
  | succ n ih => rw [pow_succ,ih,rhw_qsp_bridge_diag_mul,pow_succ]

/-- The complex conjugate of a unit-modulus number equals its inverse. -/
theorem rhw_qsp_bridge_star_of_unit (w : ℂ) (hw : ‖w‖=1) : star w=w⁻¹ := by
  have h : w*star w=1 := by
    change w*(starRingEnd ℂ) w=1
    rw [Complex.mul_conj']
    simp [hw]
  exact eq_inv_of_mul_eq_one_right h

end Qatlib.Concepts.LaurentPolys.FiniteBitCost
