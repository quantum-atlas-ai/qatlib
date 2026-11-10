/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Ring.Units
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Set.Defs
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovHelpers
import Mathlib.Topology.Algebra.Polynomial
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Polynomial
open scoped BigOperators

noncomputable def sharpLobattoNode (d : ℕ) (i : Fin (d + 1)) : ℝ :=
  Polynomial.Chebyshev.node d i.val
noncomputable def sharpLobattoBasis (d : ℕ) (i : Fin (d + 1)) : ℝ[X] :=
  Lagrange.basis Finset.univ (sharpLobattoNode d) i
noncomputable def sharpLobattoA (d : ℕ) : ℝ[X] :=
  (X ^ 2 - 1) * (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative

theorem sharpLobattoNode_injective (d : ℕ) : Function.Injective (sharpLobattoNode d) := by
  intro i j hij
  apply Fin.ext
  exact (Polynomial.Chebyshev.strictAntiOn_node d).injOn
    (by simpa using i.isLt) (by simpa using j.isLt) hij

theorem sharpLobattoA_eval_node (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    (sharpLobattoA d).eval (sharpLobattoNode d i) = 0 := by
  by_cases hi0 : i.val = 0
  · simp [sharpLobattoA, sharpLobattoNode, hi0, Polynomial.Chebyshev.node_eq_one]
  by_cases hid : i.val = d
  · simp [sharpLobattoA, sharpLobattoNode, hid,
      Polynomial.Chebyshev.node_eq_neg_one (by omega : d ≠ 0)]
  have he := Polynomial.Chebyshev.isLocalExtr_T_real (by omega : d ≠ 0)
    (by omega : 0 < i.val) (by omega : i.val < d)
  have hzero := he.deriv_eq_zero
  rw [Polynomial.deriv] at hzero
  simp [sharpLobattoA, sharpLobattoNode, Polynomial.Chebyshev.node, hzero]

theorem sharpLobattoA_eq_nodal (d : ℕ) (hd : 1 ≤ d) :
    sharpLobattoA d = C ((d : ℝ) * 2 ^ (d - 1)) *
      Lagrange.nodal Finset.univ (sharpLobattoNode d) := by
  have hdn : (d : ℝ) ≠ 0 := by positivity
  have hexp : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by omega
  have hform : sharpLobattoA d = (X ^ 2 - C (1 : ℝ)) *
      (C (d : ℝ) * Polynomial.Chebyshev.U ℝ ((d - 1 : ℕ) : ℤ)) := by
    simp [sharpLobattoA, Polynomial.Chebyshev.T_derivative_eq_U, hexp]
  have hdeg : (sharpLobattoA d).degree = (d + 1 : ℕ) := by
    rw [hform, Polynomial.degree_mul, Polynomial.degree_X_pow_sub_C (by norm_num),
      Polynomial.degree_C_mul hdn, Polynomial.Chebyshev.degree_U_natCast]
    norm_cast
    omega
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ
    (sharpLobattoNode_injective d).injOn
  · simp [hdeg]
  · rw [hdeg, Polynomial.degree_C_mul (by positivity), Lagrange.degree_nodal]
    simp
  · rw [hform, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
      (Polynomial.monic_X_pow_sub_C (1 : ℝ) (by norm_num : (2 : ℕ) ≠ 0)).leadingCoeff,
      Polynomial.leadingCoeff_C, Polynomial.Chebyshev.leadingCoeff_U_natCast,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]
    ring
  · intro i _
    rw [sharpLobattoA_eval_node d hd i, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero]

theorem sharpLobattoA_derivative (d : ℕ) (x : ℝ) :
    (sharpLobattoA d).derivative.eval x =
      x * (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative.eval x +
      (d : ℝ) ^ 2 * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x := by
  have he := congrArg (fun P : ℝ[X] => P.eval x)
    (Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
      (R := ℝ) (d : ℤ))
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X,
    Function.iterate_succ_apply, Function.iterate_zero_apply, Int.cast_natCast] at he
  simp only [sharpLobattoA, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  norm_num at he ⊢
  nlinarith [he]

theorem sharpLobattoNode_lt_tail (d : ℕ) (hd : 1 ≤ d)
    (i : Fin (d + 1)) (hi : i.val ≠ 0) :
    sharpLobattoNode d i < Real.cos (Real.pi / (2 * (d : ℝ))) := by
  have hdr : (0 : ℝ) < d := by positivity
  unfold sharpLobattoNode Polynomial.Chebyshev.node
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · apply (div_le_iff₀ hdr).mpr
    have hir : (i.val : ℝ) ≤ d := by exact_mod_cast (by omega : i.val ≤ d)
    nlinarith [Real.pi_pos]
  · apply (lt_div_iff₀ hdr).mpr
    have hir : (1 : ℝ) ≤ i.val := by exact_mod_cast (by omega : 1 ≤ i.val)
    have heq : Real.pi / (2 * (d : ℝ)) * d = Real.pi / 2 := by field_simp
    rw [heq]
    nlinarith [Real.pi_pos]

theorem sharpLobatto_T_nonneg (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : Real.cos (Real.pi / (2 * (d : ℝ))) ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x ∧
    0 ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative.eval x := by
  have hdr : (0 : ℝ) < d := by positivity
  have hangle : Real.pi / (2 * (d : ℝ)) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Real.pi_pos]
  have hangle0 : 0 ≤ Real.pi / (2 * (d : ℝ)) := by positivity
  have hx0 : 0 ≤ x := le_trans (Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hangle⟩) hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith) hx1
  have hθ : Real.arccos x ≤ Real.pi / (2 * (d : ℝ)) := by
    by_contra h
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ Real.pi / (2 * (d : ℝ))) (Real.arccos_le_pi x) (not_le.mp h)
    rw [hcos] at hc
    linarith
  have hdθ : (d : ℝ) * Real.arccos x ≤ Real.pi / 2 := by
    have heq : (d : ℝ) * (Real.pi / (2 * d)) = Real.pi / 2 := by field_simp
    calc _ ≤ (d : ℝ) * (Real.pi / (2 * d)) := mul_le_mul_of_nonneg_left hθ hdr.le
         _ = _ := heq
  constructor
  · rw [← hcos, Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.arccos_nonneg x, hdr], hdθ⟩
  · by_cases hxone : x = 1
    · subst x
      simp only [Polynomial.Chebyshev.derivative_T_eval_one, Int.cast_natCast]
      positivity
    have hs : 0 < Real.sin (Real.arccos x) :=
      Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr (lt_of_le_of_ne hx1 hxone))
        (Real.arccos_lt_pi.mpr (by linarith))
    have hu := Polynomial.Chebyshev.U_real_cos (θ := Real.arccos x) (n := (d : ℤ) - 1)
    rw [hcos] at hu
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hu
    have hU : 0 ≤ (Polynomial.Chebyshev.U ℝ ((d : ℤ) - 1)).eval x := by
      apply nonneg_of_mul_nonneg_left _ hs
      rw [hu]
      exact Real.sin_nonneg_of_nonneg_of_le_pi
        (mul_nonneg hdr.le (Real.arccos_nonneg x)) (by linarith [Real.pi_pos])
    rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul,
      Polynomial.eval_intCast, Int.cast_natCast]
    exact mul_nonneg hdr.le hU

theorem sharpLobattoA_tail_signs (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : Real.cos (Real.pi / (2 * (d : ℝ))) ≤ x) (hx1 : x ≤ 1) :
    (sharpLobattoA d).eval x ≤ 0 ∧ 0 ≤ (sharpLobattoA d).derivative.eval x := by
  obtain ⟨hT, hT'⟩ := sharpLobatto_T_nonneg d hd x hx hx1
  have hangle : Real.pi / (2 * (d : ℝ)) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Real.pi_pos]
  have hangle0 : 0 ≤ Real.pi / (2 * (d : ℝ)) := by positivity
  have hx0 : 0 ≤ x := le_trans (Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hangle⟩) hx
  constructor
  · simp only [sharpLobattoA, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hT'
  · rw [sharpLobattoA_derivative]
    exact add_nonneg (mul_nonneg hx0 hT') (mul_nonneg (sq_nonneg _) hT)

theorem sharpLobattoBasis_factor (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    C ((sharpLobattoA d).derivative.eval (sharpLobattoNode d i)) *
      (X - C (sharpLobattoNode d i)) * sharpLobattoBasis d i = sharpLobattoA d := by
  have hnorm : (Lagrange.nodal Finset.univ (sharpLobattoNode d)).derivative.eval
      (sharpLobattoNode d i) ≠ 0 := by
    rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i)]
    apply Lagrange.eval_nodal_not_at_node
    intro j hj
    exact fun h => (Finset.mem_erase.mp hj).1
      ((sharpLobattoNode_injective d) h.symm)
  rw [sharpLobattoA_eq_nodal d hd, Polynomial.derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C, sharpLobattoBasis, Lagrange.basis_eq_prod_sub_inv_mul_nodal_div
      (Finset.mem_univ i), Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i)]
  conv_rhs => rw [Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
  have hh : C ((Lagrange.nodal Finset.univ (sharpLobattoNode d)).derivative.eval
      (sharpLobattoNode d i)) *
      C (((Lagrange.nodal Finset.univ (sharpLobattoNode d)).derivative.eval
      (sharpLobattoNode d i))⁻¹) = (1 : ℝ[X]) := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hnorm, Polynomial.C_1]
  rw [Polynomial.C_mul]
  linear_combination C ((d : ℝ) * 2 ^ (d - 1)) *
    (X - C (sharpLobattoNode d i)) *
    Lagrange.nodal (Finset.univ.erase i) (sharpLobattoNode d) * hh

theorem sharpLobattoBasis_derivative_identity (d : ℕ) (hd : 1 ≤ d)
    (i : Fin (d + 1)) (x : ℝ) :
    (sharpLobattoA d).derivative.eval (sharpLobattoNode d i) *
        (x - sharpLobattoNode d i) ^ 2 * (sharpLobattoBasis d i).derivative.eval x =
      (sharpLobattoA d).derivative.eval x * (x - sharpLobattoNode d i) -
        (sharpLobattoA d).eval x := by
  have hf := sharpLobattoBasis_factor d hd i
  have hv := congrArg (fun P : ℝ[X] => P.eval x) hf
  have hder := congrArg (fun P : ℝ[X] => P.derivative.eval x) hf
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X] at hv
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_sub, Polynomial.derivative_X, sub_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one] at hder
  linear_combination (x - sharpLobattoNode d i) * hder - hv

theorem sharpLobattoA_node_derivative_sign (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ i.val * (sharpLobattoA d).derivative.eval (sharpLobattoNode d i) := by
  have hdr : (0 : ℝ) < d := by positivity
  have hs : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
    rw [← mul_pow]; simp
  rw [sharpLobattoA_derivative]
  by_cases hi0 : i.val = 0
  · simp only [sharpLobattoNode, hi0, Polynomial.Chebyshev.node_eq_one,
      Polynomial.Chebyshev.derivative_T_eval_one, Polynomial.Chebyshev.T_eval_one,
      Int.cast_natCast, pow_zero, one_mul, mul_one]
    positivity
  by_cases hid : i.val = d
  · have htneg : (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative.eval (-1) =
        -(d : ℝ) ^ 2 * (-1 : ℝ) ^ d := by
      rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul, Polynomial.eval_intCast,
        Polynomial.Chebyshev.U_eval_neg_one, Int.negOnePow_sub, Int.negOnePow_one, Units.val_mul]
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_sub, Int.cast_natCast,
        Int.cast_negOnePow_natCast, Units.val_neg, Units.val_one]
      ring
    simp only [sharpLobattoNode, hid, Polynomial.Chebyshev.node_eq_neg_one (by omega : d ≠ 0),
      htneg, Polynomial.Chebyshev.T_eval_neg_one, Int.cast_negOnePow_natCast]
    rw [hid] at hs
    nlinarith [hs, sq_pos_of_pos hdr]
  have he := Polynomial.Chebyshev.isLocalExtr_T_real (by omega : d ≠ 0)
    (by omega : 0 < i.val) (by omega : i.val < d)
  have htzero : (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative.eval
      (sharpLobattoNode d i) = 0 := by
    simpa [sharpLobattoNode, Polynomial.Chebyshev.node, Polynomial.deriv] using he.deriv_eq_zero
  rw [htzero, mul_zero, zero_add]
  rw [sharpLobattoNode,
      Polynomial.Chebyshev.eval_T_real_node (by simpa using (by omega : i.val ≤ d))]
  calc _ = (d : ℝ) ^ 2 := by nlinarith [hs]
       _ > 0 := sq_pos_of_pos hdr

theorem sharpLobattoBasis_zero_derivative_nonneg (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : Real.cos (Real.pi / (2 * (d : ℝ))) ≤ x) :
    0 ≤ (sharpLobattoBasis d 0).derivative.eval x := by
  have hweight : 0 ≤ Lagrange.nodalWeight Finset.univ (sharpLobattoNode d) (0 : Fin (d + 1)) := by
    unfold Lagrange.nodalWeight
    apply Finset.prod_nonneg
    intro j hj
    apply inv_nonneg.mpr
    have hj0 : j.val ≠ 0 := by
      intro h
      exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
    have hlt := sharpLobattoNode_lt_tail d hd j hj0
    have hle := Real.cos_le_one (Real.pi / (2 * (d : ℝ)))
    simp only [sharpLobattoNode, Fin.val_zero, Polynomial.Chebyshev.node_eq_one]
    change Polynomial.Chebyshev.node d j.val < Real.cos (Real.pi / (2 * (d : ℝ))) at hlt
    linarith
  rw [sharpLobattoBasis, Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ 0),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ 0), Polynomial.derivative_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply mul_nonneg hweight
  rw [Lagrange.derivative_nodal, Polynomial.eval_finsetSum]
  apply Finset.sum_nonneg
  intro j hj
  rw [Lagrange.eval_nodal]
  apply Finset.prod_nonneg
  intro k hk
  have hk0 : k.val ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1 (Fin.ext h)
  exact sub_nonneg.mpr (le_trans (sharpLobattoNode_lt_tail d hd k hk0).le hx)

theorem sharpLobatto_tail_derivative_signs (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : Real.cos (Real.pi / (2 * (d : ℝ))) ≤ x) (hx1 : x ≤ 1)
    (i : Fin (d + 1)) :
    0 ≤ (-1 : ℝ) ^ i.val * (sharpLobattoBasis d i).derivative.eval x := by
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    simpa using sharpLobattoBasis_zero_derivative_nonneg d hd x hx
  have hdiff : 0 < x - sharpLobattoNode d i :=
    sub_pos.mpr (lt_of_lt_of_le (sharpLobattoNode_lt_tail d hd i hi) hx)
  have hnode := sharpLobattoA_node_derivative_sign d hd i
  obtain ⟨hA, hA'⟩ := sharpLobattoA_tail_signs d hd x hx hx1
  have hid := sharpLobattoBasis_derivative_identity d hd i x
  have hprod : 0 ≤ (sharpLobattoA d).derivative.eval (sharpLobattoNode d i) *
      (sharpLobattoBasis d i).derivative.eval x := by
    apply nonneg_of_mul_nonneg_left (b := (x - sharpLobattoNode d i) ^ 2) _ (sq_pos_of_pos hdiff)
    rw [mul_right_comm, hid]
    exact sub_nonneg.mpr (le_trans hA (mul_nonneg hA' hdiff.le))
  have hs : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
    rw [← mul_pow]; simp
  apply nonneg_of_mul_nonneg_right (a := (-1 : ℝ) ^ i.val *
    (sharpLobattoA d).derivative.eval (sharpLobattoNode d i)) _ hnode
  calc _ = (sharpLobattoA d).derivative.eval (sharpLobattoNode d i) *
      (sharpLobattoBasis d i).derivative.eval x := by
        linear_combination (sharpLobattoA d).derivative.eval (sharpLobattoNode d i) *
          (sharpLobattoBasis d i).derivative.eval x * hs
       _ ≥ 0 := hprod

theorem sharpLobatto_derivative_interpolation (d : ℕ) (p : ℝ[X])
    (hdeg : p.natDegree ≤ d) (x : ℝ) :
    p.derivative.eval x = ∑ i : Fin (d + 1),
      p.eval (sharpLobattoNode d i) * (sharpLobattoBasis d i).derivative.eval x := by
  have hdegree : p.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hdeg)
    simpa only [Finset.card_univ, Fintype.card_fin] using!
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  have he := Lagrange.eq_interpolate (sharpLobattoNode_injective d).injOn hdegree
  have hdereq := congrArg (fun P : ℝ[X] => P.derivative.eval x) he
  simpa [Lagrange.interpolate, Polynomial.derivative_sum, Polynomial.derivative_C_mul,
    Polynomial.eval_finsetSum, sharpLobattoBasis] using hdereq

theorem sharpLobatto_tail_derivative_mass (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : Real.cos (Real.pi / (2 * (d : ℝ))) ≤ x) (hx1 : x ≤ 1) :
    (∑ i : Fin (d + 1), |(sharpLobattoBasis d i).derivative.eval x|) =
      (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative.eval x := by
  rw [sharpLobatto_derivative_interpolation d _ (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [sharpLobattoNode,
      Polynomial.Chebyshev.eval_T_real_node (by simpa using (by omega : i.val ≤ d))]
  have hs := sharpLobatto_tail_derivative_signs d hd x hx hx1 i
  have he : |(-1 : ℝ) ^ i.val * (sharpLobattoBasis d i).derivative.eval x| =
      |(sharpLobattoBasis d i).derivative.eval x| := by
    rw [abs_mul, abs_neg_one_pow, one_mul]
  rw [abs_of_nonneg hs] at he
  exact he.symm

theorem sharpLobatto_tail_bound (d : ℕ) (p : ℝ[X]) (C : ℝ)
    (hd : 1 ≤ d) (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    (x : ℝ) (hx : Real.cos (Real.pi / (2 * (d : ℝ))) ≤ x) (hx1 : x ≤ 1) :
    |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * C := by
  have hangle : Real.pi / (2 * (d : ℝ)) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Real.pi_pos]
  have hangle0 : 0 ≤ Real.pi / (2 * (d : ℝ)) := by positivity
  have hx0 : 0 ≤ x := le_trans (Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hangle⟩) hx
  calc
    |p.derivative.eval x| ≤ ∑ i : Fin (d + 1),
        |p.eval (sharpLobattoNode d i)| * |(sharpLobattoBasis d i).derivative.eval x| := by
      rw [sharpLobatto_derivative_interpolation d p hdeg]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun i : Fin (d + 1) => p.eval (sharpLobattoNode d i) *
          (sharpLobattoBasis d i).derivative.eval x) Finset.univ
    _ ≤ ∑ i : Fin (d + 1), C * |(sharpLobattoBasis d i).derivative.eval x| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (hb _ Polynomial.Chebyshev.node_mem_Icc) (abs_nonneg _)
    _ = C * (Polynomial.Chebyshev.T ℝ (d : ℤ)).derivative.eval x := by
      rw [← Finset.mul_sum, sharpLobatto_tail_derivative_mass d hd x hx hx1]
    _ ≤ C * (d : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact le_trans (le_abs_self _) (sharp_markov_chebyshev d x ⟨by linarith, hx1⟩)
    _ = (d : ℝ) ^ 2 * C := mul_comm _ _

end Qatlib.Concepts.QueryComplexity.DegreeMethod
