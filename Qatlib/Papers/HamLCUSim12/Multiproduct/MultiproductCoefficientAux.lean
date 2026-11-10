/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffClosedFormStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassStructureStat
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

theorem multiproduct_closed_form_k_two (N : ℝ) (h1 : N^2 ≠ 1) (h4 : N^2 ≠ 4)
    (q : Fin 3) (hq : q.val < 2) :
    mCoeff 2 N q*((q.val+1 : ℝ)^2-N^2)*
      (((2+q.val+1).factorial : ℝ)*((2-q.val-1).factorial : ℝ))=
        (-1 : ℝ)^(2-q.val-1)*2*(q.val+1 : ℝ)^6 := by
  have hd1 : (1 : ℝ)-N^2 ≠ 0 := sub_ne_zero.mpr h1.symm
  have hd4 : (4 : ℝ)-N^2 ≠ 0 := sub_ne_zero.mpr h4.symm
  fin_cases q
  · norm_num [mCoeff, mNode, Fin.prod_univ_succ]
    field_simp [hd1]
    norm_num
  · norm_num [mCoeff, mNode, Fin.prod_univ_succ]
    field_simp [hd4]
    norm_num
  · norm_num at hq

theorem multiproduct_lagrange_basis (k : ℕ) (N : ℝ)
    (hzero : ∀ q, mNode k N q ≠ 0)
    (hinj : Function.Injective (fun q => mNode k N q^2)) (q : Fin (k+1)) :
    mCoeff k N q = Polynomial.eval 0
      (Lagrange.basis Finset.univ (fun j => (mNode k N j^2)⁻¹) q) := by
  have hyinj : Function.Injective (fun j => (mNode k N j^2)⁻¹) := by
    intro i j he
    apply hinj
    simpa using congrArg Inv.inv he
  unfold mCoeff
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ q)]
  simp only [ite_true, mul_one]
  rw [Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hjq : j ≠ q := (Finset.mem_erase.mp hj).1
  rw [if_neg hjq]
  have hd : mNode k N q^2-mNode k N j^2 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hjq (hinj he).symm
  have hyd : (mNode k N q^2)⁻¹-(mNode k N j^2)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hjq (hyinj he).symm
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  have hrev : -mNode k N q^2+mNode k N j^2 ≠ 0 := by
    intro he
    apply hd
    linarith
  field_simp [hzero q, hzero j, hd, hyd]
  ring_nf
  field_simp [hrev]

theorem multiproduct_moment_of_squared_distinct (k : ℕ) (N : ℝ)
    (hzero : ∀ q, mNode k N q ≠ 0)
    (hinj : Function.Injective (fun q => mNode k N q^2)) (m : ℕ) (hm : m ≤ k) :
    (∑ q : Fin (k+1), mCoeff k N q/mNode k N q^(2*m))=(0 : ℝ)^m := by
  let y : Fin (k+1) → ℝ := fun j => (mNode k N j^2)⁻¹
  have hyinj : Function.Injective y := by
    intro i j he
    apply hinj
    simpa [y] using congrArg Inv.inv he
  have hdeg : (Polynomial.X^m : Polynomial ℝ).degree <
      (Finset.univ : Finset (Fin (k+1))).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show m < k+1 by omega)
  have he := congrArg (Polynomial.eval (0 : ℝ))
    (Lagrange.eq_interpolate hyinj.injOn hdeg)
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at he
  calc
    _ = ∑ q : Fin (k+1), y q^m * Polynomial.eval 0 (Lagrange.basis Finset.univ y q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [multiproduct_lagrange_basis k N hzero hinj q]
      dsimp [y]
      rw [pow_mul, inv_pow]
      ring
    _ = _ := he.symm

theorem multiproduct_moments_of_squared_distinct (k : ℕ) (N : ℝ)
    (hzero : ∀ q, mNode k N q ≠ 0)
    (hinj : Function.Injective (fun q => mNode k N q^2)) :
    (∑ q : Fin (k+1), mCoeff k N q)=1 ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ k →
        (∑ q : Fin (k+1), mCoeff k N q/mNode k N q^(2*m))=0 := by
  constructor
  · simpa only [Nat.mul_zero, pow_zero, div_one] using
      multiproduct_moment_of_squared_distinct k N hzero hinj 0 (Nat.zero_le _)
  · intro m hm1 hmk
    simpa only [zero_pow (by omega : m ≠ 0)] using
      multiproduct_moment_of_squared_distinct k N hzero hinj m hmk

private theorem mNode_small (k : ℕ) (N : ℝ) (q : Fin (k+1)) (hq : q.val < k) :
    mNode k N q=(q.val+1 : ℝ) := by simp [mNode, hq]

private theorem mNode_last (k : ℕ) (N : ℝ) : mNode k N (Fin.last k)=N := by
  simp [mNode]

theorem multiproduct_last_coefficient_ge_one (k : ℕ) (hk : 1 ≤ k)
    (N : ℝ) (hN : (k : ℝ) < N) : 1 ≤ mCoeff k N (Fin.last k) := by
  unfold mCoeff
  apply Finset.one_le_prod₀
  intro j _
  by_cases hj : j=Fin.last k
  · simp [hj]
  · rw [if_neg hj, mNode_last]
    have hjk : j.val < k := by
      have hne : j.val ≠ k := fun he => hj (Fin.ext he)
      omega
    rw [mNode_small k N j hjk]
    have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hjk' : (j.val+1 : ℝ) ≤ k := by exact_mod_cast (show j.val+1 ≤ k by omega)
    have hden : 0 < N^2-(j.val+1 : ℝ)^2 := by
      nlinarith [show (0 : ℝ) ≤ (j.val : ℝ) from Nat.cast_nonneg _]
    apply (le_div_iff₀ hden).mpr
    nlinarith [sq_nonneg (j.val+1 : ℝ)]

theorem multiproduct_penultimate_negative (k : ℕ) (hk : 1 ≤ k)
    (N : ℝ) (hN : (k : ℝ) < N) :
    mCoeff k N (⟨k-1, by omega⟩ : Fin (k+1)) < 0 := by
  let q : Fin (k+1) := ⟨k-1, by omega⟩
  have hqk : q.val < k := by dsimp [q]; omega
  have hqval : (q.val+1 : ℝ)=(k : ℝ) := by
    exact_mod_cast (show q.val+1=k by dsimp [q]; omega)
  have hqnode : mNode k N q=(k : ℝ) := (mNode_small k N q hqk).trans hqval
  have hlq : Fin.last k ≠ q := by
    intro he; have := congrArg Fin.val he; dsimp [q] at this; (try simp at this); omega
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let f : Fin (k+1) → ℝ := fun j => if j=q then 1 else
    mNode k N q^2/(mNode k N q^2-mNode k N j^2)
  have hlast : f (Fin.last k) < 0 := by
    dsimp [f]
    rw [if_neg hlq, hqnode, mNode_last]
    apply div_neg_of_pos_of_neg (sq_pos_of_pos hk0)
    nlinarith
  have hrest : 0 < ∏ j ∈ Finset.univ.erase (Fin.last k), f j := by
    apply Finset.prod_pos
    intro j hj
    have hjl : j ≠ Fin.last k := (Finset.mem_erase.mp hj).1
    have hjk : j.val < k := by
      have hne : j.val ≠ k := fun he => hjl (Fin.ext he)
      omega
    dsimp [f]
    by_cases hjq : j=q
    · simp [hjq]
    · rw [if_neg hjq, hqnode, mNode_small k N j hjk]
      have hjq' : j.val ≠ k-1 := fun he => hjq (Fin.ext he)
      have hjk' : (j.val+1 : ℝ) < k := by exact_mod_cast (show j.val+1 < k by omega)
      apply div_pos (sq_pos_of_pos hk0)
      nlinarith [show (0 : ℝ) ≤ (j.val : ℝ) from Nat.cast_nonneg _]
  change (∏ j : Fin (k+1), f j) < 0
  rw [← Finset.mul_prod_erase _ f (Finset.mem_univ (Fin.last k))]
  exact mul_neg_of_neg_of_pos hlast hrest

end Qatlib.Papers.HamLCUSim12.Multiproduct
