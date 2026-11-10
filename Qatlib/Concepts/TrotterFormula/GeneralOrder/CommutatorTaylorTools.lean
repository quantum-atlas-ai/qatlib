/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Set MeasureTheory Filter
open scoped Classical BigOperators ContDiff Topology

def pfTaylorBefore {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (p : ℕ) (t : ℝ) : E :=
  ∑ n∈Finset.range p,(t^n/(n.factorial:ℝ)) • iteratedDeriv n f 0

theorem pfTaylorBefore_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (n : ℕ) (t : ℝ) : pfTaylorBefore f (n+1) t=taylorWithinEval f n univ 0 t := by
  rw [taylor_within_apply]
  simp only [pfTaylorBefore,iteratedDerivWithin_univ,sub_zero,div_eq_mul_inv,mul_comm]

theorem pf_taylor_before_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ→E) (hf : ContDiff ℝ ∞ f) (p : ℕ) (t C : ℝ) (hC : 0≤C)
    (hder : ∀ u∈uIcc 0 t,‖iteratedDeriv p f u‖≤C) :
    ‖f t-pfTaylorBefore f p t‖≤C*|t| ^p/(p.factorial:ℝ) := by
  cases p with
  | zero => simpa [pfTaylorBefore] using! hder t (right_mem_uIcc)
  | succ n =>
    rw [pfTaylorBefore_succ]
    by_cases ht0 : t=0
    · subst t
      simp
    have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_Icc (by grind)
    have hpoly : taylorWithinEval f n (uIcc 0 t) 0 t=taylorWithinEval f n univ 0 t := by
      rw [taylor_within_apply,taylor_within_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))) (left_mem_uIcc),iteratedDerivWithin_univ]
    have hrem :=
        taylor_integral_remainder (n := n)
        ((hf.of_le (by exact_mod_cast (le_top : (n+1 : ℕ∞)≤⊤))).contDiffOn (s := uIcc 0 t))
    rw [hpoly] at hrem
    rw [hrem]
    let g := fun u : ℝ=>(C/(n.factorial:ℝ))*|t-u| ^n
    have hgc : Continuous g := by dsimp [g];fun_prop
    have hgb (u : ℝ) (hu' : u∈uIcc 0 t) :
        ‖((t-u)^n/(n.factorial:ℝ)) • iteratedDerivWithin (n+1) f (uIcc 0 t) u‖≤g u := by
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n+1 : ℕ∞)≤⊤))) hu']
      simp only [norm_smul,Real.norm_eq_abs,abs_div,abs_pow,Nat.abs_cast]
      calc _≤(|t-u| ^n/(n.factorial:ℝ))*C := mul_le_mul_of_nonneg_left (hder u hu') (by positivity)
           _=g u := by dsimp [g];ring
    have hb := intervalIntegral.norm_integral_le_abs_of_norm_le (μ := volume)
      (f := fun u=>((t-u)^n/(n.factorial:ℝ)) • iteratedDerivWithin (n+1) f (uIcc 0 t) u)
      (g := g) (by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu'
        exact hgb u (uIoc_subset_uIcc hu'))
      (hgc.intervalIntegrable 0 t)
    apply hb.trans_eq
    rw [intervalIntegral.abs_intervalIntegral_eq]
    have hgpos : 0≤∫ u in uIoc 0 t,g u := integral_nonneg (fun u=>by dsimp [g];positivity)
    rw [abs_of_nonneg hgpos]
    change (∫ u in uIoc 0 t,(C/(n.factorial:ℝ))*|t-u| ^n)=_
    rw [integral_const_mul]
    have hp : (∫ u in uIoc 0 t,|t-u| ^n)=|t| ^(n+1)/(n+1) := by
      calc _=(∫ u in uIoc t 0,|u-t| ^n) := by
             rw [uIoc_comm]
             apply integral_congr_ae
             exact Eventually.of_forall (fun u=>by (try dsimp only);rw [abs_sub_comm])
           _=_ := by
             simpa only [zero_sub,abs_neg] using!
               integral_pow_abs_sub_uIoc (a := t) (b := 0) (n := n)
    rw [hp,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
end Qatlib.Concepts.TrotterFormula.GeneralOrder
