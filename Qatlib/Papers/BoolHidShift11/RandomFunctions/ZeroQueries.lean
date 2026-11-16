/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalMath

@[expose] public section


/-! # Real zero-query executions under the uniform hidden-shift law

A fixed halting decision tree succeeds with probability exactly 2^(-n),
computed using the same function/shift average as the original lower target.
Unlike a free success field, this probability is tied to execution.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.RandomFunctions.ZeroQueries
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open ClassicalMath
open scoped BigOperators ENNReal

/-- The actual success probability of a zero-query deterministic guess. -/
theorem haltSuccess {n : ℕ} (z : Reg n) (oracle : Bool × Reg n → Bool) (s : Reg n) :
    BoolQueryTree.SuccessProb (PMF.pure (.halt z)) oracle (fun out => out=s)=
      if z=s then 1 else 0 := by
  classical
  unfold BoolQueryTree.SuccessProb
  rw [tsum_eq_single (BoolQueryTree.halt z)]
  · by_cases hz : z=s <;> simp [PMF.pure_apply,BoolQueryTree.Run,hz]
  · intro tree ht
    simp [PMF.pure_apply,ht]

/-- Its full source function/shift average is exactly the reciprocal cube size. -/
theorem haltAverage {n : ℕ} (z : Reg n) :
    avgSuccess (PMF.pure (BoolQueryTree.halt z))=((2:ℝ)^n)⁻¹ := by
  classical
  unfold avgSuccess
  simp_rw [haltSuccess]
  have hs : (∑ s : Reg n, (if z=s then (1:ℝ≥0∞) else 0).toReal)=1 := by
    have ht : ∀ s : Reg n, (if z=s then (1:ℝ≥0∞) else 0).toReal=
        if s=z then (1:ℝ) else 0 := by
      intro s
      by_cases h : s=z
      · subst s; simp
      · simp [h,Ne.symm h]
    simp_rw [ht]
    simp
  simp_rw [hs]
  have hc : (0:ℝ)<Fintype.card (Reg n → Bool) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,card_reg]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  field_simp

end Qatlib.Papers.BoolHidShift11.RandomFunctions.ZeroQueries
