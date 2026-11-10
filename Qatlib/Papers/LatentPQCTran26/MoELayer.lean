/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.LatentPQCTran26.MoELayer
variable {I : Type*} [Fintype I] [Nonempty I]

def coefficient (eta : I → ℝ) (i : I) : ℝ := Real.exp (eta i) / ∑ j, Real.exp (eta j)

theorem denominator_pos (eta : I → ℝ) : 0 < ∑ j, Real.exp (eta j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (eta j)) Finset.univ_nonempty

theorem coefficient_pos (eta : I → ℝ) (i : I) : 0 < coefficient eta i :=
  div_pos (Real.exp_pos _) (denominator_pos eta)

theorem coefficient_sum (eta : I → ℝ) : ∑ i, coefficient eta i = 1 := by
  simp only [coefficient,← Finset.sum_div]
  exact div_self (denominator_pos eta).ne'

def parameters {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (eta : I → ℝ) (experts : I → E) : E := ∑ i, coefficient eta i • experts i

theorem identical_experts {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (eta : I → ℝ) (x : E) : parameters eta (fun _ => x) = x := by
  rw [parameters,← Finset.sum_smul,coefficient_sum,one_smul]

theorem decoded_identical {E S : Type*} [AddCommMonoid E] [Module ℝ E]
    (eta : I → ℝ) (x : E) (U : E → S) :
    U (parameters eta (fun _ => x)) = U x := by rw [identical_experts]

theorem oneHot_error [DecidableEq I] (eta : I → ℝ) (j : I) :
    ∑ i, |coefficient eta i - (if i=j then 1 else 0)| = 2*(1-coefficient eta j) := by
  classical
  have hj : coefficient eta j ≤ 1 := by
    rw [← coefficient_sum eta]
    exact Finset.single_le_sum (fun i _ => (coefficient_pos eta i).le) (Finset.mem_univ j)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  simp only [ite_true,abs_of_nonpos (sub_nonpos.mpr hj)]
  have hs : ∑ i ∈ Finset.univ.erase j, |coefficient eta i - (if i=j then 1 else 0)| =
      ∑ i ∈ Finset.univ.erase j, coefficient eta i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi,abs_of_pos (coefficient_pos eta i)]
  rw [hs]
  have ht := Finset.sum_erase_add Finset.univ (coefficient eta) (Finset.mem_univ j)
  rw [coefficient_sum] at ht
  linarith

end Qatlib.Papers.LatentPQCTran26.MoELayer
