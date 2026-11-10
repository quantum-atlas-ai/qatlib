/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.WeightedCost.PaidExpectation
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.WeightedCost
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess

theorem actual_paid_bound {L : ℕ} (hL : 0<L) (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L,(p i).toReal=q i.val) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (C N : ℝ) (hC : 0<C) (hN : 0≤N)
    (hrow : ∀ j, 0<j → rowCharge rows j≤2*C*N/Real.sqrt (prefixSum q j)) :
    (initialized p rows).mean (fun tr => (paid tr:ℝ))≤4*C*N/Real.sqrt (popt q) := by
  rw [initialized_paid_formula p q hq h0 hnn rows hlaw]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => rowCharge rows j*(q j/prefixSum q (j+1))) L]
  have hs : (∑ j ∈ Finset.range L, rowCharge rows j*(q j/prefixSum q (j+1))) =
      ∑ j ∈ Finset.Ico 1 L, rowCharge rows j*(q j/prefixSum q (j+1)) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_Ico,Finset.mem_range] at *
      omega
    · intro j hj hn
      have hz : j=0 := by simp only [Finset.mem_Ico,Finset.mem_range] at *; omega
      subst j
      simp [rowCharge]
  rw [hs]
  calc
    _ ≤ ∑ j ∈ Finset.Ico 1 L, 2*C*N*searchTerm q j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjp : 0<j := (Finset.mem_Ico.1 hj).1
      have hw : 0≤q j/prefixSum q (j+1) :=
        div_nonneg (hnn j) (prefix_positive q h0 hnn (j+1) (by omega)).le
      refine (mul_le_mul_of_nonneg_right (hrow j hjp) hw).trans_eq ?_
      simp only [searchTerm,div_eq_mul_inv]
      ring
    _ = 2*C*N*(∑ j ∈ Finset.Ico 1 L, searchTerm q j) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := expected_queries_bound q C N hC hN h0 hnn L hL
end Qatlib.Papers.QAOAScaling23.WeightedCost
