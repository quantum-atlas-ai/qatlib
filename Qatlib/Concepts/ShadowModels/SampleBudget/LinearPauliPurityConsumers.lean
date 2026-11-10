/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.SampleBudget.RationalPauliMedian
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ShadowModels.ShadowVariance

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.SampleBudget
open Matrix
open scoped Classical BigOperators ComplexOrder

theorem native_pauli_mixed_density_actual_linear_median_consumer : ∀ (r : ℕ),
    nativePauliBlockBudget 1=1600 ∧
    nativePauliBadMass 1600 r ((1/2 : ℂ) • (1 : Operator 2)) tensorPurityMixedDensity 1 ≤
      (2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1) ∧
    (Matrix.trace (((1/2 : ℂ) • (1 : Operator 2))*((1/2 : ℂ) • (1 : Operator 2)))).re=1/2 ∧
    ∀ ω : Fin (2*r+1) → Fin 1600 → Fin 3 × Bool,
      (nativePauliMedian 1600 r ω).2.1=(2*r+1)*1279200 ∧
      (nativePauliMedian 1600 r ω).2.2.2 ≤ 10000*(2*r+1) := by
  intro r
  have hb : nativePauliBlockBudget 1=1600 := by norm_num [nativePauliBlockBudget]
  have hprob := (native_pauli_computable_tolerance_budget_and_purity_probability r
    ((1/2 : ℂ) • (1 : Operator 2)) tensorPurityMixedDensity 1 (by norm_num)).2
  refine ⟨hb,by simpa only [hb,Rat.cast_one] using hprob,?_,?_⟩
  · norm_num [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul,Matrix.trace_one]
  · intro ω
    have h := native_pauli_linear_median_same_output_and_all_ledgers 1600 r ω
    exact ⟨by simpa only [Nat.choose_two_right] using h.2.1,h.2.2.2.1⟩

theorem qSortCounted_range (n : ℕ) :
    (qSortCounted ((List.range n).map (fun k : ℕ => (k : ℚ)))).1=
      (List.range n).map (fun k : ℕ => (k : ℚ)) := by
  have hs : ((List.range n).map (fun k : ℕ => (k : ℚ))).SortedLE := by
    rw [List.sortedLE_iff_pairwise,List.pairwise_map]
    exact (List.sortedLE_iff_pairwise.mp (List.sortedLT_range n).sortedLE).imp
      (fun h => by exact_mod_cast h)
  exact (qSortCounted_perm _).eq_of_pairwise'
    (List.sortedLE_iff_pairwise.mp (qSortCounted_sorted _))
    (List.sortedLE_iff_pairwise.mp hs)

theorem nativePauliMedian_single (m : ℕ) (ω : Fin 1 → Fin m → Fin 3 × Bool) :
    nativePauliMedian m 0 ω=((nativePauliGroup (ω 0)).1,
      (nativePauliGroup (ω 0)).2.1,(nativePauliGroup (ω 0)).2.2,0) := by
  simp [nativePauliMedian,List.ofFn_succ,List.ofFn_zero,qSelect,qSelectFuel,
    qSortCounted,qInsertCounted]

set_option maxRecDepth 4096 in

theorem rational_selection_large_native_and_empty_consumers :
    (qSelect ([7,7,-3,0,7,-3] : List ℚ) 2).1=0 ∧
    (qSelect ((List.range 1001).map (fun k : ℕ => (k : ℚ))) 500).1=500 ∧
    (qSelect ((List.range 1001).map (fun k : ℕ => (k : ℚ))) 500).2 ≤ 10010000 ∧
    (qSelect ([] : List ℚ) 0)=(0,0) ∧
    ∀ (m : ℕ) (ω : Fin 1 → Fin m → Fin 3 × Bool),
      nativePauliMedian m 0 ω=((nativePauliGroup (ω 0)).1,
        (nativePauliGroup (ω 0)).2.1,(nativePauliGroup (ω 0)).2.2,0) := by
  refine ⟨by decide,?_,?_,by decide,nativePauliMedian_single⟩
  · rw [qSelect,(rational_selection_fuel_rank_and_duplicates _ _ _ (by simp)).1,
      qSortCounted_range]
    change ((List.range 1001).map (fun k : ℕ => (k : ℚ))).getD 500 ((0 : ℕ) : ℚ)=500
    rw [List.getD_map]
    simp
  · simpa only [qSelect,List.length_map,List.length_range] using
      rational_selection_sufficient_fuel_linear_comparisons
        ((List.range 1001).map (fun k : ℕ => (k : ℚ))).length 500
        ((List.range 1001).map (fun k : ℕ => (k : ℚ))) le_rfl

end Qatlib.Concepts.ShadowModels.SampleBudget
