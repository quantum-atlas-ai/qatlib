/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchClock
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchUniform
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators

abbrev TerminalTrace (I : Type*) (sizes : ℕ → ℕ) := Σ n : ℕ, TerminalStage I sizes n

noncomputable def TerminalMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (x : TerminalTrace I sizes) : ℝ :=
  TerminalStageMass A sizes x.1 x.2

def TerminalCost {I : Type*} (sizes : ℕ → ℕ) (x : TerminalTrace I sizes) : ℕ :=
  TerminalIterations sizes x.1 x.2

def TerminalOutput {I : Type*} {sizes : ℕ → ℕ} (x : TerminalTrace I sizes) : I := x.2.2.2

theorem search_nonnegative_trace_sum {γ : ℕ → Type*} [∀ n, Fintype (γ n)]
    (f : (Σ n, γ n) → ℝ) (hf : ∀ x, 0 ≤ f x) (q : ℝ)
    (hrows : HasSum (fun n => ∑ x : γ n, f ⟨n,x⟩) q) : HasSum f q := by
  have hfib (n : ℕ) : HasSum (fun x : γ n => f ⟨n,x⟩) (∑ x : γ n, f ⟨n,x⟩) := hasSum_fintype _
  have hsummable : Summable f := (summable_sigma_of_nonneg hf).2
    ⟨fun n => (hfib n).summable, by simpa only [tsum_fintype] using hrows.summable⟩
  exact hrows.sigma_of_hasSum hfib hsummable

theorem search_terminal_law {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    HasSum (TerminalMass A (ExponentialSizes (Fintype.card I))) 1 ∧
    ∀ x : TerminalTrace I (ExponentialSizes (Fintype.card I)),
      0 ≤ TerminalMass A (ExponentialSizes (Fintype.card I)) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (ExponentialSizes (Fintype.card I)) x = 0) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hsizes := (search_exponential_schedule _ hN).2.1
  have hp (x : TerminalTrace I (ExponentialSizes (Fintype.card I))) :
      0 ≤ TerminalMass A (ExponentialSizes (Fintype.card I)) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (ExponentialSizes (Fintype.card I)) x = 0) :=
    (search_terminal_stage_law hN A _ hsizes x.1).1 x.2
  refine ⟨?_,hp⟩
  apply search_nonnegative_trace_sum _ (fun x => (hp x).1) 1
  change HasSum (fun n => ∑ x : TerminalStage I (ExponentialSizes (Fintype.card I)) n,
    TerminalStageMass A (ExponentialSizes (Fintype.card I)) n x) 1
  simp_rw [(search_terminal_stage_law hN A _ hsizes _).2]
  exact search_all_density_termination A hA hproper

theorem search_terminal_output {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (i : I) :
    HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      if TerminalOutput x = i then TerminalMass A (ExponentialSizes (Fintype.card I)) x else 0)
      (if i ∈ A then 1/(A.card : ℝ) else 0) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  let sizes := ExponentialSizes (Fintype.card I)
  have hsizes : ∀ k, 0 < sizes k := (search_exponential_schedule _ hN).2.1
  apply search_nonnegative_trace_sum
  · intro x
    split_ifs
    · exact ((search_terminal_law A hA hproper).2 x).1
    · exact le_rfl
  · have hrow (n : ℕ) : (∑ x : TerminalStage I sizes n,
        if TerminalOutput ⟨n,x⟩ = i then TerminalMass A sizes ⟨n,x⟩ else 0) = RetryOutputMass A sizes n i := by
      simp only [TerminalOutput, TerminalMass]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact search_terminal_output_marginal hN A sizes hsizes n i
    change HasSum (fun n => ∑ x : TerminalStage I sizes n,
      if TerminalOutput ⟨n,x⟩ = i then TerminalMass A sizes ⟨n,x⟩ else 0) _
    simp_rw [hrow]
    exact search_final_output_uniform A hA hproper i

theorem search_terminal_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (∑' n, RetryReach A (ExponentialSizes (Fintype.card I)) n *
        MeanQueries I (ExponentialSizes (Fintype.card I) n)) ∧
      q ≤ (9/2 : ℝ)*Real.sqrt ((Fintype.card I : ℝ)/A.card) := by
  obtain ⟨q,hq,hqnn,hqocc,hqbound⟩ := search_terminal_iteration_mean A hA hproper
  refine ⟨q,?_,hqnn,hqocc,hqbound⟩
  apply search_nonnegative_trace_sum
  · intro x
    exact mul_nonneg ((search_terminal_law A hA hproper).2 x).1 (Nat.cast_nonneg _)
  · exact hq

def BudgetOutput {I : Type*} {sizes : ℕ → ℕ} (budget : ℕ)
    (x : TerminalTrace I sizes) : Option I :=
  if TerminalCost sizes x ≤ budget then some (TerminalOutput x) else none

theorem search_budget_output_iff {I : Type*} {sizes : ℕ → ℕ}
    (budget : ℕ) (x : TerminalTrace I sizes) :
    BudgetOutput budget x = some (TerminalOutput x) ↔ TerminalCost sizes x ≤ budget := by
  simp [BudgetOutput]

alias search_terminal_trace_law := search_terminal_law
alias search_terminal_trace_output := search_terminal_output
alias search_terminal_trace_cost := search_terminal_cost

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
