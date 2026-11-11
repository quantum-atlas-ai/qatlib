/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidualRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Split Residual Execution

Split Residual Execution constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual
open scoped BigOperators
open Qatlib

variable {S : Type*} [DecidableEq S]

/-- Construction for split Linear Site Q in the split residual execution model. -/
def splitLinearSiteQ (c : RecordCounts S) (u : S → ℚ) (α β : ℚ) (x : S) : ℚ :=
  -α*β*u x*((readRecordCounts c x).2 : ℚ)

/-- Construction for split Linear Q in the split residual execution model. -/
def splitLinearQ (rs : List (S × Bool)) (u : S → ℚ) (α β : ℚ) : ℚ :=
  let c := collectRecordCounts rs
  (c.keys.map (splitLinearSiteQ c u α β)).sum/(rs.length : ℚ)

/-- Construction for split Statistic Q in the split residual execution model. -/
def splitStatisticQ (M : ℕ) (rs : List (S × Bool)) (u : S → ℚ)
    (α β knownSquare : ℚ) : ℚ :=
  velocityStatisticQ M rs (fun _ => 0) α 0+2*splitLinearQ rs u α β+knownSquare

variable [Fintype S]

/-- Construction for target Square Q in the split residual execution model. -/
def targetSquareQ (β : ℚ) (u : S → ℚ) : ℚ :=
  (∑ x : S, (β*u x)^2)/(Fintype.card S : ℚ)

noncomputable section

variable {X : Type*}

/-- Complete original `ordered_add_linear` guarantee for `SplitResidualExecution`; all source hypotheses and output obligations are retained. -/
theorem ordered_add_linear {n : ℕ} (H : X → X → ℝ) (f : X → ℝ) (c : ℝ)
    (ω : Fin n → X) (hn : 2 ≤ n) :
    orderedUStatistic (addLinear H f c) ω=orderedUStatistic H ω+2*FinDist.avg f ω+c := by
  have hs : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then addLinear H f c (ω i) (ω j) else 0)=
      (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then H (ω i) (ω j) else 0)+
        2*((n : ℝ)-1)*(∑ i : Fin n, f (ω i))+((n*(n-1) : ℕ) : ℝ)*c := by
    have hp (i j : Fin n) :
        (if i ≠ j then addLinear H f c (ω i) (ω j) else 0)=
          (if i ≠ j then H (ω i) (ω j) else 0)+(if i ≠ j then f (ω i) else 0)+
          (if i ≠ j then f (ω j) else 0)+(if i ≠ j then c else 0) := by
      by_cases h : i=j
      · subst j; simp
      · simp only [ite_eq_left h, addLinear]
    simp_rw [hp, Finset.sum_add_distrib]
    rw [offdiag_left_sum, Finset.sum_comm (f := fun i j : Fin n => if i ≠ j then f (ω j) else 0)]
    have hr : (∑ j : Fin n, ∑ i : Fin n, if i ≠ j then f (ω j) else 0)=
        ((n : ℝ)-1)*(∑ j : Fin n, f (ω j)) := by
      simp_rw [ne_comm]
      exact offdiag_left_sum _
    rw [hr, offdiag_constant_sum c (by omega)]
    ring
  unfold orderedUStatistic FinDist.avg
  rw [hs, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp

/-- Complete original `weighted_grouped_sum` guarantee for `SplitResidualExecution`; all source hypotheses and output obligations are retained. -/
theorem weighted_grouped_sum {n : ℕ} (r : Fin n → S × Bool) (f : S → ℝ) :
    (∑ x : S, f x*groupedRecordSum (fun i => (r i).1) (fun i => recordSign (r i).2) x)=
      ∑ i : Fin n, f (r i).1*recordSign (r i).2 := by
  unfold groupedRecordSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hp (x : S) : f x*(if (r i).1=x then recordSign (r i).2 else 0)=
      if (r i).1=x then f (r i).1*recordSign (r i).2 else 0 := by
    by_cases h : (r i).1=x <;> simp [h]
  simp_rw [hp]
  simp

/-- Complete original `split_linear_cast` guarantee for `SplitResidualExecution`; all source hypotheses and output obligations are retained. -/
theorem split_linear_cast {n : ℕ} (r : Fin n → S × Bool) (u : S → ℚ) (α β : ℚ) :
    (splitLinearQ (List.ofFn r) u α β : ℝ)=
      FinDist.avg (targetLinear (α : ℝ) (β : ℝ) (fun x => (u x : ℝ))) r := by
  have hz (x : S) (hx : x ∉ (collectRecordCounts (List.ofFn r)).keys) :
      splitLinearSiteQ (collectRecordCounts (List.ofFn r)) u α β x=0 := by
    simp [splitLinearSiteQ, record_counts_not_mem _ _ hx]
  rw [splitLinearQ, record_counts_sparse_sum _ _ hz]
  simp only [List.length_ofFn, Rat.cast_div, Rat.cast_natCast, Rat.cast_sum]
  have hp (x : S) : (splitLinearSiteQ (collectRecordCounts (List.ofFn r)) u α β x : ℝ)=
      (-(α : ℝ)*(β : ℝ)*(u x : ℝ))*
        groupedRecordSum (fun i => (r i).1) (fun i => recordSign (r i).2) x := by
    dsimp only [splitLinearSiteQ]
    push_cast
    rw [(record_counts_real r x).2]
  simp_rw [hp]
  rw [weighted_grouped_sum]
  unfold FinDist.avg
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold targetLinear
  ring

/-- Construction for split Streaming in the split residual execution model. -/
def splitStreaming {n : ℕ} (u : S → ℝ) (α β : ℝ) (r : Fin n → S × Bool) : ℝ :=
  residualStreamingStatistic (fun _ => 0) α 0 r+2*FinDist.avg (targetLinear α β u) r+targetSquare β u

/-- Complete original `split_streaming_eq_ordered` guarantee for `SplitResidualExecution`; all source hypotheses and output obligations are retained. -/
theorem split_streaming_eq_ordered {n : ℕ} (u : S → ℝ) (α β : ℝ)
    (r : Fin n → S × Bool) (hn : 2 ≤ n) :
    splitStreaming u α β r=orderedUStatistic (splitKernel α β u) r := by
  rw [splitStreaming, residual_streaming_eq_ordered, splitKernel, ordered_add_linear _ _ _ r hn]

/-- Complete original `split_statistic_cast` guarantee for `SplitResidualExecution`; all source hypotheses and output obligations are retained. -/
theorem split_statistic_cast {n : ℕ} (r : Fin n → S × Bool) (u : S → ℚ) (α β : ℚ) :
    (splitStatisticQ (Fintype.card S) (List.ofFn r) u α β (targetSquareQ β u) : ℝ)=
      splitStreaming (fun x => (u x : ℝ)) (α : ℝ) (β : ℝ) r := by
  simp only [splitStatisticQ, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  rw [velocity_statistic_cast, split_linear_cast]
  have ht : (targetSquareQ β u : ℝ)=targetSquare (β : ℝ) (fun x => (u x : ℝ)) := by
    dsimp [targetSquareQ, targetSquare]
    push_cast
    rfl
  rw [ht]
  simp only [splitStreaming, Rat.cast_zero]

end
end Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual

#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.ordered_add_linear
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.weighted_grouped_sum
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_linear_cast
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_streaming_eq_ordered
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_statistic_cast
