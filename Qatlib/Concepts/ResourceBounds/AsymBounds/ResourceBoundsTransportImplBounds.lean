/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs

/-!
# Implementation bounds for search and parity

This module transports concrete search and parity programs into the common `Implements`,
`QueryUpper`, and `QueryLower` interfaces. It rules out nonterminating, timed-out, and constant
implementations of the relevant tasks, and supplies a resource budget for workspace Grover
search.

The search and query lower-bound background is given in [Grover1996] and [Ambainis2002].

## Main statements

* `search_implements_budget`: For `n ≥ 2`, the singleton-search generator implements its task
  within `searchBudget`.
* `parity_lower_bound_consumer`: The parity task has query lower bound `Fintype.card I / 2`,
  with multiplicative constant one, for the given family of parity programs.

## References

* [Grover, 1996][Grover1996]
* [Ambainis, 2002][Ambainis2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

open Qatlib
open Qatlib
open scoped ENNReal
set_option warningAsError false

namespace Qatlib.Concepts.ResourceBounds.AsymBounds
noncomputable section

/-- A computation that never returns cannot implement a task with a legal instance. -/
theorem never_not_implements {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account)
    (i : Inst) (hlegal : T.legal i) :
    ¬Implements T (fun _ => (.never : Outcome (Out × Account))) B := by
  intro h
  obtain ⟨o, acc, h1, _, _⟩ := h i hlegal
  simp at h1
end
noncomputable section

/-- A computation that always times out cannot implement a nontrivial task. -/
theorem timeout_not_implements {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account)
    (hnt : T.nontrivial) :
    ¬Implements T (fun _ => (.timeout : Outcome (Out × Account))) B := by
  intro h
  obtain ⟨i, j, hi, hj, hno⟩ := hnt
  obtain ⟨o, acc, h1, _, _⟩ := h i hi
  simp at h1
end
noncomputable section

/-- A computation with a fixed output cannot implement a nontrivial task, regardless of its
instance-dependent resource account. -/
theorem constant_not_implements {Inst Out : Type*} (T : TaskSpec Inst Out) (B : Account)
    (o0 : Out) (K : Inst → Account) (hnt : T.nontrivial) :
    ¬Implements T (fun i => .done (o0, K i)) B := by
  intro h
  obtain ⟨i, j, hi, hj, hno⟩ := hnt
  by_cases hok : T.ok i o0
  · obtain ⟨o, acc, h1, hok2, _⟩ := h j hj
    simp only [Outcome.done.injEq, Prod.mk.injEq] at h1
    have ho : o = o0 := h1.1.symm
    rw [ho] at hok2
    exact hno o0 ⟨hok, hok2⟩
  · obtain ⟨o, acc, h1, hok2, _⟩ := h i hi
    simp only [Outcome.done.injEq, Prod.mk.injEq] at h1
    have ho : o = o0 := h1.1.symm
    rw [ho] at hok2
    exact hok hok2
end
noncomputable section

/-- For `n ≥ 2`, workspace Grover search assigns Born mass at least `1 - 1 / Fintype.card (Reg
n)` to the marked query fiber. -/
theorem search_born_mass (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (w : W) (hn : 2 ≤ n) (x : Reg n) :
    MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
        (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
      (workspaceQueryFiber (W := W) x) ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ) :=
  (workspace_singleton_search_actual_upper (W := W) n w x hn).1
end
noncomputable section

/-- For `n ≥ 2`, the workspace Grover circuit uses at most `2 ^ n` queries. -/
theorem search_query_count_le (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (w : W) (hn : 2 ≤ n) :
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ)
      ≤ ((2 ^ n : ℕ) : ℝ) := by
  have hq : (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ)
      ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 :=
    (workspace_singleton_search_actual_upper (W := W) n w (fun _ => false) hn).2.1
  have hcard : (Fintype.card (Reg n) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast card_reg n
  have hN4 : (4 : ℝ) ≤ Fintype.card (Reg n) := by
    have h : (4 : ℕ) ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hcard]
    exact_mod_cast h
  have hNpos : (0 : ℝ) < Fintype.card (Reg n) := by
    rw [hcard]
    positivity
  have hsqrt : Real.sqrt (Fintype.card (Reg n) : ℝ) ≤ Fintype.card (Reg n) := by
    have h1 : (1 : ℝ) ≤ Fintype.card (Reg n) := by linarith
    have h2 : Fintype.card (Reg n) ≤ (Fintype.card (Reg n) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((Fintype.card (Reg n) : ℝ) - 1)]
    exact (Real.sqrt_le_iff (x := Fintype.card (Reg n))
      (y := Fintype.card (Reg n))).mpr ⟨hNpos.le, h2⟩
  have hpi : Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4
      ≤ Real.sqrt (Fintype.card (Reg n) : ℝ) := by
    have h1 : (4 - Real.pi) * Real.sqrt (Fintype.card (Reg n) : ℝ) ≥ 0 :=
      mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (Real.sqrt_nonneg _)
    have h2 : Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4
        = Real.sqrt (Fintype.card (Reg n) : ℝ)
          - (4 - Real.pi) * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 := by ring
    linarith
  calc (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ)
      ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 := hq
    _ ≤ Real.sqrt (Fintype.card (Reg n) : ℝ) := hpi
    _ ≤ Fintype.card (Reg n) := hsqrt
    _ = ((2 ^ n : ℕ) : ℝ) := hcard
end
noncomputable section

/-- The singleton-search generator is correct and yields a query upper bound of `2 ^ n` with
multiplicative constant one. -/
theorem search_upper_bound_consumer (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (w : W) (hn : 2 ≤ n) :
    Correct (singletonSearchTask n) (searchGen n W w) ∧
      QueryUpper (singletonSearchTask n) (fun _ => 2 ^ n) 1 := by
  have hq' := search_query_count_le n W w hn
  have hcorrect : Correct (singletonSearchTask n) (searchGen n W w) := by
    intro i _
    refine ⟨(i, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = i)))
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
          (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) i)),
      Account.ofCircuit (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)), ?_⟩
    refine ⟨rfl, ?_⟩
    exact ⟨rfl, search_born_mass n W w hn i⟩
  refine ⟨hcorrect, ?_⟩
  unfold QueryUpper
  refine ⟨searchGen n W w, hcorrect, ?_⟩
  intro i acc o _ hEq
  have hacc : acc =
      Account.ofCircuit (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) := by
    have h2 := hEq
    simp only [searchGen] at h2
    simp only [Outcome.done.injEq] at h2
    simp only [Prod.mk.injEq] at h2
    exact h2.2.symm
  rw [hacc]
  simp only [Account.ofCircuit]
  have hle : QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) ≤ 2 ^ n := by
    exact_mod_cast hq'
  omega
end
noncomputable section

/-- The resource account for singleton search, with query allowance `2 ^ n` and circuit-derived
gate and depth costs. -/
def searchBudget (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] : Account :=
  { Account.zero with
    queries := 2 ^ n
    macroGates := GateCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
    basicGates := GateCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
    depth := Size (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) }
end
noncomputable section

/-- For `n ≥ 2`, the singleton-search generator implements its task within `searchBudget`. -/
theorem search_implements_budget (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (w : W) (hn : 2 ≤ n) :
    Implements (singletonSearchTask n) (searchGen n W w) (searchBudget n W) := by
  intro i _
  refine ⟨(i, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = i)))
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
          (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) i)),
      Account.ofCircuit (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)),
      rfl, ⟨rfl, ?_⟩, ?_⟩
  · exact search_born_mass n W w hn i
  · have hq' := search_query_count_le n W w hn
    simp only [accountLE, Account.ofCircuit, searchBudget, Account.zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hq'
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
end
noncomputable section

/-- The parity task has query lower bound `Fintype.card I / 2`, with multiplicative constant
one, for the given family of parity programs. -/
theorem parity_lower_bound_consumer (I W : Type) [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] :
    QueryLower (parityGen : ParityProgram I W → Gen (I → Bool) ℝ) (parityTask I)
      (fun _ => Fintype.card I / 2) 1 := by
  intro P hC
  have hApprox : ∀ f : I → Bool,
      |MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) P.circuit P.psi) P.accept
        - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3 := by
    intro f
    obtain ⟨o, acc, hEq, hOk⟩ := hC f trivial
    have ho : o = MeasureProb
        (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) P.circuit P.psi) P.accept := by
      have h2 := hEq
      simp only [parityGen] at h2
      simp only [Outcome.done.injEq] at h2
      simp only [Prod.mk.injEq] at h2
      exact h2.1.symm
    rw [ho] at hOk
    change |MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) P.circuit P.psi)
        P.accept - parityIndicator f| ≤ 1 / 3 at hOk
    simpa only [parityIndicator] using! hOk
  have hlb : Fintype.card I ≤ 2 * QueryCount P.circuit :=
    parity_actual_bounded_error_query_lower_bound P.circuit P.psi P.accept P.unitary P.normalized
      hApprox
  refine ⟨fun _ => false, trivial, ?_⟩
  intro o acc hEq
  have hacc : acc = Account.ofCircuit P.circuit := by
    have h2 := hEq
    simp only [parityGen] at h2
    simp only [Outcome.done.injEq] at h2
    simp only [Prod.mk.injEq] at h2
    exact h2.2.symm
  rw [hacc]
  simp only [Account.ofCircuit]
  have hdiv : Fintype.card I / 2 ≤ QueryCount P.circuit := by
    have hstep := Nat.div_le_div_right (c := 2) hlb
    omega
  omega
end
end Qatlib.Concepts.ResourceBounds.AsymBounds
