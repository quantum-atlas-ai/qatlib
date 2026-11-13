/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.WorkspaceCircuit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.ENNReal.BigOperators

/-!
# Workspace machines and finite execution prefixes

`WorkspaceMachine` describes a quantum machine with classical control indexed by workspace
width, unitary gates, oracle queries, and instruments that may change the width. Its finite
execution traces carry the quantum state, control, outcome record, query count, and halting
status, using the quantum-operation framework of [Watrous2018].

Finite prefixes unroll to `WorkspaceCircuit` values with matching traces and expected query
counts. Monotonicity supports supremum definitions for unbounded halting masses and query costs,
while finite seed mixtures possess common approximation cutoffs; replay reconstructs the
terminal classical data from a halted trace's outcome record.

## Main statements

* `unrollWorkspaceMachine_traces`: identify machine prefixes with unrolled circuit traces.
* `workspaceMachineExpectedQueries_monotone`: expected query cost increases with the prefix
  length.
* `workspaceMachineSeedHaltMass_finite_approx`: choose a common cutoff for finitely many strict
  halting-mass thresholds.
* `workspaceMachineReplay_correct`: recover the classical data of every halted trace.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Classical ComplexOrder ENNReal

/-- A workspace-indexed instruction that halts, applies a gate, makes an oracle query, or
applies a finite-outcome instrument and continues at its output width. -/
inductive WorkspaceInstruction (d : ℕ) (C : ℕ → Type*) : ℕ → Type _ where
  | halt {k : ℕ} (accepted : Bool) : WorkspaceInstruction d C k
  | gate {k : ℕ} (G : Operator (d*k)) (next : C k) : WorkspaceInstruction d C k
  | query {k : ℕ} (next : C k) : WorkspaceInstruction d C k
  | instrument {k : ℕ} (s l : ℕ) (I : Instrument (Fin s) (d*k) (d*l))
      (next : Fin s → C l) : WorkspaceInstruction d C k

/-- A transition function assigning a workspace instruction to each width-indexed classical
control state. -/
abbrev WorkspaceMachine (d : ℕ) (C : ℕ → Type*) :=
  (k : ℕ) → C k → WorkspaceInstruction d C k

/-- The predicate that every gate instruction in the machine uses a unitary operator. -/
def workspaceMachineWellFormed {d : ℕ} {C : ℕ → Type*} (M : WorkspaceMachine d C) : Prop :=
  ∀ k c, match M k c with
    | .gate G _ => G ∈ Matrix.unitaryGroup (Fin (d*k)) ℂ
    | _ => True

/-- A workspace trace augmented with a classical control state at its final width and a Boolean
halting flag. -/
structure WorkspaceMachineTrace (d : ℕ) (C : ℕ → Type*) extends WorkspaceTrace d where
  control : C width
  halted : Bool

/-- Enumerate the machine's branch traces for a finite instruction budget, retaining pending
traces when the budget is exhausted. -/
noncomputable def workspaceMachineTraces {d : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) :
    {k : ℕ} → ℕ → C k → Operator (d*k) → List (WorkspaceMachineTrace d C)
  | k, 0, c, rho => [⟨⟨k,rho,false,0,[]⟩,c,false⟩]
  | k, T+1, c, rho => match M k c with
    | .halt b => [⟨⟨k,rho,b,0,[]⟩,c,true⟩]
    | .gate G next => workspaceMachineTraces M U T next (conjBranch G rho)
    | .query next =>
        (workspaceMachineTraces M U T next (conjBranch (forwardWorkspaceOracle k U) rho)).map
          fun t => {t with queries := t.queries+1}
    | .instrument s l I next =>
        (List.ofFn fun o : Fin s =>
          (workspaceMachineTraces M U T (next o) (I.branch o rho)).map fun t =>
            {t with outcomes := (s,o.val)::t.outcomes}).flatten

/-- The sum of trace masses of halted branches satisfying the supplied predicate on final width,
control, acceptance, and outcome record. -/
noncomputable def workspaceMachineHaltMass {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k))
    (E : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) : ℝ :=
  ((workspaceMachineTraces M U T c rho).map fun t =>
    if t.halted && E t.width t.control t.accepted t.outcomes then workspaceMass t.toWorkspaceTrace
    else 0).sum

/-- The sum of each finite-prefix branch mass times its oracle-query count, including pending
branches. -/
noncomputable def workspaceMachineExpectedQueries {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) : ℝ :=
  ((workspaceMachineTraces M U T c rho).map fun t =>
    workspaceMass t.toWorkspaceTrace * t.queries).sum

/-- The sum of the masses of finite-prefix traces that have not halted. -/
noncomputable def workspaceMachinePendingMass {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) : ℝ :=
  ((workspaceMachineTraces M U T c rho).map fun t =>
    if t.halted then 0 else workspaceMass t.toWorkspaceTrace).sum

/-- Unroll a machine for a finite instruction budget into a workspace circuit, replacing budget
exhaustion with rejection. -/
noncomputable def unrollWorkspaceMachine {d : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) : {k : ℕ} → ℕ → C k → WorkspaceCircuit d k
  | _, 0, _ => .halt false
  | k, T+1, c => match M k c with
    | .halt b => .halt b
    | .gate G next => .gate G (unrollWorkspaceMachine M T next)
    | .query next => .query (unrollWorkspaceMachine M T next)
    | .instrument s l I next => .instrument s l I (fun o => unrollWorkspaceMachine M T (next o))

/-- Every finite unrolling of a well-formed workspace machine is a well-formed workspace
circuit. -/
theorem unrollWorkspaceMachine_wellFormed {d : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (hM : workspaceMachineWellFormed M) :
    ∀ {k : ℕ} (T : ℕ) (c : C k), workspaceCircuitWellFormed (unrollWorkspaceMachine M T c) := by
  intro k T
  induction T generalizing k with
  | zero => intro c; trivial
  | succ T ih =>
    intro c
    cases h : M k c with
    | halt b => simp [unrollWorkspaceMachine, h, workspaceCircuitWellFormed]
    | gate G next =>
      simp only [unrollWorkspaceMachine, h, workspaceCircuitWellFormed]
      exact ⟨by simpa only [h] using hM k c, ih next⟩
    | query next => simpa only [unrollWorkspaceMachine, h, workspaceCircuitWellFormed] using ih next
    | instrument s l I next =>
      simpa only [unrollWorkspaceMachine, h, workspaceCircuitWellFormed] using
          (fun o => ih (next o))

/-- Forgetting machine control and halting flags in finite-prefix traces gives exactly the
traces of the unrolled workspace circuit. -/
theorem unrollWorkspaceMachine_traces {d : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) :
    ∀ {k : ℕ} (T : ℕ) (c : C k) (rho : Operator (d*k)),
      (workspaceMachineTraces M U T c rho).map (fun t => t.toWorkspaceTrace) =
        workspaceTraces U (unrollWorkspaceMachine M T c) rho := by
  intro k T
  induction T generalizing k with
  | zero => intro c rho; rfl
  | succ T ih =>
    intro c rho
    cases h : M k c with
    | halt b => simp [workspaceMachineTraces, unrollWorkspaceMachine, h, workspaceTraces]
    | gate G next => simp only [workspaceMachineTraces, unrollWorkspaceMachine, h, workspaceTraces]; exact ih next _
    | query next =>
      simp only [workspaceMachineTraces, unrollWorkspaceMachine, h, workspaceTraces, List.map_map]
      have hh := congrArg (List.map (fun t : WorkspaceTrace d => {t with queries := t.queries+1}))
        (ih next (conjBranch (forwardWorkspaceOracle k U) rho))
      simpa only [Function.comp_def, List.map_map] using hh
    | instrument s l I next =>
      simp only [workspaceMachineTraces, unrollWorkspaceMachine, h, workspaceTraces, List.map_flatten,
        List.map_map, List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext o
      have hh := congrArg (List.map (fun t : WorkspaceTrace d =>
        {t with outcomes := (s,o.val)::t.outcomes})) (ih (next o) (I.branch o rho))
      simpa only [Function.comp_def, List.map_map] using hh

/-- The expected oracle-query count of the unrolled circuit equals the finite-prefix machine
expected query count. -/
theorem unrollWorkspaceMachine_expected {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) :
    workspaceCircuitExpectedQueries U (unrollWorkspaceMachine M T c) rho =
      workspaceMachineExpectedQueries M U T c rho := by
  unfold workspaceCircuitExpectedQueries workspaceMachineExpectedQueries
  rw [← unrollWorkspaceMachine_traces M U T c rho, List.map_map]
  rfl

/-- Every branch state in a finite machine execution is positive semidefinite when the initial
state is positive semidefinite. -/
theorem workspaceMachineTraces_posSemidef {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) (hrho : rho.PosSemidef)
    (t : WorkspaceMachineTrace d C) (ht : t ∈ workspaceMachineTraces M U T c rho) :
    t.state.PosSemidef := by
  apply workspaceTraces_posSemidef U (unrollWorkspaceMachine M T c) rho hrho t.toWorkspaceTrace
  rw [← unrollWorkspaceMachine_traces M U T c rho]
  exact List.mem_map.mpr ⟨t,ht,rfl⟩

/-- For a well-formed machine and a unitary oracle, the total mass of all finite-prefix traces
equals the real trace of the initial operator. -/
private theorem workspaceMachineTraces_total {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (hM : workspaceMachineWellFormed M)
    (U : Operator d) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (T : ℕ) (c : C k) (rho : Operator (d*k)) :
    ((workspaceMachineTraces M U T c rho).map
      (fun t => workspaceMass t.toWorkspaceTrace)).sum = (trace rho).re := by
  have h := workspaceTraces_total U hU (unrollWorkspaceMachine M T c)
    (unrollWorkspaceMachine_wellFormed M hM T c) rho
  rw [← unrollWorkspaceMachine_traces M U T c rho, List.map_map] at h
  exact h

/-- A finite-prefix machine expected query count is nonnegative for a positive semidefinite
initial state. -/
private theorem workspaceMachineExpectedQueries_nonneg {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) (hrho : rho.PosSemidef) :
    0 ≤ workspaceMachineExpectedQueries M U T c rho := by
  rw [← unrollWorkspaceMachine_expected]
  exact workspaceCircuitExpectedQueries_nonneg U _ rho hrho

/-- Every finite-prefix halting-event mass is nonnegative for a positive semidefinite initial
state. -/
private theorem workspaceMachineHaltMass_nonneg {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) (hrho : rho.PosSemidef)
    (E : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) :
    0 ≤ workspaceMachineHaltMass M U T c rho E := by
  unfold workspaceMachineHaltMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (RCLike.nonneg_iff.mp
      (workspaceMachineTraces_posSemidef M U T c rho hrho t ht).trace_nonneg).1
  · exact le_rfl

/-- Express the halting-event mass for one additional instruction by cases on the current
instruction, prefixing the outcome record at instrument steps. -/
private theorem workspaceMachineHaltMass_succ {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k))
    (E : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) :
    workspaceMachineHaltMass M U (T+1) c rho E = match M k c with
      | .halt b => if E k c b [] then (trace rho).re else 0
      | .gate G next => workspaceMachineHaltMass M U T next (conjBranch G rho) E
      | .query next => workspaceMachineHaltMass M U T next
          (conjBranch (forwardWorkspaceOracle k U) rho) E
      | .instrument s l I next => ∑ o : Fin s,
          workspaceMachineHaltMass M U T (next o) (I.branch o rho)
            (fun l c b rec => E l c b ((s,o.val)::rec)) := by
  cases h : M k c <;>
    simp [workspaceMachineHaltMass, workspaceMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, workspaceMass]

/-- For a positive semidefinite initial state, the halting-event mass is monotone in the finite
instruction budget. -/
theorem workspaceMachineHaltMass_monotone {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (c : C k) (rho : Operator (d*k))
    (hrho : rho.PosSemidef)
    (E : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) :
    Monotone (fun T => workspaceMachineHaltMass M U T c rho E) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing k c rho E with
  | zero =>
    simpa only [workspaceMachineHaltMass, workspaceMachineTraces, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, add_zero] using workspaceMachineHaltMass_nonneg M U 1 c rho hrho E
  | succ T ih =>
    rw [workspaceMachineHaltMass_succ, workspaceMachineHaltMass_succ]
    cases h : M k c with
    | halt b => exact le_rfl
    | gate G next => exact ih next _ ((completelyPositive_conjBranch G).positive hrho) E
    | query next => exact ih next _ ((completelyPositive_conjBranch _).positive hrho) E
    | instrument s l I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)
        (fun l c b rec => E l c b ((s,o.val)::rec))

/-- The sum of pointwise sums over a list equals the sum of the two separate list sums. -/
private theorem workspace_sum_map_add {A : Type*} (xs : List A) (f g : A → ℝ) :
    (xs.map (fun x => f x+g x)).sum = (xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, add_left_comm]

/-- For a well-formed machine and unitary oracle, express the next-prefix expected query count
by the current instruction. A query adds the real trace of the current operator to the
continuation cost. -/
private theorem workspaceMachineExpectedQueries_succ {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (hM : workspaceMachineWellFormed M)
    (U : Operator d) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (T : ℕ) (c : C k) (rho : Operator (d*k)) :
    workspaceMachineExpectedQueries M U (T+1) c rho = match M k c with
      | .halt _ => 0
      | .gate G next => workspaceMachineExpectedQueries M U T next (conjBranch G rho)
      | .query next => (trace rho).re + workspaceMachineExpectedQueries M U T next
          (conjBranch (forwardWorkspaceOracle k U) rho)
      | .instrument s l I next => ∑ o : Fin s,
          workspaceMachineExpectedQueries M U T (next o) (I.branch o rho) := by
  cases h : M k c with
  | halt b => simp [workspaceMachineExpectedQueries, workspaceMachineTraces, h]
  | gate G next =>
    simp [workspaceMachineExpectedQueries, workspaceMachineTraces, h, Function.comp_def,
        workspaceMass]
  | instrument s l I next =>
    simp [workspaceMachineExpectedQueries, workspaceMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, workspaceMass]
  | query next =>
    simp only [workspaceMachineExpectedQueries, workspaceMachineTraces, h, List.map_map,
      Function.comp_def, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    rw [workspace_sum_map_add]
    change workspaceMachineExpectedQueries M U T next
      (conjBranch (forwardWorkspaceOracle k U) rho) +
      ((workspaceMachineTraces M U T next (conjBranch (forwardWorkspaceOracle k U) rho)).map
        fun t => workspaceMass t.toWorkspaceTrace).sum = _
    rw [workspaceMachineTraces_total M hM U hU,
      trace_conjBranch_unitary _ (forwardWorkspaceOracle_unitary _ U hU)]
    exact add_comm _ _

/-- For a well-formed machine, a unitary oracle, and a positive semidefinite initial state, the
finite-prefix expected query count is monotone in the instruction budget. -/
theorem workspaceMachineExpectedQueries_monotone {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (hM : workspaceMachineWellFormed M)
    (U : Operator d) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (c : C k) (rho : Operator (d*k)) (hrho : rho.PosSemidef) :
    Monotone (fun T => workspaceMachineExpectedQueries M U T c rho) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing k c rho with
  | zero =>
    simpa [workspaceMachineExpectedQueries, workspaceMachineTraces] using
      workspaceMachineExpectedQueries_nonneg M U 1 c rho hrho
  | succ T ih =>
    rw [workspaceMachineExpectedQueries_succ M hM U hU,
      workspaceMachineExpectedQueries_succ M hM U hU]
    cases h : M k c with
    | halt b => exact le_rfl
    | gate G next => exact ih next _ ((completelyPositive_conjBranch G).positive hrho)
    | query next =>
      exact add_le_add le_rfl (ih next _ ((completelyPositive_conjBranch _).positive hrho))
    | instrument s l I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)

/-- The supremum over finite instruction budgets of the extended nonnegative conversions of
halting-event masses. -/
noncomputable def workspaceMachineInfiniteHaltMass {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (c : C k) (rho : Operator (d*k))
    (E : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) : ℝ≥0∞ :=
  ⨆ T : ℕ, ENNReal.ofReal (workspaceMachineHaltMass M U T c rho E)

/-- The supremum over finite instruction budgets of the extended nonnegative conversions of
expected oracle-query counts. -/
noncomputable def workspaceMachineInfiniteExpectedQueries {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (c : C k) (rho : Operator (d*k)) : ℝ≥0∞ :=
  ⨆ T : ℕ, ENNReal.ofReal (workspaceMachineExpectedQueries M U T c rho)

/-- Every finite-prefix expected query count, converted to an extended nonnegative real, is at
most `workspaceMachineInfiniteExpectedQueries`. -/
theorem workspaceMachineExpectedQueries_le_infinite {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) :
    ENNReal.ofReal (workspaceMachineExpectedQueries M U T c rho) ≤
      workspaceMachineInfiniteExpectedQueries M U c rho := by
  exact le_iSup (fun S => ENNReal.ofReal (workspaceMachineExpectedQueries M U S c rho)) T

/-- The finite-distribution weighted sum of finite-prefix halting-event masses for a
seed-indexed family of machines and initial states. -/
noncomputable def workspaceMachineSeedHaltMass {d r : ℕ} {C : ℕ → Type*}
    (p : FinDist (Fin r)) (M : Fin r → WorkspaceMachine d C) (U : Operator d)
    (T : ℕ) (k : Fin r → ℕ) (c : (j : Fin r) → C (k j))
    (rho : (j : Fin r) → Operator (d*k j))
    (E : Fin r → (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) : ℝ :=
  ∑ j, p.prob j * workspaceMachineHaltMass (M j) U T (c j) (rho j) (E j)

/-- The extended nonnegative weighted sum of unbounded halting-event masses for a finite seed
distribution. -/
noncomputable def workspaceMachineSeedInfiniteHaltMass {d r : ℕ} {C : ℕ → Type*}
    (p : FinDist (Fin r)) (M : Fin r → WorkspaceMachine d C) (U : Operator d)
    (k : Fin r → ℕ) (c : (j : Fin r) → C (k j))
    (rho : (j : Fin r) → Operator (d*k j))
    (E : Fin r → (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (p.prob j) * workspaceMachineInfiniteHaltMass (M j) U (c j) (rho j) (E j)

/-- The finite-distribution weighted sum of finite-prefix expected oracle-query counts for a
seed-indexed machine family. -/
noncomputable def workspaceMachineSeedExpectedQueries {d r : ℕ} {C : ℕ → Type*}
    (p : FinDist (Fin r)) (M : Fin r → WorkspaceMachine d C) (U : Operator d)
    (T : ℕ) (k : Fin r → ℕ) (c : (j : Fin r) → C (k j))
    (rho : (j : Fin r) → Operator (d*k j)) : ℝ :=
  ∑ j, p.prob j * workspaceMachineExpectedQueries (M j) U T (c j) (rho j)

/-- The extended nonnegative weighted sum of unbounded expected oracle-query counts for a finite
seed distribution. -/
noncomputable def workspaceMachineSeedInfiniteExpectedQueries {d r : ℕ} {C : ℕ → Type*}
    (p : FinDist (Fin r)) (M : Fin r → WorkspaceMachine d C) (U : Operator d)
    (k : Fin r → ℕ) (c : (j : Fin r) → C (k j))
    (rho : (j : Fin r) → Operator (d*k j)) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (p.prob j) * workspaceMachineInfiniteExpectedQueries (M j) U (c j) (rho j)

/-- For a finite seed distribution and nonnegative monotone prefix quantities, the weighted sum
of their extended nonnegative suprema equals the supremum of the weighted prefix sums. -/
private theorem workspace_seed_prefix_iSup {r : ℕ} (p : FinDist (Fin r))
    (f : Fin r → ℕ → ℝ) (hf : ∀ j T, 0 ≤ f j T) (hmono : ∀ j, Monotone (f j)) :
    (∑ j, ENNReal.ofReal (p.prob j) * ⨆ T, ENNReal.ofReal (f j T)) =
      ⨆ T, ENNReal.ofReal (∑ j, p.prob j * f j T) := by
  simp only [ENNReal.mul_iSup]
  have hm (j : Fin r) : Monotone (fun T : ℕ =>
      ENNReal.ofReal (p.prob j) * ENNReal.ofReal (f j T)) := by
    intro S T hST
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hmono j hST)) _
  rw [ENNReal.finsetSum_iSup_of_monotone (s := Finset.univ) hm]
  congr 1
  funext T
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.ofReal_mul (p.nonneg j)]
  · intro j _
    exact mul_nonneg (p.nonneg j) (hf j T)

/-- For finitely many oracles and event predicates, any strict thresholds below the seeded
unbounded halting masses are simultaneously exceeded at some common finite cutoff, assuming
positive semidefinite initial states. -/
theorem workspaceMachineSeedHaltMass_finite_approx {d r : ℕ} {C : ℕ → Type*}
    {J : Type*} [Fintype J] (p : FinDist (Fin r))
    (M : Fin r → WorkspaceMachine d C) (U : J → Operator d)
    (k : Fin r → ℕ) (c : (j : Fin r) → C (k j))
    (rho : (j : Fin r) → Operator (d*k j)) (hrho : ∀ j, (rho j).PosSemidef)
    (E : J → Fin r → (l : ℕ) → C l → Bool → List (ℕ×ℕ) → Bool)
    (threshold : J → ℝ≥0∞)
    (hthreshold : ∀ a, threshold a < workspaceMachineSeedInfiniteHaltMass
      p M (U a) k c rho (E a)) :
    ∃ T : ℕ, ∀ a, threshold a < ENNReal.ofReal
      (workspaceMachineSeedHaltMass p M (U a) T k c rho (E a)) := by
  have hsup (a : J) : workspaceMachineSeedInfiniteHaltMass p M (U a) k c rho (E a) =
      ⨆ T : ℕ, ENNReal.ofReal (workspaceMachineSeedHaltMass p M (U a) T k c rho (E a)) :=
    workspace_seed_prefix_iSup p
      (fun j T => workspaceMachineHaltMass (M j) (U a) T (c j) (rho j) (E a j))
      (fun j T => workspaceMachineHaltMass_nonneg (M j) (U a) T (c j) (rho j) (hrho j) (E a j))
      (fun j => workspaceMachineHaltMass_monotone (M j) (U a) (c j) (rho j) (hrho j) (E a j))
  have hchoose (a : J) : ∃ T : ℕ, threshold a < ENNReal.ofReal
      (workspaceMachineSeedHaltMass p M (U a) T k c rho (E a)) := by
    apply lt_iSup_iff.mp
    rw [← hsup a]
    exact hthreshold a
  choose cutoff hcutoff using hchoose
  let T := Finset.univ.sup cutoff
  refine ⟨T,fun a => (hcutoff a).trans_le ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (workspaceMachineHaltMass_monotone (M j) (U a) (c j) (rho j) (hrho j) (E a j)
      (Finset.le_sup (f := cutoff) (Finset.mem_univ a))) (p.nonneg j)

/-- For positive semidefinite seed-indexed initial states, the extended nonnegative
finite-prefix seeded expected query count is bounded by its unbounded counterpart. -/
theorem workspaceMachineSeedExpectedQueries_le_infinite {d r : ℕ} {C : ℕ → Type*}
    (p : FinDist (Fin r)) (M : Fin r → WorkspaceMachine d C) (U : Operator d)
    (T : ℕ) (k : Fin r → ℕ) (c : (j : Fin r) → C (k j))
    (rho : (j : Fin r) → Operator (d*k j)) (hrho : ∀ j, (rho j).PosSemidef) :
    ENNReal.ofReal (workspaceMachineSeedExpectedQueries p M U T k c rho) ≤
      workspaceMachineSeedInfiniteExpectedQueries p M U k c rho := by
  unfold workspaceMachineSeedExpectedQueries workspaceMachineSeedInfiniteExpectedQueries
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_le_sum
    intro j _
    rw [ENNReal.ofReal_mul (p.nonneg j)]
    exact mul_le_mul_right (workspaceMachineExpectedQueries_le_infinite (M j) U T (c j) (rho j)) _
  · intro j _
    exact mul_nonneg (p.nonneg j)
      (workspaceMachineExpectedQueries_nonneg (M j) U T (c j) (rho j) (hrho j))

/-- Replay a finite outcome record through classical machine control, returning the terminal
width, control state, and acceptance value only when halting occurs with no unused outcomes. -/
noncomputable def workspaceMachineReplay {d : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) :
    {k : ℕ} → ℕ → C k → List (ℕ×ℕ) → Option (Σ l : ℕ, C l × Bool)
  | _, 0, _, _ => none
  | k, T+1, c, rec => match M k c with
    | .halt b => if rec = [] then some ⟨k,c,b⟩ else none
    | .gate _ next => workspaceMachineReplay M T next rec
    | .query next => workspaceMachineReplay M T next rec
    | .instrument s _ _ next => match rec with
        | [] => none
        | (a,o)::tail => if a = s then
            if ho : o < s then workspaceMachineReplay M T (next ⟨o,ho⟩) tail else none
          else none

/-- Replaying the outcome record of a halted finite-prefix trace returns exactly its final
width, control state, and acceptance value. -/
theorem workspaceMachineReplay_correct {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) (t : WorkspaceMachineTrace d C)
    (ht : t ∈ workspaceMachineTraces M U T c rho) (hh : t.halted = true) :
    workspaceMachineReplay M T c t.outcomes = some ⟨t.width,t.control,t.accepted⟩ := by
  induction T generalizing k c rho t with
  | zero =>
    simp only [workspaceMachineTraces, List.mem_singleton] at ht
    subst t
    contradiction
  | succ T ih =>
    cases h : M k c with
    | halt b =>
      simp only [workspaceMachineTraces, h, List.mem_singleton] at ht
      subst t
      simp [workspaceMachineReplay, h]
    | gate G next =>
      simp only [workspaceMachineTraces, h] at ht
      simpa only [workspaceMachineReplay, h] using ih next _ t ht hh
    | query next =>
      simp only [workspaceMachineTraces, h] at ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      simpa only [workspaceMachineReplay, h] using ih next _ u hu hh
    | instrument s l I next =>
      simp only [workspaceMachineTraces, h, List.mem_flatten, List.mem_ofFn] at ht
      obtain ⟨xs,⟨o,rfl⟩,ht⟩ := ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      have hr := ih (next o) (I.branch o rho) u hu hh
      simpa [workspaceMachineReplay, h, o.isLt] using hr

/-- Decode the terminal data obtained by replaying an outcome record, returning zero if replay
fails. -/
noncomputable def workspaceMachineDecode {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (T : ℕ) (c : C k)
    (decode : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → ℝ) (rec : List (ℕ×ℕ)) : ℝ :=
  match workspaceMachineReplay M T c rec with
    | none => 0
    | some ⟨l,e,b⟩ => decode l e b rec

/-- Pointwise inequalities on the elements of a list imply the corresponding inequality between
mapped sums. -/
private theorem workspace_sum_map_mono {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- For a positive semidefinite initial state, the mass of halted machine traces whose decoded
scalar is within `epsilon` of `a` is bounded by the corresponding scalar-indicator statistic
of the unrolled circuit. -/
theorem workspaceMachineHaltMass_le_unroll_scalar {d k : ℕ} {C : ℕ → Type*}
    (M : WorkspaceMachine d C) (U : Operator d) (T : ℕ) (c : C k)
    (rho : Operator (d*k)) (hrho : rho.PosSemidef)
    (decode : (l : ℕ) → C l → Bool → List (ℕ×ℕ) → ℝ) (a epsilon : ℝ) :
    workspaceMachineHaltMass M U T c rho
      (fun l e b rec => decide (|decode l e b rec-a| ≤ epsilon)) ≤
    workspaceCircuitStatistic U (unrollWorkspaceMachine M T c) rho
      (fun _ rec => if |workspaceMachineDecode M T c decode rec-a| ≤ epsilon then 1 else 0) := by
  unfold workspaceCircuitStatistic
  rw [← unrollWorkspaceMachine_traces M U T c rho, List.map_map]
  unfold workspaceMachineHaltMass
  apply workspace_sum_map_mono
  intro t ht
  have hn : 0 ≤ workspaceMass t.toWorkspaceTrace :=
    (RCLike.nonneg_iff.mp (workspaceMachineTraces_posSemidef M U T c rho hrho t ht).trace_nonneg).1
  by_cases hh : t.halted = true
  · have hrec := workspaceMachineReplay_correct M U T c rho t ht hh
    simp [hh, workspaceMachineDecode, hrec, mul_ite]
  · simp only [Bool.and_eq_true, hh, false_and, ↓reduceIte]
    apply mul_nonneg hn
    split_ifs <;> norm_num

end Qatlib.Concepts.AdversaryBounds.AdvDuality
