/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit

/-!
# Instrument Machines and Infinite Query Costs

An `InstrumentMachine` assigns a halting, gate, query, or instrument instruction to each
classical control state. `instrumentMachineTraces` unfolds a finite number of instructions while
retaining unnormalized branch states, measurement records, operation counts, and endpoints. This
branch description uses quantum instruments and density operators as presented in [Watrous2018].

Finite halting masses and expected query costs form monotone families, while pending mass
decreases for well-formed machines and unitary oracles. Their suprema define
`instrumentMachineInfiniteHaltMass` and `instrumentMachineInfiniteExpectedQueries`, allowing
costs and success probabilities to be studied without a fixed running-time bound.

## Main statements

* `instrumentMachineTraces_posSemidef` and `instrumentMachineTraces_total` give positivity and
  conservation of trace mass.
* `instrumentMachineHaltMass_add_pending` partitions total mass into halted and pending
  branches.
* `instrumentMachineHaltMass_finite_approx` gives one finite cutoff for finitely many strict
  halting-mass thresholds.
* `instrumentMachineInfiniteExpectedQueries_le_iff` characterizes an infinite expected cost
  bound by all finite prefixes.

## References

* [Watrous, 2018][Watrous2018], The Theory of Quantum Information.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped ComplexOrder ENNReal

/-- An instruction for a classically controlled quantum machine: halt with an acceptance bit,
apply a gate, query the oracle, or branch on a finite quantum instrument outcome. -/
inductive InstrumentInstruction (D : ℕ) (C : Type*) where
  | halt (accepted : Bool)
  | gate (G : Operator D) (next : C)
  | query (next : C)
  | instrument (s : ℕ) (I : Instrument (Fin s) D D) (next : Fin s → C)

/-- A quantum instrument machine assigning an instruction to each classical control state. -/
abbrev InstrumentMachine (D : ℕ) (C : Type*) := C → InstrumentInstruction D C

/-- Every gate instruction of the machine uses a unitary operator; the other instruction forms
impose no additional condition. -/
def instrumentMachineWellFormed {D : ℕ} {C : Type*} (M : InstrumentMachine D C) : Prop :=
  ∀ c, match M c with
    | .gate G _ => G ∈ Matrix.unitaryGroup (Fin D) ℂ
    | _ => True

/-- The final classical control state of an execution prefix together with a flag indicating
whether that prefix has halted. -/
structure InstrumentMachineEndpoint (C : Type*) where
  control : C
  halted : Bool

/-- A mixed-state branch trace augmented with its classical control endpoint and halting flag. -/
structure InstrumentMachineTrace (D : ℕ) (C : Type*) extends MixedBranchTrace D where
  endpoint : InstrumentMachineEndpoint C

/-- Unfolds the machine for at most `T` instructions, retaining halted branches and marking
unfinished endpoints when fuel is exhausted. Instrument outcomes produce separate
unnormalized branch states and records. -/
noncomputable def instrumentMachineTraces {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) :
    ℕ → C → Operator D → List (InstrumentMachineTrace D C)
  | 0, c, rho => [⟨⟨rho, false, 0, 0, 0, []⟩, ⟨c, false⟩⟩]
  | T+1, c, rho => match M c with
    | .halt b => [⟨⟨rho, b, 0, 0, 0, []⟩, ⟨c, true⟩⟩]
    | .gate G next =>
        (instrumentMachineTraces M O T next (conjBranch G rho)).map fun t =>
          {t with gates := t.gates + 1}
    | .query next =>
        (instrumentMachineTraces M O T next (conjBranch O rho)).map fun t =>
          {t with queries := t.queries + 1}
    | .instrument s I next =>
        (List.ofFn fun o : Fin s =>
          (instrumentMachineTraces M O T (next o) (I.branch o rho)).map fun t =>
            {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s,o.val) :: t.outcomes}).flatten

/-- The total branch mass of execution prefixes that have halted within `T` instructions and
satisfy the event on the final control state, acceptance bit, and measurement record. -/
noncomputable def instrumentMachineHaltMass {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) : ℝ :=
  ((instrumentMachineTraces M O T c rho).map fun t =>
    if t.endpoint.halted && event t.endpoint.control t.accepted t.outcomes then
      mixedMass t.toMixedBranchTrace else 0).sum

/-- The total branch mass of execution prefixes still pending after `T` instructions. -/
noncomputable def instrumentMachinePendingMass {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) : ℝ :=
  ((instrumentMachineTraces M O T c rho).map fun t =>
    if t.endpoint.halted then 0 else mixedMass t.toMixedBranchTrace).sum

/-- The sum of each execution prefix's query count weighted by its unnormalized branch mass,
including both halted and pending prefixes. -/
noncomputable def instrumentMachineExpectedQueries {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) : ℝ :=
  ((instrumentMachineTraces M O T c rho).map fun t =>
    mixedMass t.toMixedBranchTrace * t.queries).sum

/-- Every branch state in a finite machine execution is positive semidefinite when the initial
state is positive semidefinite. -/
theorem instrumentMachineTraces_posSemidef {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (t : InstrumentMachineTrace D C)
    (ht : t ∈ instrumentMachineTraces M O T c rho) : t.state.PosSemidef := by
  induction T generalizing c rho t with
  | zero =>
    simp only [instrumentMachineTraces, List.mem_singleton] at ht
    subst t
    exact hrho
  | succ T ih =>
    cases h : M c with
    | halt b =>
      simp only [instrumentMachineTraces, h, List.mem_singleton] at ht
      subst t
      exact hrho
    | gate G next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact ih next _ ((completelyPositive_conjBranch G).positive hrho) u hu
    | query next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact ih next _ ((completelyPositive_conjBranch O).positive hrho) u hu
    | instrument s I next =>
      simp only [instrumentMachineTraces, h, List.mem_flatten, List.mem_ofFn] at ht
      obtain ⟨xs,⟨o,rfl⟩,ht⟩ := ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih (next o) _ ((I.cp o).positive hrho) u hu

/-- The pending mass of a finite machine execution is nonnegative for a positive semidefinite
initial state. -/
theorem instrumentMachinePendingMass_nonneg {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) : 0 ≤ instrumentMachinePendingMass M O T c rho := by
  unfold instrumentMachinePendingMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact le_rfl
  · exact (RCLike.nonneg_iff.mp
      (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1

/-- The expected query count of a finite machine execution is nonnegative for a positive
semidefinite initial state. -/
theorem instrumentMachineExpectedQueries_nonneg {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) : 0 ≤ instrumentMachineExpectedQueries M O T c rho := by
  unfold instrumentMachineExpectedQueries
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg ((RCLike.nonneg_iff.mp
    (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1)
    (Nat.cast_nonneg _)

/-- For a well-formed machine and a unitary oracle, the masses of all finite execution branches
sum to the real part of the initial trace. -/
theorem instrumentMachineTraces_total {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) :
    ((instrumentMachineTraces M O T c rho).map fun t => mixedMass t.toMixedBranchTrace).sum =
      (trace rho).re := by
  induction T generalizing c rho with
  | zero => simp [instrumentMachineTraces, mixedMass]
  | succ T ih =>
    cases h : M c with
    | halt b => simp [instrumentMachineTraces, h, mixedMass]
    | gate G next =>
      have hG : G ∈ Matrix.unitaryGroup (Fin D) ℂ := by
        simpa [instrumentMachineWellFormed, h] using hM c
      simpa only [instrumentMachineTraces, h, List.map_map, Function.comp_def] using!
        (ih next (conjBranch G rho)).trans (congrArg Complex.re (trace_conjBranch_unitary G hG rho))
    | query next =>
      simpa only [instrumentMachineTraces, h, List.map_map, Function.comp_def] using!
        (ih next (conjBranch O rho)).trans (congrArg Complex.re (trace_conjBranch_unitary O hO rho))
    | instrument s I next =>
      simp only [instrumentMachineTraces, h, List.map_flatten, List.sum_flatten,
        List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def]
      change (∑ o : Fin s, ((instrumentMachineTraces M O T (next o) (I.branch o rho)).map
        fun t => mixedMass t.toMixedBranchTrace).sum) = (trace rho).re
      simp_rw [ih]
      exact sum_instrumentProb I rho

/-- Gives the one-instruction recurrence for pending mass, propagating through gates and queries
and summing over instrument outcomes. -/
theorem instrumentMachinePendingMass_succ {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    instrumentMachinePendingMass M O (T+1) c rho = match M c with
      | .halt _ => 0
      | .gate G next => instrumentMachinePendingMass M O T next (conjBranch G rho)
      | .query next => instrumentMachinePendingMass M O T next (conjBranch O rho)
      | .instrument s I next => ∑ o : Fin s,
          instrumentMachinePendingMass M O T (next o) (I.branch o rho) := by
  cases h : M c <;>
    simp [instrumentMachinePendingMass, instrumentMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, mixedMass]

/-- The sum of the pointwise addition of two real-valued list maps equals the sum of their
separate mapped sums. -/
private theorem machine_sum_map_add {A : Type*} (xs : List A) (f g : A → ℝ) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, add_left_comm]

/-- Gives the one-instruction recurrence for expected query cost of a well-formed machine with a
unitary oracle. A query contributes the real part of the current state's trace in addition
to the continuation cost. -/
theorem instrumentMachineExpectedQueries_succ {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) :
    instrumentMachineExpectedQueries M O (T+1) c rho = match M c with
      | .halt _ => 0
      | .gate G next => instrumentMachineExpectedQueries M O T next (conjBranch G rho)
      | .query next => (trace rho).re +
          instrumentMachineExpectedQueries M O T next (conjBranch O rho)
      | .instrument s I next => ∑ o : Fin s,
          instrumentMachineExpectedQueries M O T (next o) (I.branch o rho) := by
  cases h : M c with
  | halt b => simp [instrumentMachineExpectedQueries, instrumentMachineTraces, h]
  | gate G next =>
    simp [instrumentMachineExpectedQueries, instrumentMachineTraces, h, Function.comp_def,
        mixedMass]
  | instrument s I next =>
    simp [instrumentMachineExpectedQueries, instrumentMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, mixedMass]
  | query next =>
    simp only [instrumentMachineExpectedQueries, instrumentMachineTraces, h, List.map_map,
      Function.comp_def, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    rw [machine_sum_map_add]
    change instrumentMachineExpectedQueries M O T next (conjBranch O rho) +
      ((instrumentMachineTraces M O T next (conjBranch O rho)).map
        fun t => mixedMass t.toMixedBranchTrace).sum = _
    rw [instrumentMachineTraces_total M hM O hO, trace_conjBranch_unitary O hO]
    exact add_comm _ _

/-- Pointwise domination on a list implies domination of the sums of the corresponding
real-valued maps. -/
private theorem machine_sum_map_mono {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- For a well-formed machine, a unitary oracle, and a positive semidefinite input, pending mass
is at most the real part of the initial trace. -/
theorem instrumentMachinePendingMass_le_trace {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) (hrho : rho.PosSemidef) :
    instrumentMachinePendingMass M O T c rho ≤ (trace rho).re := by
  calc
    _ ≤ ((instrumentMachineTraces M O T c rho).map
        fun t => mixedMass t.toMixedBranchTrace).sum := by
      apply machine_sum_map_mono
      intro t ht
      split_ifs
      · exact (RCLike.nonneg_iff.mp
          (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1
      · exact le_rfl
    _ = _ := instrumentMachineTraces_total M hM O hO T c rho

/-- The mass of any halted event in a finite execution is nonnegative for a positive
semidefinite initial state. -/
theorem instrumentMachineHaltMass_nonneg {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (event : C → Bool → List (ℕ×ℕ) → Bool) :
    0 ≤ instrumentMachineHaltMass M O T c rho event := by
  unfold instrumentMachineHaltMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (RCLike.nonneg_iff.mp
      (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1
  · exact le_rfl

/-- Gives the one-instruction recurrence for halted-event mass, prepending each instrument
outcome to the event's measurement record. -/
theorem instrumentMachineHaltMass_succ {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) :
    instrumentMachineHaltMass M O (T+1) c rho event = match M c with
      | .halt b => if event c b [] then (trace rho).re else 0
      | .gate G next => instrumentMachineHaltMass M O T next (conjBranch G rho) event
      | .query next => instrumentMachineHaltMass M O T next (conjBranch O rho) event
      | .instrument s I next => ∑ o : Fin s,
          instrumentMachineHaltMass M O T (next o) (I.branch o rho)
            (fun c b rec => event c b ((s,o.val)::rec)) := by
  cases h : M c <;>
    simp [instrumentMachineHaltMass, instrumentMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, mixedMass]

/-- For a positive semidefinite initial state, the mass of a fixed halted event is nondecreasing
as execution fuel increases. -/
theorem instrumentMachineHaltMass_monotone {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (event : C → Bool → List (ℕ×ℕ) → Bool) :
    Monotone (fun T => instrumentMachineHaltMass M O T c rho event) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing c rho event with
  | zero =>
    simpa only [instrumentMachineHaltMass, instrumentMachineTraces, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, add_zero] using instrumentMachineHaltMass_nonneg M O 1 c rho hrho event
  | succ T ih =>
    rw [instrumentMachineHaltMass_succ, instrumentMachineHaltMass_succ]
    cases h : M c with
    | halt b => exact le_rfl
    | gate G next => exact ih next _ ((completelyPositive_conjBranch G).positive hrho) event
    | query next => exact ih next _ ((completelyPositive_conjBranch O).positive hrho) event
    | instrument s I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)
        (fun c b rec => event c b ((s,o.val)::rec))

/-- For a well-formed machine and a unitary oracle, the mass of all halted prefixes plus pending
mass equals the real part of the initial trace. -/
theorem instrumentMachineHaltMass_add_pending {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) :
    instrumentMachineHaltMass M O T c rho (fun _ _ _ => true) +
      instrumentMachinePendingMass M O T c rho = (trace rho).re := by
  unfold instrumentMachineHaltMass instrumentMachinePendingMass
  rw [← machine_sum_map_add]
  have hsum : ((instrumentMachineTraces M O T c rho).map fun t =>
      (if t.endpoint.halted && true then mixedMass t.toMixedBranchTrace else 0) +
      (if t.endpoint.halted then 0 else mixedMass t.toMixedBranchTrace)) =
      (instrumentMachineTraces M O T c rho).map (fun t => mixedMass t.toMixedBranchTrace) := by
    apply List.map_congr_left
    intro t ht
    cases h : t.endpoint.halted <;> simp [h]
  rw [hsum]
  exact instrumentMachineTraces_total M hM O hO T c rho

/-- For a well-formed machine with a unitary oracle and positive semidefinite input, pending
mass is nonincreasing as execution fuel grows. -/
theorem instrumentMachinePendingMass_antitone {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (c : C) (rho : Operator D) (hrho : rho.PosSemidef) :
    Antitone (fun T => instrumentMachinePendingMass M O T c rho) := by
  apply antitone_nat_of_succ_le
  intro T
  induction T generalizing c rho with
  | zero =>
    simpa only [instrumentMachinePendingMass, instrumentMachineTraces,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Bool.false_eq_true,
      ↓reduceIte, add_zero, mixedMass] using
        instrumentMachinePendingMass_le_trace M hM O hO 1 c rho hrho
  | succ T ih =>
    rw [instrumentMachinePendingMass_succ, instrumentMachinePendingMass_succ]
    cases h : M c with
    | halt b => exact le_rfl
    | gate G next =>
      exact ih next _ ((completelyPositive_conjBranch G).positive hrho)
    | query next =>
      exact ih next _ ((completelyPositive_conjBranch O).positive hrho)
    | instrument s I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)

/-- For a well-formed machine with a unitary oracle and positive semidefinite input, finite
expected query cost is nondecreasing in execution fuel. -/
theorem instrumentMachineExpectedQueries_monotone {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (c : C) (rho : Operator D) (hrho : rho.PosSemidef) :
    Monotone (fun T => instrumentMachineExpectedQueries M O T c rho) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing c rho with
  | zero =>
    simpa only [instrumentMachineExpectedQueries, instrumentMachineTraces,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_zero,
      mul_zero, add_zero] using instrumentMachineExpectedQueries_nonneg M O 1 c rho hrho
  | succ T ih =>
    rw [instrumentMachineExpectedQueries_succ M hM O hO,
      instrumentMachineExpectedQueries_succ M hM O hO]
    cases h : M c with
    | halt b => exact le_rfl
    | gate G next =>
      exact ih next _ ((completelyPositive_conjBranch G).positive hrho)
    | query next =>
      exact add_le_add le_rfl (ih next _ ((completelyPositive_conjBranch O).positive hrho))
    | instrument s I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)

/-- The extended nonnegative halting-event mass defined as the supremum of its finite-fuel
masses after applying `ENNReal.ofReal`. -/
noncomputable def instrumentMachineInfiniteHaltMass {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) : ℝ≥0∞ :=
  ⨆ T : ℕ, ENNReal.ofReal (instrumentMachineHaltMass M O T c rho event)

/-- For finitely many oracles and halted events, strict thresholds below their infinite halting
masses are all exceeded at one common finite execution cutoff. -/
theorem instrumentMachineHaltMass_finite_approx {D : ℕ} {C J : Type*} [Fintype J]
    (M : InstrumentMachine D C) (O : J → Operator D) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (event : J → C → Bool → List (ℕ×ℕ) → Bool)
    (threshold : J → ℝ≥0∞)
    (hthreshold : ∀ j, threshold j < instrumentMachineInfiniteHaltMass M (O j) c rho (event j)) :
    ∃ T : ℕ, ∀ j, threshold j < ENNReal.ofReal (instrumentMachineHaltMass M (O j) T c rho (event j)) := by
  classical
  have hchoose (j : J) : ∃ T : ℕ, threshold j <
      ENNReal.ofReal (instrumentMachineHaltMass M (O j) T c rho (event j)) := by
    exact lt_iSup_iff.mp (hthreshold j)
  choose cutoff hcutoff using hchoose
  let T := Finset.univ.sup cutoff
  refine ⟨T, fun j => (hcutoff j).trans_le ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact instrumentMachineHaltMass_monotone M (O j) c rho hrho (event j)
    (Finset.le_sup (f := cutoff) (Finset.mem_univ j))

/-- The infinite expected query cost, defined in extended nonnegative reals as the supremum of
the finite-fuel expected query costs. -/
noncomputable def instrumentMachineInfiniteExpectedQueries {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D) : ℝ≥0∞ :=
  ⨆ T : ℕ, ENNReal.ofReal (instrumentMachineExpectedQueries M O T c rho)

/-- Every finite-fuel expected query cost, mapped by `ENNReal.ofReal`, is bounded by the
infinite expected query cost. -/
theorem instrumentMachineExpectedQueries_le_infinite {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    ENNReal.ofReal (instrumentMachineExpectedQueries M O T c rho) ≤
      instrumentMachineInfiniteExpectedQueries M O c rho := by
  unfold instrumentMachineInfiniteExpectedQueries
  exact le_iSup (fun S => ENNReal.ofReal (instrumentMachineExpectedQueries M O S c rho)) T

/-- An extended nonnegative bound holds for the infinite expected query cost exactly when it
holds for every finite-fuel expected query cost. -/
theorem instrumentMachineInfiniteExpectedQueries_le_iff {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D) (Q : ℝ≥0∞) :
    instrumentMachineInfiniteExpectedQueries M O c rho ≤ Q ↔
      ∀ T : ℕ, ENNReal.ofReal (instrumentMachineExpectedQueries M O T c rho) ≤ Q :=
  iSup_le_iff

end Qatlib.Concepts.AdversaryBounds.AdvDuality
