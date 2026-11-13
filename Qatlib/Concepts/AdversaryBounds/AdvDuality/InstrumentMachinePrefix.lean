/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachine

/-!
# Finite Circuit Prefixes of Instrument Machines

`unrollInstrumentMachine` turns a bounded execution of an instrument machine into an
`InstrumentCircuit`, using a false halt at the time boundary. `instrumentMachineReplay` recovers
the control endpoint and its halted flag from a valid outcome record, preserving the distinction
between an actual halt and an exhausted time budget. This connects machine execution with the
quantum circuit and measurement formalism described in [NielsenChuang2010].

The trace correspondence retains branch states, outcomes, and resource counters. Replay then
transports endpoint-dependent statistics, halted event mass, pending mass, and expected query
counts between the two representations.

## Main statements

- `unrollInstrumentMachine_wellFormed` preserves well-formedness.
* `unrollInstrumentMachine_traces` and `unrollInstrumentMachine_annotated` identify the trace
  lists before and after replay.
- `unrollInstrumentMachine_statistic` transports arbitrary complex-valued trace statistics.
* `unrollInstrumentMachine_expected`, `unrollInstrumentMachine_event`, and
  `unrollInstrumentMachine_pending` transport the corresponding quantitative observables.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010], *Quantum Computation and Quantum Information*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.CircuitCompile

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix

/-- Unroll at most the given number of machine instructions into a finite instrument circuit,
replacing an exhausted time budget by a false halt. -/
noncomputable def unrollInstrumentMachine {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) : ℕ → C → InstrumentCircuit D
  | 0, _ => .halt false
  | T+1, c => match M c with
    | .halt b => .halt b
    | .gate G next => .step (.gate G) (unrollInstrumentMachine M T next)
    | .query next => .step .query (unrollInstrumentMachine M T next)
    | .instrument s I next => .instrument s I (fun o => unrollInstrumentMachine M T (next o))

/-- Replay a bounded machine execution from its instrument outcome record to recover its control
endpoint and halted flag. Return `none` for a record whose arities, outcomes, or length do
not fit the execution. -/
def instrumentMachineReplay {D : ℕ} {C : Type*} (M : InstrumentMachine D C) :
    ℕ → C → List (ℕ×ℕ) → Option (InstrumentMachineEndpoint C)
  | 0, c, [] => some ⟨c, false⟩
  | 0, _, _::_ => none
  | T+1, c, record => match M c with
    | .halt _ => match record with
      | [] => some ⟨c, true⟩
      | _::_ => none
    | .gate _ next => instrumentMachineReplay M T next record
    | .query next => instrumentMachineReplay M T next record
    | .instrument s _ next => match record with
      | [] => none
      | (arity,a)::rest => if h : arity = s ∧ a < s then
          instrumentMachineReplay M T (next ⟨a,h.2⟩) rest
        else none

/-- Every finite unrolling of a well-formed instrument machine is a well-formed instrument
circuit. -/
theorem unrollInstrumentMachine_wellFormed {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M) (T : ℕ) (c : C) :
    instrumentCircuitWellFormed (unrollInstrumentMachine M T c) := by
  induction T generalizing c with
  | zero => trivial
  | succ T ih =>
    cases h : M c with
    | halt b => simp [unrollInstrumentMachine, h, instrumentCircuitWellFormed]
    | gate G next =>
      simp only [unrollInstrumentMachine, h, instrumentCircuitWellFormed]
      exact ⟨by simpa [instrumentMachineWellFormed, h] using hM c, ih next⟩
    | query next =>
      simpa only [unrollInstrumentMachine, h, instrumentCircuitWellFormed] using ih next
    | instrument s I next =>
      simpa only [unrollInstrumentMachine, h, instrumentCircuitWellFormed] using
          fun o => ih (next o)

/-- Forgetting the control endpoints of the bounded machine traces gives exactly the mixed
branch traces of the unrolled circuit. -/
theorem unrollInstrumentMachine_traces {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    (instrumentMachineTraces M O T c rho).map InstrumentMachineTrace.toMixedBranchTrace =
      instrumentCircuitMixedTraces O (unrollInstrumentMachine M T c) rho := by
  induction T generalizing c rho with
  | zero => rfl
  | succ T ih =>
    cases h : M c with
    | halt b => simp [instrumentMachineTraces, unrollInstrumentMachine, h,
        instrumentCircuitMixedTraces]
    | gate G next =>
      simpa only [instrumentMachineTraces, unrollInstrumentMachine, h,
        instrumentCircuitMixedTraces, List.map_map, Function.comp_def] using
        congrArg (List.map (fun t : MixedBranchTrace D => {t with gates := t.gates+1}))
          (ih next (conjBranch G rho))
    | query next =>
      simpa only [instrumentMachineTraces, unrollInstrumentMachine, h,
        instrumentCircuitMixedTraces, List.map_map, Function.comp_def] using
        congrArg (List.map (fun t : MixedBranchTrace D => {t with queries := t.queries+1}))
          (ih next (conjBranch O rho))
    | instrument s I next =>
      simp only [instrumentMachineTraces, unrollInstrumentMachine, h,
        instrumentCircuitMixedTraces, List.map_flatten, List.map_ofFn,
        List.map_map, Function.comp_def]
      congr 1
      apply congrArg List.ofFn
      funext o
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun t : MixedBranchTrace D =>
          {t with gates := t.gates+2, measurements := t.measurements+1, outcomes := (s,o.val)::t.outcomes})) (ih (next o) (I.branch o rho))

/-- Replaying the outcome record of any bounded machine trace recovers that trace's endpoint. -/
theorem instrumentMachineReplay_correct {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (t : InstrumentMachineTrace D C) (ht : t ∈ instrumentMachineTraces M O T c rho) :
    instrumentMachineReplay M T c t.outcomes = some t.endpoint := by
  induction T generalizing c rho t with
  | zero =>
    simp only [instrumentMachineTraces, List.mem_singleton] at ht
    subst t
    rfl
  | succ T ih =>
    cases h : M c with
    | halt b =>
      simp only [instrumentMachineTraces, h, List.mem_singleton] at ht
      subst t
      simp [instrumentMachineReplay, h]
    | gate G next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      simpa only [instrumentMachineReplay, h] using ih next (conjBranch G rho) u hu
    | query next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      simpa only [instrumentMachineReplay, h] using ih next (conjBranch O rho) u hu
    | instrument s I next =>
      simp only [instrumentMachineTraces, h, List.mem_flatten, List.mem_ofFn] at ht
      obtain ⟨xs,⟨o,rfl⟩,ht⟩ := ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      simpa only [instrumentMachineReplay, h, Fin.isLt, and_self, ↓reduceDIte] using
        ih (next o) (I.branch o rho) u hu

/-- Annotating each unrolled circuit trace with the endpoint recovered by replay produces
exactly the bounded machine trace list, with every replay successful. -/
theorem unrollInstrumentMachine_annotated {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    ((instrumentCircuitMixedTraces O (unrollInstrumentMachine M T c) rho).map fun t =>
      match instrumentMachineReplay M T c t.outcomes with
      | none => none
      | some e => some (⟨t,e⟩ : InstrumentMachineTrace D C)) =
      (instrumentMachineTraces M O T c rho).map some := by
  rw [← unrollInstrumentMachine_traces M O T c rho]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro t ht
  rw [instrumentMachineReplay_correct M O T c rho t ht]

/-- The sum of any complex-valued statistic of endpoints, branch data, resource counters,
outcomes, and states agrees between machine traces and circuit traces annotated by replay,
using zero when replay fails. -/
theorem unrollInstrumentMachine_statistic {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (F : C → Bool → Bool → ℕ → ℕ → ℕ → List (ℕ×ℕ) → Operator D → ℂ) :
    ((instrumentMachineTraces M O T c rho).map fun t =>
      F t.endpoint.control t.endpoint.halted t.accepted t.queries t.gates t.measurements
        t.outcomes t.state).sum =
    ((instrumentCircuitMixedTraces O (unrollInstrumentMachine M T c) rho).map fun t =>
      match instrumentMachineReplay M T c t.outcomes with
      | none => 0
      | some e => F e.control e.halted t.accepted t.queries t.gates t.measurements
          t.outcomes t.state).sum := by
  rw [← unrollInstrumentMachine_traces M O T c rho]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [instrumentMachineReplay_correct M O T c rho t ht]

/-- The unrolled circuit and the bounded machine execution have equal expected query counts. -/
theorem unrollInstrumentMachine_expected {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    instrumentCircuitExpectedQueries O (unrollInstrumentMachine M T c) rho =
      instrumentMachineExpectedQueries M O T c rho := by
  rw [instrumentCircuitExpectedQueries, ← unrollInstrumentMachine_traces M O T c rho]
  simp only [instrumentMachineExpectedQueries, List.map_map, Function.comp_def]

/-- An unrolled circuit event selected by a replayed halted endpoint has exactly the
corresponding halted machine event mass. -/
theorem unrollInstrumentMachine_event {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) :
    instrumentCircuitEventMass O (unrollInstrumentMachine M T c) rho
      (fun b rec => match instrumentMachineReplay M T c rec with
        | none => false
        | some e => e.halted && event e.control b rec) =
      instrumentMachineHaltMass M O T c rho event := by
  rw [instrumentCircuitEventMass, ← unrollInstrumentMachine_traces M O T c rho]
  simp only [instrumentMachineHaltMass, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [instrumentMachineReplay_correct M O T c rho t ht]

/-- The unrolled circuit event whose replayed endpoint has not halted has exactly the bounded
machine's pending mass. -/
theorem unrollInstrumentMachine_pending {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    instrumentCircuitEventMass O (unrollInstrumentMachine M T c) rho
      (fun _ rec => match instrumentMachineReplay M T c rec with
        | none => false
        | some e => !e.halted) = instrumentMachinePendingMass M O T c rho := by
  rw [instrumentCircuitEventMass, ← unrollInstrumentMachine_traces M O T c rho]
  simp only [instrumentMachinePendingMass, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [instrumentMachineReplay_correct M O T c rho t ht]
  cases h : t.endpoint.halted <;> simp [h]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
