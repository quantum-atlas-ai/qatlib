/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedEnvironmentStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance

/-!
# Purification of observed mixed executions

`observed_purification_traces` identifies mixed-state execution with the partial traces of a
pure execution on an extended space. The same correspondence preserves masses of events
determined by acceptance and outcomes, expected query counts, and the structural query budget.
These are finite-dimensional purification and partial trace identities in the framework of
[Watrous2018].

## Main statements

* `observed_purification_traces`: Reducing the extended pure traces gives the mixed traces.
* `observed_purification_event`: Classical event masses agree under reduction.
* `observed_purification_expected`: Expected query counts agree under reduction.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Foundations.PureStateMath.BornBridge


namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- Sums the masses of mixed execution traces whose acceptance flag and outcome history satisfy
the specified event. -/
noncomputable def mixedObservedEventMass {d : ℕ} (O : Operator d)
    (P : ObservedCircuit (Fin d)) (rho : Operator d)
    (event : Bool → List (ℕ × ℕ) → Bool) : ℝ :=
  ((observedMixedTraces O P rho).map
    (fun t => if event t.accepted t.outcomes then mixedMass t else 0)).sum

/-- Applying `G` on the system factor and then taking the partial trace of the pure outer
product equals conjugating the reduced operator by `G`. -/
private theorem purification_apply {d e : ℕ} (G : Operator d)
    (psi : QState (Fin d × Fin e)) :
    PartialTrace (outerProduct (ApplyGate (TensorGate G (1 : Operator e)) psi)) =
      conjBranch G (PartialTrace (outerProduct psi)) :=
  partialTrace_outerProduct_apply_tensorLeft d e G psi

/-- Tensoring `1 - G` with the environment identity equals the complement of `G` tensored with
that identity. -/
private theorem purification_complement {d e : ℕ} (G : Operator d) :
    TensorGate (1 - G) (1 : Operator e) =
      1 - TensorGate G (1 : Operator e) := by
  have h : TensorGate (1 - G) (1 : Operator e) =
      TensorGate (1 : Operator d) (1 : Operator e) -
        TensorGate G (1 : Operator e) := by
    funext x y
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    simp only [tensorGate_apply, Matrix.sub_apply, sub_mul]
  simpa only [tensorGate_one] using h

/-- The projector onto a system measurement fiber in the extended space is the tensor product of
the system fiber projector and the environment identity. -/
private theorem purification_label_projector {d e n : ℕ}
    (label : Fin d → Fin n) (o : Fin n) :
    Projector (Finset.univ.filter (fun x : Fin d × Fin e => label x.1 = o)) =
      TensorGate (Projector (Finset.univ.filter (fun i : Fin d => label i = o)))
        (1 : Operator e) := by
  funext x y
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [Projector, tensorGate_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Prod.mk.injEq, hij, hab]

/-- Collapsing a pure state onto a system measurement fiber and reducing the result equals
conjugating its reduced operator by the fiber projector. -/
private theorem purification_collapse {d e n : ℕ}
    (label : Fin d → Fin n) (o : Fin n) (psi : QState (Fin d × Fin e)) :
    PartialTrace (outerProduct
        (Collapse psi (Finset.univ.filter (fun x : Fin d × Fin e => label x.1 = o)))) =
      conjBranch (Projector (Finset.univ.filter (fun i : Fin d => label i = o)))
        (PartialTrace (outerProduct psi)) := by
  simpa only [Collapse, purification_label_projector] using
    purification_apply (Projector (Finset.univ.filter (fun i : Fin d => label i = o))) psi

/-- Reducing a pure projective branch in the extended space equals conjugating the reduced input
by `G` or `1 - G`, according to the outcome. -/
private theorem purification_project {d e : ℕ} (G : Operator d)
    (outcome : Bool) (psi : QState (Fin d × Fin e)) :
    PartialTrace (outerProduct (ProjectiveBranch (TensorGate G (1 : Operator e))
        outcome psi)) =
      conjBranch (if outcome then G else 1 - G) (PartialTrace (outerProduct psi)) := by
  cases outcome with
  | false =>
    change PartialTrace (outerProduct (ApplyGate (1 - TensorGate G (1 : Operator e)) psi)) =
      conjBranch (1 - G) (PartialTrace (outerProduct psi))
    rw [← purification_complement G]
    exact purification_apply (1 - G) psi
  | true => exact purification_apply G psi

/-- Reducing each trace of the environment-lifted pure execution gives exactly the mixed
execution traces of the reduced input operator. -/
theorem observed_purification_traces {d e : ℕ} (O : Operator d)
    (P : ObservedCircuit (Fin d)) (psi : QState (Fin d × Fin e)) :
    (observedTraces (TensorGate O (1 : Operator e))
      (liftObservedEnvironment (E := Fin e) P) psi).map reduceEnvironmentTrace =
      observedMixedTraces O P (PartialTrace (outerProduct psi)) := by
  induction P generalizing psi with
  | halt accepted => rfl
  | step s next ih =>
    cases s with
    | gate G =>
      have h := congrArg
        (fun ts : List (MixedBranchTrace d) =>
          ts.map (fun t => { t with gates := t.gates + 1 }))
        (ih (ApplyGate (TensorGate G (1 : Operator e)) psi))
      rw [purification_apply] at h
      simpa only [liftObservedEnvironment, observedTraces, observedMixedTraces,
        List.map_map, Function.comp_def, reduceEnvironmentTrace] using h
    | query =>
      have h := congrArg
        (fun ts : List (MixedBranchTrace d) =>
          ts.map (fun t => { t with queries := t.queries + 1 }))
        (ih (ApplyGate (TensorGate O (1 : Operator e)) psi))
      rw [purification_apply] at h
      simpa only [liftObservedEnvironment, observedTraces, observedMixedTraces,
        List.map_map, Function.comp_def, reduceEnvironmentTrace] using h
  | measure n label next ih =>
    simp only [liftObservedEnvironment, observedTraces, observedMixedTraces,
      List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext o
    have h := congrArg
      (fun ts : List (MixedBranchTrace d) =>
        ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (n, o.val) :: t.outcomes }))
      (ih o (Collapse psi
        (Finset.univ.filter (fun x : Fin d × Fin e => label x.1 = o))))
    rw [purification_collapse] at h
    simpa only [List.map_map, Function.comp_def, reduceEnvironmentTrace] using h
  | project G onFalse onTrue ihFalse ihTrue =>
    simp only [liftObservedEnvironment, observedTraces, observedMixedTraces, List.map_append]
    apply congrArg₂ List.append
    · have h := congrArg
        (fun ts : List (MixedBranchTrace d) =>
          ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (2, 0) :: t.outcomes }))
        (ihFalse (ProjectiveBranch (TensorGate G (1 : Operator e)) false psi))
      rw [purification_project] at h
      simpa only [List.map_map, Function.comp_def, reduceEnvironmentTrace] using! h
    · have h := congrArg
        (fun ts : List (MixedBranchTrace d) =>
          ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (2, 1) :: t.outcomes }))
        (ihTrue (ProjectiveBranch (TensorGate G (1 : Operator e)) true psi))
      rw [purification_project] at h
      simpa only [List.map_map, Function.comp_def, reduceEnvironmentTrace] using! h

/-- The mass of a reduced environment trace equals the squared norm mass of its pure state. -/
private theorem purification_mass {d e : ℕ} (t : BranchTrace (Fin d × Fin e)) :
    mixedMass (reduceEnvironmentTrace t) = branchMass t.state := by
  unfold mixedMass reduceEnvironmentTrace
  (try dsimp only)
  rw [trace_partialTrace, trace_outerProduct]
  simp only [Complex.ofReal_re]
  rfl

/-- Events depending on acceptance and outcome history have equal mass in the extended pure
execution and the mixed execution of its reduced input. -/
theorem observed_purification_event {d e : ℕ} (O : Operator d)
    (P : ObservedCircuit (Fin d)) (psi : QState (Fin d × Fin e))
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass (TensorGate O (1 : Operator e))
      (liftObservedEnvironment (E := Fin e) P) psi
      (fun t => event t.accepted t.outcomes) =
      mixedObservedEventMass O P (PartialTrace (outerProduct psi)) event := by
  unfold observedEventMass mixedObservedEventMass
  rw [← observed_purification_traces O P psi]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  refine List.map_congr_left fun t _ => ?_
  change (if event t.accepted t.outcomes then branchMass t.state else 0) =
    (if event t.accepted t.outcomes then mixedMass (reduceEnvironmentTrace t) else 0)
  rw [purification_mass]

/-- The extended pure execution and the mixed execution of its reduced input have the same
expected query count. -/
theorem observed_purification_expected {d e : ℕ} (O : Operator d)
    (P : ObservedCircuit (Fin d)) (psi : QState (Fin d × Fin e)) :
    expectedObservedQueries (TensorGate O (1 : Operator e))
      (liftObservedEnvironment (E := Fin e) P) psi =
      mixedExpectedQueries O P (PartialTrace (outerProduct psi)) := by
  rw [expectedObservedQueries_eq_sum]
  unfold mixedExpectedQueries
  rw [← observed_purification_traces O P psi]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  refine List.map_congr_left fun t _ => ?_
  change branchMass t.state * (t.queries : ℝ) =
    mixedMass (reduceEnvironmentTrace t) * (t.queries : ℝ)
  rw [purification_mass]

/-- Lifting an observed circuit to an additional environment preserves its structural query
budget. -/
theorem liftObservedEnvironment_budget
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (P : ObservedCircuit I) :
    observedQueryBudget (liftObservedEnvironment (E := E) P) = observedQueryBudget P := by
  induction P with
  | halt accepted => rfl
  | step s next ih =>
    cases s <;> simp only [liftObservedEnvironment, observedQueryBudget, ih]
  | measure n label next ih =>
    simp only [liftObservedEnvironment, observedQueryBudget, ih]
  | project G onFalse onTrue ihFalse ihTrue =>
    simp only [liftObservedEnvironment, observedQueryBudget, ihFalse, ihTrue]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
