/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedEnvironment
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedEvent
import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Tactic.SimpRw

/-!
# Statistics of hidden oracle mixtures

This module evaluates an observed circuit coupled to `hiddenTableOracle` from a product input
`TensorState psi gamma`. It shows that statistics visible through acceptance, query counts, and
outcomes are sums of the individual oracle statistics weighted by the squared moduli of the
environment amplitudes. For normalized environment states these are mixture weights, in the
sense of [Watrous2018].

`hidden_weighted_average` supplies the common calculation, using linearity of branch states and
decomposition of mass into environment slices. The public results specialize it to expected
queries and metadata events.

## Main statements

* `hidden_weighted_average` decomposes a general mass-weighted metadata statistic over oracle
  blocks.
* `observed_hiddenTable_expected_average` gives the weighted sum formula for expected query
  counts.
* `observed_hiddenTable_event_average` gives the corresponding formula for event mass.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

section Helpers

variable {I E : Type*}

/-- Multiplies a branch state by a complex scalar while retaining its classical trace fields. -/
private def scaleTrace (c : ℂ) (t : BranchTrace I) : BranchTrace I :=
  { t with state := c • t.state }

variable [Fintype I] [DecidableEq I]

/-- Scaling the input state scales every terminal branch state by the same scalar and leaves the
trace metadata unchanged. -/
private theorem traces_smul (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi : QState I) (c : ℂ) :
    observedTraces O P (c • psi) = (observedTraces O P psi).map (scaleTrace c) := by
  have hgate (G : Matrix I I ℂ) (v : QState I) :
      ApplyGate G (c • v) = c • ApplyGate G v := Matrix.mulVec_smul G c v
  have hcollapse (v : QState I) (S : Finset I) :
      Collapse (c • v) S = c • Collapse v S := hgate (Projector S) v
  have hproject (Q : Matrix I I ℂ) (b : Bool) (v : QState I) :
      ProjectiveBranch Q b (c • v) = c • ProjectiveBranch Q b v := hgate _ v
  induction P generalizing psi with
  | halt accepted => rfl
  | step s next ih =>
      cases s with
      | gate G =>
          simpa only [observedTraces, hgate, List.map_map, Function.comp_def,
            scaleTrace] using! congrArg
              (fun ts : List (BranchTrace I) =>
                ts.map (fun t => { t with gates := t.gates + 1 }))
              (ih (ApplyGate G psi))
      | query =>
          simpa only [observedTraces, hgate, List.map_map, Function.comp_def,
            scaleTrace] using! congrArg
              (fun ts : List (BranchTrace I) =>
                ts.map (fun t => { t with queries := t.queries + 1 }))
              (ih (ApplyGate O psi))
  | measure n label next ih =>
      simp only [observedTraces, List.map_flatten, List.map_ofFn]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext o
      simpa only [hcollapse, List.map_map, Function.comp_def, scaleTrace] using!
        congrArg
          (fun ts : List (BranchTrace I) => ts.map (fun t =>
            { t with measurements := t.measurements + 1, outcomes := (n, o.val) :: t.outcomes }))
          (ih o (Collapse psi (Finset.univ.filter (fun i => label i = o))))
  | project Q onFalse onTrue ihFalse ihTrue =>
      simpa only [observedTraces, hproject, List.map_append, List.map_map,
        Function.comp_def, scaleTrace] using! congrArg₂ List.append
          (congrArg
            (fun ts : List (BranchTrace I) => ts.map (fun t =>
              { t with measurements := t.measurements + 1, outcomes := (2, 0) :: t.outcomes }))
            (ihFalse (ProjectiveBranch Q false psi)))
          (congrArg
            (fun ts : List (BranchTrace I) => ts.map (fun t =>
              { t with measurements := t.measurements + 1, outcomes := (2, 1) :: t.outcomes }))
            (ihTrue (ProjectiveBranch Q true psi)))

/-- Scaling a branch state by a complex scalar multiplies its mass by the scalar's squared
modulus. -/
private theorem mass_smul (c : ℂ) (psi : QState I) :
    branchMass (c • psi) = Complex.normSq c * branchMass psi := by
  simpa only [branchMass, Complex.normSq_eq_norm_sq] using!
    measureProb_smul c psi Finset.univ

variable [Fintype E] [DecidableEq E]

/-- The mass of a product-register state is the sum of the masses of its fixed environment
slices. -/
private theorem mass_slices (psi : QState (I × E)) :
    branchMass psi = ∑ a, branchMass (fun i => psi (i, a)) := by
  simp only [branchMass, MeasureProb, BornProb, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Interchanges a list sum with a finite sum over environment coordinates. -/
private theorem list_sum_finset_sum {A : Type*} (xs : List A) (f : A → E → ℝ) :
    (xs.map (fun x => ∑ a, f x a)).sum =
      ∑ a, (xs.map (fun x => f x a)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- For a product input, any branch mass statistic weighted by acceptance, query count, and
outcomes decomposes over the hidden oracle blocks with weights `Complex.normSq (gamma a)`. -/
private theorem hidden_weighted_average (O : E → Matrix I I ℂ)
    (P : ObservedCircuit I) (psi : QState I) (gamma : QState E)
    (weight : Bool → ℕ → List (ℕ × ℕ) → ℝ) :
    ((observedTraces (hiddenTableOracle O) (liftObservedEnvironment (E := E) P)
      (TensorState psi gamma)).map (fun t =>
        branchMass t.state * weight t.accepted t.queries t.outcomes)).sum =
      ∑ a, Complex.normSq (gamma a) *
        ((observedTraces (O a) P psi).map (fun t =>
          branchMass t.state * weight t.accepted t.queries t.outcomes)).sum := by
  calc
    _ = ∑ a, (((observedTraces (hiddenTableOracle O)
          (liftObservedEnvironment (E := E) P) (TensorState psi gamma)).map
          (sliceEnvironmentTrace a)).map (fun t =>
            branchMass t.state * weight t.accepted t.queries t.outcomes)).sum := by
      simp only [List.map_map, Function.comp_def, sliceEnvironmentTrace]
      simp_rw [mass_slices, Finset.sum_mul]
      exact list_sum_finset_sum _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [observed_hiddenTable_slices]
      have hs : (fun i => TensorState psi gamma (i, a)) = gamma a • psi := by
        funext i
        simp only [TensorState, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [hs, traces_smul]
      simp only [List.map_map, Function.comp_def, scaleTrace, mass_smul, mul_assoc]
      exact List.sum_map_mul_left _ _ _

end Helpers

/-- Expected queries for a hidden table oracle on a product input equal the sum of the
individual oracle expectations weighted by the squared environment amplitudes. -/
theorem observed_hiddenTable_expected_average
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (O : E → Matrix I I ℂ) (P : ObservedCircuit I)
    (psi : QState I) (gamma : QState E) :
    expectedObservedQueries (hiddenTableOracle O) (liftObservedEnvironment (E := E) P)
      (TensorState psi gamma) =
      ∑ a, Complex.normSq (gamma a) * expectedObservedQueries (O a) P psi := by
  simpa only [expectedObservedQueries_eq_sum] using!
    hidden_weighted_average O P psi gamma (fun _ queries _ => (queries : ℝ))

/-- The mass of an acceptance-and-outcome event under a hidden table oracle on a product input
is the corresponding weighted sum over its oracle blocks. -/
theorem observed_hiddenTable_event_average
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (O : E → Matrix I I ℂ) (P : ObservedCircuit I)
    (psi : QState I) (gamma : QState E)
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass (hiddenTableOracle O) (liftObservedEnvironment (E := E) P)
      (TensorState psi gamma) (fun t => event t.accepted t.outcomes) =
      ∑ a, Complex.normSq (gamma a) *
        observedEventMass (O a) P psi (fun t => event t.accepted t.outcomes) := by
  simpa only [observedEventMass, mul_ite, mul_one, mul_zero] using!
    hidden_weighted_average O P psi gamma
      (fun accepted _ outcomes => if event accepted outcomes then 1 else 0)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
