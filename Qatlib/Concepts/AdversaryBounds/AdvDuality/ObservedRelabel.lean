/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

variable {I J : Type*}

noncomputable def relabelObserved [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) : ObservedCircuit I → ObservedCircuit J
  | .halt accepted => .halt accepted
  | .step (.gate U) next => .step (.gate (relabelGate e U)) (relabelObserved e next)
  | .step .query next => .step .query (relabelObserved e next)
  | .measure n label next =>
      .measure n (label ∘ e.symm) (fun o => relabelObserved e (next o))
  | .project Q onFalse onTrue =>
      .project (relabelGate e Q) (relabelObserved e onFalse) (relabelObserved e onTrue)

noncomputable def relabelObservedTrace [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (t : BranchTrace I) : BranchTrace J :=
  { state := relabelState e t.state
    accepted := t.accepted
    queries := t.queries
    gates := t.gates
    measurements := t.measurements
    outcomes := t.outcomes }

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem relabel_compl (e : I ≃ J) (Q : Matrix I I ℂ) :
    relabelGate e (1 - Q) = 1 - relabelGate e Q := by
  calc
    relabelGate e (1 - Q) = relabelGate e (1 : Matrix I I ℂ) - relabelGate e Q := rfl
    _ = 1 - relabelGate e Q := by rw [CircuitRelabel.relabelGate_one]

private theorem relabel_projective (e : I ≃ J) (Q : Matrix I I ℂ)
    (b : Bool) (psi : QState I) :
    ProjectiveBranch (relabelGate e Q) b (relabelState e psi) =
      relabelState e (ProjectiveBranch Q b psi) := by
  cases b with
  | false =>
      simpa only [ProjectiveBranch, Bool.false_eq_true, ↓reduceIte, relabel_compl] using
        applyGate_relabelGate e (1 - Q) psi
  | true =>
      simpa only [ProjectiveBranch, ↓reduceIte] using applyGate_relabelGate e Q psi

private theorem relabel_partition (e : I ≃ J) (psi : QState I)
    {n : ℕ} (label : I → Fin n) (o : Fin n) :
    Collapse (relabelState e psi)
        (Finset.univ.filter (fun j => label (e.symm j) = o)) =
      relabelState e (Collapse psi (Finset.univ.filter (fun i => label i = o))) := by
  funext j
  simp only [collapse_apply, Finset.mem_filter, Finset.mem_univ, true_and,
    relabelState_apply, Function.comp_apply]

private theorem relabel_projector (e : I ≃ J) {Q : Matrix I I ℂ}
    (hQ : IsOrthogonalProjector Q) : IsOrthogonalProjector (relabelGate e Q) := by
  refine ⟨?_, ?_⟩
  · show relabelGate e Q * relabelGate e Q = relabelGate e Q
    rw [← CircuitRelabel.relabelGate_mul, hQ.1]
  · have hstar : (relabelGate e Q)ᴴ = relabelGate e Qᴴ := by
      ext i j
      rfl
    have hQstar : Qᴴ = Q := hQ.2
    show (relabelGate e Q)ᴴ = relabelGate e Q
    rw [hstar, hQstar]

private theorem relabel_mass (e : I ≃ J) (psi : QState I) :
    branchMass (relabelState e psi) = branchMass psi := by
  change (∑ j : J, BornProb (relabelState e psi) j) = ∑ i : I, BornProb psi i
  simp only [bornProb_relabelState]
  exact e.symm.sum_comp (BornProb psi)

theorem relabelObserved_traces (e : I ≃ J) (O : Matrix I I ℂ)
    (P : ObservedCircuit I) (psi : QState I) :
    observedTraces (relabelGate e O) (relabelObserved e P) (relabelState e psi) =
      (observedTraces O P psi).map (relabelObservedTrace e) := by
  induction P generalizing psi with
  | halt accepted => rfl
  | step s next ih =>
      cases s with
      | gate U =>
          simp only [relabelObserved, observedTraces, applyGate_relabelGate, ih,
            List.map_map, Function.comp_def, relabelObservedTrace]
      | query =>
          simp only [relabelObserved, observedTraces, applyGate_relabelGate, ih,
            List.map_map, Function.comp_def, relabelObservedTrace]
  | measure n label next ih =>
      simp only [relabelObserved, observedTraces, Function.comp_def, relabel_partition, ih,
        List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def,
        relabelObservedTrace]
  | project Q onFalse onTrue ihFalse ihTrue =>
      simp only [relabelObserved, observedTraces, relabel_projective, ihFalse, ihTrue,
        List.map_append, List.map_map, Function.comp_def, relabelObservedTrace]

theorem relabelObserved_budget (e : I ≃ J) (P : ObservedCircuit I) :
    observedQueryBudget (relabelObserved e P) = observedQueryBudget P := by
  induction P with
  | halt accepted => rfl
  | step s next ih =>
      cases s <;> simp only [relabelObserved, observedQueryBudget, ih]
  | measure n label next ih =>
      simp only [relabelObserved, observedQueryBudget, ih]
  | project Q onFalse onTrue ihFalse ihTrue =>
      simp only [relabelObserved, observedQueryBudget, ihFalse, ihTrue]

theorem relabelObserved_wellFormed (e : I ≃ J) (P : ObservedCircuit I)
    (hP : observedWellFormed P) : observedWellFormed (relabelObserved e P) := by
  induction P with
  | halt accepted => trivial
  | step s next ih =>
      cases s with
      | gate U => exact ⟨(relabelGate_mem_unitaryGroup e U).2 hP.1, ih hP.2⟩
      | query => exact ih hP
  | measure n label next ih => exact fun o => ih o (hP o)
  | project Q onFalse onTrue ihFalse ihTrue =>
      exact ⟨relabel_projector e hP.1, ihFalse hP.2.1, ihTrue hP.2.2⟩

theorem relabelObserved_event (e : I ≃ J) (O : Matrix I I ℂ)
    (P : ObservedCircuit I) (psi : QState I)
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass (relabelGate e O) (relabelObserved e P) (relabelState e psi)
        (fun t => event t.accepted t.outcomes) =
      observedEventMass O P psi (fun t => event t.accepted t.outcomes) := by
  simp only [observedEventMass, relabelObserved_traces, List.map_map,
    Function.comp_def, relabelObservedTrace, relabel_mass]

theorem relabelObserved_expected (e : I ≃ J) (O : Matrix I I ℂ)
    (P : ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries (relabelGate e O) (relabelObserved e P) (relabelState e psi) =
      expectedObservedQueries O P psi := by
  simp only [expectedObservedQueries_eq_sum, relabelObserved_traces, List.map_map,
    Function.comp_def, relabelObservedTrace, relabel_mass]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
