/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix

inductive KrausCircuit (d s : ℕ) where
  | halt (accepted : Bool)
  | step (action : Step (Fin d)) (next : KrausCircuit d s)
  | instrument (K : Fin s → Operator d) (next : Fin s → KrausCircuit d s)

def krausCircuitWellFormed {d s : ℕ} : KrausCircuit d s → Prop
  | .halt _ => True
  | .step (.gate G) P => G ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ krausCircuitWellFormed P
  | .step .query P => krausCircuitWellFormed P
  | .instrument K next => (∑ a, (K a).conjTranspose * K a = 1) ∧
      ∀ a, krausCircuitWellFormed (next a)

def krausCircuitBudget {d s : ℕ} : KrausCircuit d s → ℕ
  | .halt _ => 0
  | .step (.gate _) P => krausCircuitBudget P
  | .step .query P => krausCircuitBudget P + 1
  | .instrument _ next => Finset.univ.sup (fun a => krausCircuitBudget (next a))

noncomputable def krausCircuitTraces {d s : ℕ} (O : Operator d) :
    KrausCircuit d s → QState (Fin d) → List (BranchTrace (Fin d))
  | .halt b, psi => [⟨psi, b, 0, 0, 0, []⟩]
  | .step (.gate G) P, psi =>
      (krausCircuitTraces O P (ApplyGate G psi)).map fun t => {t with gates := t.gates + 1}
  | .step .query P, psi =>
      (krausCircuitTraces O P (ApplyGate O psi)).map fun t => {t with queries := t.queries + 1}
  | .instrument K next, psi =>
      (List.ofFn fun a : Fin s =>
        (krausCircuitTraces O (next a) (ApplyGate (K a) psi)).map fun t =>
          {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, a.val) :: t.outcomes}).flatten

noncomputable def krausCircuitMixedTraces {d s : ℕ} (O : Operator d) :
    KrausCircuit d s → Operator d → List (MixedBranchTrace d)
  | .halt b, rho => [⟨rho, b, 0, 0, 0, []⟩]
  | .step (.gate G) P, rho =>
      (krausCircuitMixedTraces O P (conjBranch G rho)).map fun t => {t with gates := t.gates + 1}
  | .step .query P, rho =>
      (krausCircuitMixedTraces O P (conjBranch O rho)).map fun t => {t with queries := t.queries + 1}
  | .instrument K next, rho =>
      (List.ofFn fun a : Fin s =>
        (krausCircuitMixedTraces O (next a) (conjBranch (K a) rho)).map fun t =>
          {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, a.val) :: t.outcomes}).flatten

noncomputable def krausCircuitEventMass {d s : ℕ} (O : Operator d)
    (P : KrausCircuit d s) (rho : Operator d)
    (event : Bool → List (ℕ × ℕ) → Bool) : ℝ :=
  ((krausCircuitMixedTraces O P rho).map fun t =>
    if event t.accepted t.outcomes then mixedMass t else 0).sum

noncomputable def krausCircuitExpectedQueries {d s : ℕ} (O : Operator d)
    (P : KrausCircuit d s) (rho : Operator d) : ℝ :=
  ((krausCircuitMixedTraces O P rho).map fun t => mixedMass t * t.queries).sum

end Qatlib.Concepts.AdversaryBounds.AdvDuality
