/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions

/-!
# Global phase invariance without a reference

`phaseLeaf` tracks how multiplying the oracle by a scalar changes a branch operator by that
scalar raised to the branch's query count. For a scalar of unit norm, this leaves branch masses
and all events determined by branch metadata unchanged.

Consequently, observed acceptance is invariant under global oracle phase. The decision
corollaries rule out distinguishing an oracle from its negation, including the two constant
phase oracles, with the stated error threshold below one half. See [NielsenChuang2010] for
background.

## Main statements

* `leaves_phase`: oracle scaling acts on leaves through their query counts.
* `metadata_event_phase_fin`: metadata event masses are invariant under unit global phase.
* `no_reference_constant_phase_bit`: the two constant phase oracles cannot satisfy the specified
  decision inequalities.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib Matrix
open scoped Classical BigOperators

variable {D : ℕ}

/-- Scale a leaf operator by `c` raised to its query count, retaining all branch metadata. -/
def phaseLeaf (c : ℂ) (leaf : ObservedKrausLeaf D) : ObservedKrausLeaf D :=
  { leaf with operator := c ^ leaf.queries • leaf.operator }

/-- Phase scaling commutes with prepending an operation when that operation is also scaled by
`c^q` for its added query count. -/
theorem phase_prepend (c : ℂ) (leaf : ObservedKrausLeaf D) (U : Operator D)
    (q g m : ℕ) (history : List (ℕ × ℕ)) :
    (phaseLeaf c leaf).prepend (c ^ q • U) q g m history =
      phaseLeaf c (leaf.prepend U q g m history) := by
  have hK : (c ^ leaf.queries • leaf.operator) * (c ^ q • U) =
      c ^ (leaf.queries + q) • (leaf.operator * U) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
  cases leaf
  dsimp only [phaseLeaf, ObservedKrausLeaf.prepend] at *
  congr 1

/-- Phase scaling commutes with prepending an operation that adds no queries. -/
theorem phase_prepend_zero (c : ℂ) (leaf : ObservedKrausLeaf D) (U : Operator D)
    (g m : ℕ) (history : List (ℕ × ℕ)) :
    (phaseLeaf c leaf).prepend U 0 g m history =
      phaseLeaf c (leaf.prepend U 0 g m history) := by
  simpa only [pow_zero, one_smul] using phase_prepend c leaf U 0 g m history

/-- Prepending the scaled oracle to a phase-scaled leaf equals phase-scaling the leaf after
prepending the original oracle. -/
theorem phase_prepend_query (c : ℂ) (leaf : ObservedKrausLeaf D) (O : Operator D) :
    (phaseLeaf c leaf).prepend (c • O) 1 0 0 [] =
      phaseLeaf c (leaf.prepend O 1 0 0 []) := by
  simpa only [pow_one] using phase_prepend c leaf O 1 0 0 []

/-- Scaling the oracle by `c` scales each extracted leaf operator by `c` raised to that leaf's
query count. -/
theorem leaves_phase (c : ℂ) (O : Operator D) (C : ObservedCircuit (Fin D)) :
    observedKrausLeaves (c • O) C =
      (observedKrausLeaves O C).map (phaseLeaf c) := by
  induction C with
  | halt accepted =>
      simp [observedKrausLeaves, phaseLeaf]
  | step s next ih =>
      cases s with
      | gate U =>
          simp only [observedKrausLeaves, ih, List.map_map, Function.comp_def,
            phase_prepend_zero]
      | query =>
          simp only [observedKrausLeaves, ih, List.map_map, Function.comp_def,
            phase_prepend_query]
  | measure n label next ih =>
      simp only [observedKrausLeaves, ih, List.map_flatten, List.map_ofFn,
        List.map_map, Function.comp_def, phase_prepend_zero]
  | project P onFalse onTrue ihFalse ihTrue =>
      simp only [observedKrausLeaves, ihFalse, ihTrue, List.map_append,
        List.map_map, Function.comp_def, phase_prepend_zero]

/-- Multiplying a branch operator by a power of a unit-norm scalar preserves the mass of its
output state. -/
theorem phase_operator_mass (c : ℂ) (hc : ‖c‖ = 1) (q : ℕ)
    (K : Operator D) (ψ : QState (Fin D)) :
    branchMass (ApplyGate (c ^ q • K) ψ) = branchMass (ApplyGate K ψ) := by
  change MeasureProb ((c ^ q • K) *ᵥ ψ) Finset.univ =
    MeasureProb (K *ᵥ ψ) Finset.univ
  rw [Matrix.smul_mulVec, measureProb_smul]
  simp only [norm_pow, hc, one_pow, one_mul]

/-- Phase scaling a Kraus leaf by a unit-norm scalar preserves the mass of its associated trace
state. -/
theorem phase_trace_mass (c : ℂ) (hc : ‖c‖ = 1)
    (leaf : ObservedKrausLeaf D) (ψ : QState (Fin D)) :
    branchMass ((phaseLeaf c leaf).toTrace ψ).state =
      branchMass (leaf.toTrace ψ).state := by
  exact phase_operator_mass c hc leaf.queries leaf.operator ψ

/-- Multiplying the oracle by a unit-norm scalar preserves the mass of every event depending
only on acceptance, resource counters, and measurement outcomes. -/
theorem metadata_event_phase_fin (c : ℂ) (hc : ‖c‖ = 1)
    (O : Operator D) (C : ObservedCircuit (Fin D)) (ψ : QState (Fin D))
    (event : Bool → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool) :
    observedEventMass (c • O) C ψ
        (fun t => event t.accepted t.queries t.gates t.measurements t.outcomes) =
      observedEventMass O C ψ
        (fun t => event t.accepted t.queries t.gates t.measurements t.outcomes) := by
  simp only [observedEventMass, observedTraces_eq_krausLeaves, leaves_phase,
    List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro leaf _
  change (if event leaf.accepted leaf.queries leaf.gates leaf.measurements leaf.outcomes
      then branchMass ((phaseLeaf c leaf).toTrace ψ).state else 0) =
    (if event leaf.accepted leaf.queries leaf.gates leaf.measurements leaf.outcomes
      then branchMass (leaf.toTrace ψ).state else 0)
  rw [phase_trace_mass c hc]

/-- For a circuit on `Fin D`, multiplying the oracle by a unit-norm scalar preserves observed
acceptance. -/
theorem acceptance_phase_fin (c : ℂ) (hc : ‖c‖ = 1)
    (O : Operator D) (C : ObservedCircuit (Fin D)) (ψ : QState (Fin D)) :
    observedAcceptance (c • O) C ψ = observedAcceptance O C ψ := by
  simpa only [observedEventMass_accepted] using
    metadata_event_phase_fin c hc O C ψ (fun b _ _ _ _ => b)

/-- For any finite register, observed acceptance is invariant under multiplication of the oracle
by a unit-norm scalar. -/
theorem acceptance_phase {I : Type} [Fintype I] [DecidableEq I]
    (c : ℂ) (hc : ‖c‖ = 1) (O : Matrix I I ℂ)
    (C : ObservedCircuit I) (ψ : QState I) :
    observedAcceptance (c • O) C ψ = observedAcceptance O C ψ := by
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hscaled := relabelObserved_event e (c • O) C ψ (fun b _ => b)
  have hbase := relabelObserved_event e O C ψ (fun b _ => b)
  simp only [observedEventMass_accepted] at hscaled hbase
  calc
    observedAcceptance (c • O) C ψ =
        observedAcceptance (relabelGate e (c • O)) (relabelObserved e C)
          (relabelState e ψ) := hscaled.symm
    _ = observedAcceptance (relabelGate e O) (relabelObserved e C)
          (relabelState e ψ) := by
      have hrel : relabelGate e (c • O) = c • relabelGate e O := rfl
      rw [hrel]
      exact acceptance_phase_fin c hc _ _ _
    _ = observedAcceptance O C ψ := hbase

/-- Negating the oracle preserves the observed acceptance mass. -/
theorem acceptance_neg {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : ObservedCircuit I) (ψ : QState I) :
    observedAcceptance (-O) C ψ = observedAcceptance O C ψ := by
  simpa only [neg_one_smul] using
    acceptance_phase (-1 : ℂ) (by simp) O C ψ

/-- For `ε < 1/2`, acceptance cannot be at most `ε` for an oracle and at least `1-ε` for its
negation. -/
theorem no_reference_decision {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : ObservedCircuit I) (ψ : QState I)
    (ε : ℝ) (hε : ε < 1 / 2) :
    ¬ (observedAcceptance O C ψ ≤ ε ∧
      1 - ε ≤ observedAcceptance (-O) C ψ) := by
  rintro ⟨hzero, hone⟩
  rw [acceptance_neg] at hone
  linarith

/-- For `ε < 1/2`, a circuit cannot have acceptance at most `ε` for the constant-false phase
oracle and at least `1-ε` for the constant-true phase oracle. -/
theorem no_reference_constant_phase_bit {I : Type} [Fintype I] [DecidableEq I]
    (C : ObservedCircuit I) (ψ : QState I) (ε : ℝ) (hε : ε < 1 / 2) :
    ¬ (observedAcceptance (PhaseOracle (fun _ : I => false)) C ψ ≤ ε ∧
      1 - ε ≤ observedAcceptance (PhaseOracle (fun _ : I => true)) C ψ) := by
  simpa only [phaseOracle_false_eq_one, phaseOracle_true_eq_neg_one] using
    no_reference_decision (1 : Matrix I I ℂ) C ψ ε hε

end Qatlib.Concepts.ShadowModels.ShadowChannel

end
