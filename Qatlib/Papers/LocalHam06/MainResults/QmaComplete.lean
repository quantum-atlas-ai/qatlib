/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessFullSpace

/-!
# Padded history-Hamiltonian energy separation

The predicates `YesWitness` and `NoSound` express completeness and soundness conditions for a
history circuit. Under the specified parameter bounds, `two_local_hamiltonian_qma_hard` packages
the padded Hamiltonian and separated energy thresholds used in the reduction of
[KempeKitaevRegev2006].

## Main statements

* `YesWitness`: Requires a legal normalized input with acceptance at least `a`.
* `NoSound`: Bounds acceptance by `ε` on every legal normalized input.
* `two_local_hamiltonian_qma_hard`: Constructs the Hamiltonian with positive yes threshold and a
  gap equal to that threshold.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical BigOperators Kronecker
open Matrix

namespace Qatlib.Papers.LocalHam06.MainResults.QmaComplete

open Qatlib.Papers.LocalHam06.MainResults Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

/-- The circuit has a legal normalized input whose acceptance probability is at least `a`. -/
def YesWitness (C : QmaHistoryCircuit) (a : ℝ) : Prop :=
  ∃ φ : QState (Reg C.qubits),
    QmaInitLegal C φ ∧ Normalized φ ∧ a ≤ qmaHistoryAcceptProb C φ

/-- Every legal normalized input to the circuit has acceptance probability at most `ε`. -/
def NoSound (C : QmaHistoryCircuit) (ε : ℝ) : Prop :=
  ∀ φ : QState (Reg C.qubits),
    QmaInitLegal C φ → Normalized φ → qmaHistoryAcceptProb C φ ≤ ε

/-- Under the stated bounds on `ε` and `1 - a`, the padded history Hamiltonian has positive yes
threshold, no-minus-yes gap equal to the yes threshold, and the specified completeness and
soundness energy implications. This packages the energy separation used for Theorem 1 of
[KempeKitaevRegev2006]. -/
theorem two_local_hamiltonian_qma_hard
    (C : QmaHistoryCircuit) (a ε : ℝ)
    (hε : ε ≤ 1 / 4)
    (ha : 1 - a ≤ 1 / ((2 : ℝ) ^ 14 * (((paid64 C).gates.length : ℝ) + 1) ^ 2)) :
    ∃ (H : Matrix (Phys (paid64 C)) (Phys (paid64 C)) ℂ) (yes no : ℝ),
      H = fullHamiltonian (paid64 C) ∧ 0 < yes ∧ no - yes = yes ∧
        (YesWitness C a →
          ∃ η : QState (Phys (paid64 C)), Normalized η ∧ energy H η ≤ yes) ∧
        (NoSound C ε →
          ∀ η : QState (Phys (paid64 C)), Normalized η → no ≤ energy H η) := by
  have h := padded_full_contract C a ε hε ha
  exact ⟨fullHamiltonian (paid64 C), yesCut (paid64 C), noCut (paid64 C), rfl,
    h.2.2.1, h.2.2.2, h.1, h.2.1⟩

end Qatlib.Papers.LocalHam06.MainResults.QmaComplete
