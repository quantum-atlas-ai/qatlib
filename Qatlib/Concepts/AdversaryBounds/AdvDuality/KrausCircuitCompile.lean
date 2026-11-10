/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausMemoryReset
import Qatlib.Concepts.Execution.KnownKraus.KrausUnitaryDilation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.KnownKraus

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

noncomputable def chosenKrausUnitary {d s : ℕ} (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (zero : Fin s) :
    Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ :=
  Classical.choose (kraus_unitary_dilation K hK zero)

theorem chosenKrausUnitary_spec {d s : ℕ} (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (zero : Fin s) :
    chosenKrausUnitary K hK zero ∈ Matrix.unitaryGroup (Fin d × Fin s) ℂ ∧
      ∀ psi : QState (Fin d),
        ApplyGate (chosenKrausUnitary K hK zero) (TensorState psi (Ket zero)) =
          fun x => ApplyGate (K x.2) psi x.1 :=
  Classical.choose_spec (kraus_unitary_dilation K hK zero)

noncomputable def compileKrausCircuit {d s : ℕ} (zero : Fin s) :
    (P : KrausCircuit d s) → krausCircuitWellFormed P →
      ObservedCircuit (Fin d × Fin s)
  | .halt b, _ => .halt b
  | .step (.gate G) P, hP =>
      .step (.gate (TensorGate G (1 : Operator s)))
        (compileKrausCircuit zero P hP.2)
  | .step .query P, hP => .step .query (compileKrausCircuit zero P hP)
  | .instrument K next, hP =>
      .step (.gate (chosenKrausUnitary K hP.1 zero))
        (.measure s Prod.snd (fun a =>
          .step (.gate (krausMemoryReset zero a))
            (compileKrausCircuit zero (next a) (hP.2 a))))

noncomputable def embedKrausPureTrace {d s : ℕ} (zero : Fin s)
    (t : BranchTrace (Fin d)) : BranchTrace (Fin d × Fin s) where
  state := TensorState t.state (Ket zero)
  accepted := t.accepted
  queries := t.queries
  gates := t.gates
  measurements := t.measurements
  outcomes := t.outcomes

theorem compileKrausCircuit_wellFormed {d s : ℕ} (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) :
    observedWellFormed (compileKrausCircuit zero P hP) := by
  induction P with
  | halt b => trivial
  | step action P ih =>
      cases action with
      | gate G => exact ⟨tensorGate_unitary hP.1 (Submonoid.one_mem _), ih hP.2⟩
      | query => exact ih hP
  | instrument K next ih =>
      exact ⟨(chosenKrausUnitary_spec K hP.1 zero).1,
        fun a => ⟨kraus_memory_reset_unitary zero a, ih a (hP.2 a)⟩⟩

theorem compileKrausCircuit_budget {d s : ℕ} (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) :
    observedQueryBudget (compileKrausCircuit zero P hP) = krausCircuitBudget P := by
  induction P with
  | halt b => rfl
  | step action P ih =>
      cases action <;>
        simp only [compileKrausCircuit, observedQueryBudget, krausCircuitBudget, ih]
  | instrument K next ih =>
      simp only [compileKrausCircuit, observedQueryBudget, krausCircuitBudget, ih]

theorem compileKrausCircuit_traces {d s : ℕ} (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (O : Operator d) (psi : QState (Fin d)) :
    observedTraces (TensorGate O (1 : Operator s))
        (compileKrausCircuit zero P hP) (TensorState psi (Ket zero)) =
      (krausCircuitTraces O P psi).map (embedKrausPureTrace zero) := by
  induction P generalizing psi with
  | halt b => rfl
  | step action P ih =>
      cases action with
      | gate G =>
          simp only [compileKrausCircuit, observedTraces, applyGate_tensorGate,
            applyGate_one, ih, krausCircuitTraces, List.map_map,
            Function.comp_def, embedKrausPureTrace]
      | query =>
          simp only [compileKrausCircuit, observedTraces, applyGate_tensorGate,
            applyGate_one, ih, krausCircuitTraces, List.map_map,
            Function.comp_def, embedKrausPureTrace]
  | instrument K next ih =>
      simp only [compileKrausCircuit, observedTraces,
        kraus_memory_reset_branch K zero _ (chosenKrausUnitary K hP.1 zero)
          (chosenKrausUnitary_spec K hP.1 zero).2,
        ih, krausCircuitTraces, List.map_flatten, List.map_ofFn,
        List.map_map, Function.comp_def, embedKrausPureTrace, Nat.add_assoc]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
