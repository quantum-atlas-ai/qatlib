/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord

/-!
# Unitary gates in adjoint query circuits

This module defines well-formedness of an adjoint query circuit by requiring each explicitly
stored gate to be unitary. It proves that this condition survives list operations, exchange of
forward and backward queries, and taking the adjoint circuit, and that evaluation at a unitary
oracle is unitary. The compiler results support the QSVT circuit framework of
[GilyenSuLowWiebe2019].

## Main statements

* `WellFormedAdjointCircuit` and `WellFormedAdjointCircuit.evaluate_unitary` connect gate-level
  well-formedness with unitary evaluation.
* `compileQSVT_wellFormed` proves the condition for orthogonal projectors and unit-modulus
  phases.
* `compileParallelQSVT_wellFormed` and `compileRealPartQSVT_wellFormed` cover parallel and
  real-part compilers, with query-swapped and adjoint variants.

## References

* [Gilyen, Su, Low, and Wiebe, 2019][GilyenSuLowWiebe2019], *Quantum singular value
  transformation and beyond: exponential improvements for quantum matrix arithmetics*.
-/

set_option warningAsError false


open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- An adjoint query word satisfies `WellFormedAdjointCircuit` when every explicit instruction
`AdjointStep.gate V` occurring in it has a unitary matrix `V`. -/
def WellFormedAdjointCircuit (cs : List (AdjointStep H)) : Prop :=
  ∀ V : Matrix H H ℂ, AdjointStep.gate V ∈ cs → V ∈ Matrix.unitaryGroup H ℂ

namespace WellFormedAdjointCircuit

/-- The empty adjoint query word satisfies `WellFormedAdjointCircuit`. -/
@[simp] theorem nil : WellFormedAdjointCircuit ([] : List (AdjointStep H)) := by
  simp [WellFormedAdjointCircuit]

/-- The word `c :: cs` satisfies `WellFormedAdjointCircuit` exactly when both the singleton word
containing `c` and the tail `cs` satisfy it. -/
theorem cons_iff (c : AdjointStep H) (cs : List (AdjointStep H)) :
    WellFormedAdjointCircuit (c :: cs) ↔
      WellFormedAdjointCircuit [c] ∧ WellFormedAdjointCircuit cs := by
  simp [WellFormedAdjointCircuit, or_imp, forall_and]

/-- Prepending a step whose singleton word satisfies `WellFormedAdjointCircuit` to a well-formed
word produces a well-formed word. -/
theorem cons {c : AdjointStep H} {cs : List (AdjointStep H)}
    (hc : WellFormedAdjointCircuit [c]) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (c :: cs) := (cons_iff c cs).mpr ⟨hc, hcs⟩

/-- A word beginning with `AdjointStep.gate V` satisfies `WellFormedAdjointCircuit` exactly when
`V` is unitary and its tail is well formed. -/
@[simp] theorem gate_cons_iff (V : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    WellFormedAdjointCircuit (.gate V :: cs) ↔
      V ∈ Matrix.unitaryGroup H ℂ ∧ WellFormedAdjointCircuit cs := by
  simp [WellFormedAdjointCircuit, or_imp, forall_and]

/-- Prepending a forward query preserves and reflects `WellFormedAdjointCircuit`. -/
@[simp] theorem forward_cons_iff (cs : List (AdjointStep H)) :
    WellFormedAdjointCircuit (.forward :: cs) ↔ WellFormedAdjointCircuit cs := by
  simp [WellFormedAdjointCircuit]

/-- Prepending a backward query preserves and reflects `WellFormedAdjointCircuit`. -/
@[simp] theorem backward_cons_iff (cs : List (AdjointStep H)) :
    WellFormedAdjointCircuit (.backward :: cs) ↔ WellFormedAdjointCircuit cs := by
  simp [WellFormedAdjointCircuit]

/-- The concatenation `cs ++ ds` satisfies `WellFormedAdjointCircuit` exactly when each of `cs`
and `ds` satisfies it. -/
@[simp] theorem append_iff (cs ds : List (AdjointStep H)) :
    WellFormedAdjointCircuit (cs ++ ds) ↔
      WellFormedAdjointCircuit cs ∧ WellFormedAdjointCircuit ds := by
  simp only [WellFormedAdjointCircuit, List.mem_append, or_imp, forall_and]

/-- Concatenation preserves `WellFormedAdjointCircuit` when both component words are well
formed. -/
theorem append {cs ds : List (AdjointStep H)}
    (hcs : WellFormedAdjointCircuit cs) (hds : WellFormedAdjointCircuit ds) :
    WellFormedAdjointCircuit (cs ++ ds) := (append_iff cs ds).mpr ⟨hcs, hds⟩

/-- Exchanging forward and backward queries with `swapQueries` preserves
`WellFormedAdjointCircuit`. -/
theorem swapQueries {cs : List (AdjointStep H)} (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (cs.map Qatlib.Concepts.CoherentSim.CoherentOAA.swapQueries) := by
  induction cs with
  | nil => exact nil
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons, Qatlib.Concepts.CoherentSim.CoherentOAA.swapQueries, gate_cons_iff,
      forward_cons_iff, backward_cons_iff] at hcs ⊢
    · exact ⟨hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

/-- Taking `adjointCircuit` preserves `WellFormedAdjointCircuit`. -/
theorem adjointCircuit {cs : List (AdjointStep H)} (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) := by
  induction cs with
  | nil => exact nil
  | cons c cs ih =>
    cases c <;> simp only [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, adjointInstruction, append_iff,
      gate_cons_iff, forward_cons_iff, backward_cons_iff, nil, and_true] at hcs ⊢
    · exact ⟨ih hcs.2, adjoint_unitary hcs.1⟩
    · exact ih hcs
    · exact ih hcs

/-- Evaluating a word satisfying `WellFormedAdjointCircuit` at a unitary oracle `U` yields a
unitary matrix. -/
theorem evaluate_unitary {cs : List (AdjointStep H)} (hcs : WellFormedAdjointCircuit cs)
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    evaluate U cs ∈ Matrix.unitaryGroup H ℂ := by
  induction cs with
  | nil => exact (Matrix.unitaryGroup H ℂ).one_mem
  | cons c cs ih =>
    cases c <;> simp only [gate_cons_iff, forward_cons_iff, backward_cons_iff] at hcs
    · exact (Matrix.unitaryGroup H ℂ).mul_mem hcs.1 (ih hcs.2)
    · exact (Matrix.unitaryGroup H ℂ).mul_mem hU (ih hcs)
    · exact (Matrix.unitaryGroup H ℂ).mul_mem (adjoint_unitary hU) (ih hcs)

end WellFormedAdjointCircuit

/-- For orthogonal projectors `P` and `Q`, `compileQSVT` satisfies `WellFormedAdjointCircuit`
whenever the base and every listed phase satisfy `IsPhase`. -/
theorem compileQSVT_wellFormed {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (compileQSVT P Q base zs) := by
  induction zs generalizing P Q with
  | nil =>
    simpa only [compileQSVT, WellFormedAdjointCircuit.gate_cons_iff,
      WellFormedAdjointCircuit.nil, and_true] using phaseRotation_unitary hQ hb
  | cons z zs ih =>
    simp only [compileQSVT, WellFormedAdjointCircuit.gate_cons_iff,
      WellFormedAdjointCircuit.forward_cons_iff]
    exact ⟨phaseRotation_unitary hQ (hzs z (by simp)),
      (ih hQ hP (fun w hw => hzs w (by simp [hw]))).swapQueries⟩

/-- Under the orthogonal-projector and unit-phase hypotheses, exchanging the queries in the
output of `compileQSVT` yields a word satisfying `WellFormedAdjointCircuit`. -/
theorem compileQSVT_wellFormed_swap {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit ((compileQSVT P Q base zs).map swapQueries) :=
  (compileQSVT_wellFormed hP hQ hb zs hzs).swapQueries

/-- Under the orthogonal-projector and unit-phase hypotheses, the adjoint of the output of
`compileQSVT` satisfies `WellFormedAdjointCircuit`. -/
theorem compileQSVT_wellFormed_adjoint {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (adjointCircuit (compileQSVT P Q base zs)) :=
  (compileQSVT_wellFormed hP hQ hb zs hzs).adjointCircuit

section Parallel

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- For orthogonal projectors `P` and `Q`, `compileParallelQSVT` satisfies
`WellFormedAdjointCircuit` when every branch's base and listed phases satisfy `IsPhase`. -/
theorem compileParallelQSVT_wellFormed {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (base : J → ℂ) (hb : ∀ j, IsPhase (base j)) (zs : List (J → ℂ))
    (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit (compileParallelQSVT P Q base zs) := by
  induction zs generalizing P Q with
  | nil =>
    simpa only [compileParallelQSVT, WellFormedAdjointCircuit.gate_cons_iff,
      WellFormedAdjointCircuit.nil, and_true] using parallelPhase_unitary hQ base hb
  | cons z zs ih =>
    simp only [compileParallelQSVT, WellFormedAdjointCircuit.gate_cons_iff,
      WellFormedAdjointCircuit.forward_cons_iff]
    exact ⟨parallelPhase_unitary hQ z (hzs z (by simp)),
      (ih hQ hP (fun w hw => hzs w (by simp [hw]))).swapQueries⟩

/-- Under the orthogonal-projector and branchwise unit-phase hypotheses, exchanging the queries
in the output of `compileParallelQSVT` preserves `WellFormedAdjointCircuit`. -/
theorem compileParallelQSVT_wellFormed_swap {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (base : J → ℂ) (hb : ∀ j, IsPhase (base j)) (zs : List (J → ℂ))
    (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit ((compileParallelQSVT P Q base zs).map swapQueries) :=
  (compileParallelQSVT_wellFormed hP hQ base hb zs hzs).swapQueries

/-- Under the orthogonal-projector and branchwise unit-phase hypotheses, the adjoint of the
output of `compileParallelQSVT` satisfies `WellFormedAdjointCircuit`. -/
theorem compileParallelQSVT_wellFormed_adjoint {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (base : J → ℂ) (hb : ∀ j, IsPhase (base j)) (zs : List (J → ℂ))
    (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit (adjointCircuit (compileParallelQSVT P Q base zs)) :=
  (compileParallelQSVT_wellFormed hP hQ base hb zs hzs).adjointCircuit

end Parallel

/-- For orthogonal projectors `P` and `Q`, `compileRealPartQSVT` satisfies
`WellFormedAdjointCircuit` whenever the base and every listed phase satisfy `IsPhase`. -/
theorem compileRealPartQSVT_wellFormed {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (compileRealPartQSVT P Q base zs) := by
  apply compileParallelQSVT_wellFormed hP hQ
  · intro b
    cases b
    · exact Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate hb
    · exact hb
  · intro z hz b
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    cases b
    · exact Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate (hzs w hw)
    · exact hzs w hw

/-- Under the orthogonal-projector and unit-phase hypotheses, exchanging the queries in the
output of `compileRealPartQSVT` preserves `WellFormedAdjointCircuit`. -/
theorem compileRealPartQSVT_wellFormed_swap {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit ((compileRealPartQSVT P Q base zs).map swapQueries) :=
  (compileRealPartQSVT_wellFormed hP hQ hb zs hzs).swapQueries

/-- Under the orthogonal-projector and unit-phase hypotheses, the adjoint of the output of
`compileRealPartQSVT` satisfies `WellFormedAdjointCircuit`. -/
theorem compileRealPartQSVT_wellFormed_adjoint {P Q : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (adjointCircuit (compileRealPartQSVT P Q base zs)) :=
  (compileRealPartQSVT_wellFormed hP hQ hb zs hzs).adjointCircuit

end Qatlib.Concepts.QspSimulation.Achievability
