/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DimInstruments.DimTreeExec.DimInstrumentTreeDefs

/-!
# Execution laws for adaptive instrument trees

This module proves complete positivity of the leaf maps of `Program` and trace preservation of
`forget`. It also identifies the leafwise effect of `thenChannel` and proves positivity and
total trace preservation in the presence of any finite reference system, using the framework of
[Watrous2018].

## Main statements

* `g1`: leaf maps are completely positive and their sum preserves trace.
* `g2`: appending a channel postcomposes each leaf map and their sum.
* `g3`: reference amplification preserves leaf positivity and the total trace.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace Qatlib.Concepts.DimInstruments.DimTreeExec
open Qatlib.Concepts.DimInstruments.DimTreeExec
open scoped BigOperators ComplexOrder

/-- Trace commutes with summation over a finite list of operators. -/
lemma trace_list_sum {E : ℕ} (l : List (Operator E)) :
    Matrix.trace l.sum = (l.map Matrix.trace).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [ih, Matrix.trace_add]

/-- Applying a sum of linear maps equals summing their values on the same input. -/
lemma sum_map_apply {D E : ℕ} (l : List (Operator D →ₗ[ℂ] Operator E)) (A : Operator D) :
    l.sum A = (l.map (fun T => T A)).sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
    simp [ih]

/-- Every enumerated execution leaf of an instrument program has a completely positive map. -/
lemma leaves_cp {D E : ℕ} (P : Program D E) :
    ∀ t ∈ leaves P, CompletelyPositive t.map := by
  induction P with
  | halt T =>
    intro t ht
    simp [leaves] at ht
    simpa [ht] using T.completelyPositive
  | measure I next ih =>
    intro t ht
    simp only [leaves] at ht
    rw [List.mem_flatten] at ht
    obtain ⟨ys, hys, htys⟩ := ht
    rw [List.mem_ofFn] at hys
    obtain ⟨o, rfl⟩ := hys
    rw [List.mem_map] at htys
    obtain ⟨u, hu, rfl⟩ := htys
    exact (ih o u hu).comp (I.cp o)

/-- Summing a function over a flattened list equals summing its sums over the component lists. -/
lemma map_sum_flatten {α β : Type} [AddCommMonoid β] (l : List (List α)) (f : α → β) :
    ((l.flatten.map f).sum) = (l.map fun xs => (xs.map f).sum).sum := by
  induction l with
  | nil => simp
  | cons xs l ih =>
    simp [List.flatten_cons, List.map_append, List.sum_append, Function.comp_def]

/-- Forgetting a measurement node equals summing the continuation outputs on the respective
instrument branches. -/
lemma forget_measure {D M E s : ℕ} (I : Instrument (Fin s) D M)
    (next : Fin s → Program M E) (A : Operator D) :
    forget (.measure I next) A = ∑ o : Fin s, forget (next o) (I.branch o A) := by
  classical
  change (((leaves (.measure I next)).map Leaf.map).sum) A = _
  rw [sum_map_apply]
  simp only [leaves, List.map_map, Function.comp_def]
  rw [map_sum_flatten, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [forget, sum_map_apply, List.map_map, Function.comp_def, LinearMap.comp_apply]

/-- The sum of all leaf maps of an instrument program preserves trace. -/
lemma forget_trace {D E : ℕ} (P : Program D E) : TracePreserving (forget P) := by
  induction P with
  | halt T =>
    intro A
    simp [forget, leaves]
    exact T.tracePreserving A
  | measure I next ih =>
    intro A
    rw [forget_measure]
    calc
      Matrix.trace (∑ o, forget (next o) (I.branch o A))
          = ∑ o, Matrix.trace (forget (next o) (I.branch o A)) := by
            rw [← List.sum_ofFn]
            simpa [List.sum_ofFn] using
              (trace_list_sum (List.ofFn fun o => forget (next o) (I.branch o A))).symm
      _ = ∑ o, Matrix.trace (I.branch o A) := by
            refine Finset.sum_congr rfl fun o _ => ih o (I.branch o A)
      _ = Matrix.trace (∑ o, I.branch o A) := by
            rw [← List.sum_ofFn]
            simpa [List.sum_ofFn] using
              (trace_list_sum (List.ofFn fun o => I.branch o A))
      _ = Matrix.trace A := I.total A

/-- Every instrument program has completely positive leaf maps and a trace-preserving map after
forgetting its records. -/
theorem g1 :
    ∀ (D E : ℕ) (P : Program D E),
      (∀ t ∈ leaves P, CompletelyPositive t.map) ∧
      TracePreserving (forget P) := by
  intro D E P
  exact ⟨leaves_cp P, forget_trace P⟩

/-- Postcomposition by a linear map commutes with summation over a list of linear maps. -/
lemma comp_list_sum {D E F : ℕ} (S : Operator E →ₗ[ℂ] Operator F)
    (l : List (Operator D →ₗ[ℂ] Operator E)) :
    (l.map (fun T => S.comp T)).sum = S.comp l.sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
    simp [ih, LinearMap.comp_add]

/-- Appending a channel postcomposes every enumerated leaf map and preserves its record and
measurement count. -/
lemma leaves_thenChannel {D E F : ℕ} (P : Program D E) (S : QuantumChannel E F) :
    leaves (thenChannel P S) =
      (leaves P).map (fun t => (⟨S.map.comp t.map, t.record, t.measurements⟩ : Leaf D F)) := by
  induction P with
  | halt T =>
    simp [thenChannel, leaves, QuantumChannel.comp]
  | measure I next ih =>
    simp only [thenChannel, leaves, ih, List.map_ofFn, List.map_flatten, List.map_map,
      Function.comp_def, LinearMap.comp_assoc]

/-- Forgetting records after appending a channel equals postcomposing the forgotten program map
by that channel. -/
lemma forget_thenChannel {D E F : ℕ} (P : Program D E) (S : QuantumChannel E F) :
    forget (thenChannel P S) = S.map.comp (forget P) := by
  have h := comp_list_sum S.map ((leaves P).map Leaf.map)
  simp only [List.map_map, Function.comp_def] at h
  simpa [forget, leaves_thenChannel] using! h

/-- Appending a channel gives the stated postcomposition formulas for both individual leaves and
their sum. -/
theorem g2 :
    ∀ (D E F : ℕ) (P : Program D E) (S : QuantumChannel E F),
      leaves (thenChannel P S) =
        (leaves P).map (fun t => (⟨S.map.comp t.map, t.record, t.measurements⟩ : Leaf D F)) ∧
      forget (thenChannel P S) = S.map.comp (forget P) := by
  intro D E F P S
  exact ⟨leaves_thenChannel P S, forget_thenChannel P S⟩

/-- Amplification by a finite reference system commutes with summation over a list of linear
maps. -/
lemma tensorLeft_list_sum {D E R : ℕ} (l : List (Operator D →ₗ[ℂ] Operator E))
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft l.sum ρ = (l.map (fun T => tensorLeft T ρ)).sum := by
  induction l with
  | nil =>
    ext x y
    simp [tensorLeft]
  | cons T l ih =>
    ext x y
    have hih : tensorLeft l.sum ρ x y = (List.map (fun T => tensorLeft T ρ) l).sum x y :=
      congrArg (fun M => M x y) ih
    simp only [tensorLeft] at hih
    simp only [List.sum_cons, List.map_cons, tensorLeft, LinearMap.add_apply, Matrix.add_apply, hih]

/-- With any finite reference system, each leaf preserves positive semidefiniteness and the sum
of amplified leaf outputs preserves trace. -/
theorem g3 :
    ∀ (D E R : ℕ) (P : Program D E)
      (rho : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      (rho.PosSemidef → ∀ t ∈ leaves P, (tensorLeft t.map rho).PosSemidef) ∧
      Matrix.trace (((leaves P).map (fun t => tensorLeft t.map rho)).sum) = Matrix.trace rho := by
  intro D E R P rho
  refine ⟨?_, ?_⟩
  · intro hρ t ht
    exact tensorLeft_posSemidef (leaves_cp P t ht) hρ
  · calc
      Matrix.trace (((leaves P).map (fun t => tensorLeft t.map rho)).sum)
          = Matrix.trace (tensorLeft (forget P) rho) := by
            have hsum := tensorLeft_list_sum ((leaves P).map Leaf.map) rho
            have hforget : ((leaves P).map Leaf.map).sum = forget P := rfl
            rw [hforget, List.map_map, Function.comp_def] at hsum
            simpa using congrArg Matrix.trace hsum.symm
      _ = Matrix.trace rho := tensorLeft_trace_map (forget P) (forget_trace P) rho

end Qatlib.Concepts.DimInstruments.DimTreeExec
