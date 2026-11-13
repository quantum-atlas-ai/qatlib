/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument

/-!
# Lifting observed circuits to network registers

`networkStepLiftGate` extends a local operator by an identity tensor factor and transports it
through a basis equivalence. `networkStepLift` applies this construction to observed circuits,
including their measurement labels and projectors, as needed for local patterns in the
measurement calculus [DanosKashefiPanangaden2007].

The lifting preserves well-formedness and acts leaf by leaf on the Kraus enumeration.
`networkStepLiftLeaf` retains the resource counts and outcome records of each original leaf.

## Main statements

* `networkStepLiftGate_isOrthogonalProjector`: preservation of orthogonal projectors.
* `networkStepLift_wellFormed`: preservation of circuit well-formedness.
* `observedKrausLeaves_networkStepLift`: compatibility of lifting with Kraus-leaf enumeration.

## References

* [Danos, Kashefi, and Panangaden, 2007][DanosKashefiPanangaden2007]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

/-- Extends a local operator by the identity on a complementary system and relabels the tensor
product along `e`. -/
noncomputable def networkStepLiftGate {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    (U : Operator s) : Operator D :=
  relabelGate e (TensorGate U (1 : Operator t))

/-- Lifts a local measurement label by reading the first component of the inverse layout
equivalence. -/
def networkStepLiftLabel {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D) {k : ℕ}
    (l : Fin s → Fin k) : Fin D → Fin k :=
  fun r => l (e.symm r).1

/-- Lifts an observed circuit to a larger register by extending its gates and projectors and
transporting its measurement labels. -/
noncomputable def networkStepLift {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D) :
    ObservedCircuit (Fin s) → ObservedCircuit (Fin D)
  | .halt b => .halt b
  | .step (.gate U) next =>
      .step (.gate (networkStepLiftGate e U)) (networkStepLift e next)
  | .step .query next => .step .query (networkStepLift e next)
  | .measure k l next =>
      .measure k (networkStepLiftLabel e l) (fun o => networkStepLift e (next o))
  | .project P onFalse onTrue =>
      .project (networkStepLiftGate e P) (networkStepLift e onFalse)
        (networkStepLift e onTrue)

/-- Lifts the operator of an observed Kraus leaf while retaining its acceptance flag, resource
counts, and recorded outcomes. -/
noncomputable def networkStepLiftLeaf {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    (L : ObservedKrausLeaf s) : ObservedKrausLeaf D where
  operator := networkStepLiftGate e L.operator
  accepted := L.accepted
  queries := L.queries
  gates := L.gates
  measurements := L.measurements
  outcomes := L.outcomes

/-- Lifting operators preserves multiplication. -/
theorem networkStepLiftGate_mul {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    (A B : Operator s) :
    networkStepLiftGate e (A * B) = networkStepLiftGate e A * networkStepLiftGate e B := by
  unfold networkStepLiftGate
  rw [← teleportRelabelGate_mul, tensorGate_mul, Matrix.mul_one]

/-- Lifting the local identity gives the identity on the larger register. -/
theorem networkStepLiftGate_one {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D) :
    networkStepLiftGate e (1 : Operator s) = 1 := by
  unfold networkStepLiftGate
  rw [tensorGate_one, teleportRelabelGate_one]

/-- Lifting a unitary local operator gives a unitary operator on the larger register. -/
theorem networkStepLiftGate_unitary {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    {U : Operator s} (hU : U ∈ Matrix.unitaryGroup (Fin s) ℂ) :
    networkStepLiftGate e U ∈ Matrix.unitaryGroup (Fin D) ℂ :=
  teleportRelabelGate_mem_unitaryGroup
    (tensorGate_unitary hU (Submonoid.one_mem _)) _

/-- Gate relabeling preserves subtraction. -/
theorem networkRelabelGate_sub {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A - B) = relabelGate e A - relabelGate e B := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

/-- Lifting operators preserves subtraction. -/
theorem networkStepLiftGate_sub {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    (A B : Operator s) :
    networkStepLiftGate e (A - B) = networkStepLiftGate e A - networkStepLiftGate e B := by
  have hT : TensorGate (A - B) (1 : Operator t)
      = TensorGate A (1 : Operator t) - TensorGate B (1 : Operator t) := by
    ext p q
    show ((A - B) p.1 q.1) * (1 : Operator t) p.2 q.2
      = (A p.1 q.1) * (1 : Operator t) p.2 q.2 - (B p.1 q.1) * (1 : Operator t) p.2 q.2
    rw [Matrix.sub_apply, sub_mul]
  rw [networkStepLiftGate, networkStepLiftGate, networkStepLiftGate, hT,
    networkRelabelGate_sub]

/-- A basis projector tensored with the identity projects onto pairs whose first component lies
in the selected set. -/
theorem tensorGate_projector_one {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (S : Finset I) :
    TensorGate (Projector S) (1 : Matrix J J ℂ)
      = Projector (Finset.univ.filter (fun p : I × J => p.1 ∈ S)) := by
  ext p q
  rw [tensorGate_apply]
  simp only [Projector, Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [if_neg hpq]
    by_cases h1 : p.1 = q.1
    · rw [if_pos h1]
      have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- Relabeling a basis projector selects precisely those new indices whose inverse images belong
to the original set. -/
theorem networkRelabelGate_projector {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (S : Finset I) :
    relabelGate e (Projector S)
      = Projector (Finset.univ.filter (fun j => e.symm j ∈ S)) := by
  ext r r'
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Projector,
    Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hrr' : r = r'
  · subst hrr'
    simp
  · have hne : e.symm r ≠ e.symm r' := fun h => hrr' (e.symm.injective h)
    rw [if_neg hrr', if_neg hne]

/-- Lifting a projector onto a measurement outcome gives the projector onto that outcome for the
lifted measurement label. -/
theorem networkStepLiftGate_projector {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D) {k : ℕ}
    (l : Fin s → Fin k) (o : Fin k) :
    networkStepLiftGate e (Projector (Finset.univ.filter (fun i => l i = o)))
      = Projector (Finset.univ.filter (fun r => networkStepLiftLabel e l r = o)) := by
  rw [networkStepLiftGate, tensorGate_projector_one, networkRelabelGate_projector]
  congr 1
  ext r
  simp [Finset.mem_filter, networkStepLiftLabel]

/-- Relabeling an orthogonal projector preserves the orthogonal-projector property. -/
theorem networkRelabelGate_isOrthogonalProjector {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) {P : Matrix I I ℂ}
    (hP : IsOrthogonalProjector P) : IsOrthogonalProjector (relabelGate e P) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨?_, ?_⟩
  · show relabelGate e P * relabelGate e P = relabelGate e P
    rw [← teleportRelabelGate_mul, h1]
  · show star (relabelGate e P) = relabelGate e P
    rw [Matrix.star_eq_conjTranspose, teleportRelabelGate_conjTranspose,
      ← Matrix.star_eq_conjTranspose]
    exact congrArg (relabelGate e) h2

/-- Lifting an orthogonal projector by an identity tensor factor preserves the
orthogonal-projector property. -/
theorem networkStepLiftGate_isOrthogonalProjector {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    {P : Operator s} (hP : IsOrthogonalProjector P) :
    IsOrthogonalProjector (networkStepLiftGate e P) := by
  have hT : IsOrthogonalProjector (TensorGate P (1 : Operator t)) := by
    obtain ⟨h1, h2⟩ := hP
    refine ⟨?_, ?_⟩
    · show TensorGate P 1 * TensorGate P 1 = TensorGate P 1
      rw [tensorGate_mul, h1, Matrix.mul_one]
    · show star (TensorGate P 1) = TensorGate P 1
      rw [Matrix.star_eq_conjTranspose, tensorGate_conjTranspose, ← Matrix.star_eq_conjTranspose,
        ← Matrix.star_eq_conjTranspose]
      have hs1 : star (1 : Operator t) = 1 := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one]
      rw [hs1]
      exact congrArg (fun X => TensorGate X (1 : Operator t)) h2
  exact networkRelabelGate_isOrthogonalProjector e hT

/-- Lifting an observed circuit preserves well-formedness. -/
theorem networkStepLift_wellFormed {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D) :
    ∀ P : ObservedCircuit (Fin s), observedWellFormed P →
      observedWellFormed (networkStepLift e P) := by
  intro P
  induction P with
  | halt b => intro _; trivial
  | step st next ih =>
    cases st with
    | gate U => intro h; exact ⟨networkStepLiftGate_unitary e h.1, ih h.2⟩
    | query => intro h; exact ih h
  | measure k l nexts ih => intro h o; exact ih o (h o)
  | project Q onFalse onTrue ihFalse ihTrue =>
    intro h
    exact ⟨networkStepLiftGate_isOrthogonalProjector e h.1, ihFalse h.2.1, ihTrue h.2.2⟩

/-- Prepending a lifted operation to a lifted leaf equals lifting the leaf obtained by
prepending the original operation. -/
theorem networkStepLiftLeaf_prepend {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    (U : Operator s) (q g c : ℕ) (outcomes : List (ℕ × ℕ)) (L : ObservedKrausLeaf s) :
    ObservedKrausLeaf.prepend (networkStepLiftGate e U) q g c outcomes (networkStepLiftLeaf e L)
      = networkStepLiftLeaf e (ObservedKrausLeaf.prepend U q g c outcomes L) := by
  simp only [ObservedKrausLeaf.prepend, networkStepLiftLeaf, networkStepLiftGate_mul]

/-- Pointwise equal finite functions produce equal lists under `List.ofFn`. -/
private theorem networkOfFn_congr {α : Type*} {n : ℕ} {f g : Fin n → α} (h : ∀ i, f i = g i) :
    List.ofFn f = List.ofFn g := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact List.map_congr_left (fun a _ => h a)

/-- The Kraus leaves of a lifted circuit with a lifted oracle are exactly the lifts of the
original circuit's Kraus leaves. -/
theorem observedKrausLeaves_networkStepLift {s t D : ℕ} (e : (Fin s × Fin t) ≃ Fin D)
    (oracle : Operator s) :
    ∀ P : ObservedCircuit (Fin s),
      observedKrausLeaves (networkStepLiftGate e oracle) (networkStepLift e P)
        = (observedKrausLeaves oracle P).map (networkStepLiftLeaf e) := by
  intro P
  induction P with
  | halt b =>
    simp only [networkStepLift, observedKrausLeaves, List.map_cons, List.map_nil,
      networkStepLiftLeaf, networkStepLiftGate_one]
  | step st next ih =>
    cases st with
    | gate U =>
      simp only [networkStepLift, observedKrausLeaves, ih, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun L _ => networkStepLiftLeaf_prepend e U 0 1 0 [] L)
    | query =>
      simp only [networkStepLift, observedKrausLeaves, ih, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun L _ => networkStepLiftLeaf_prepend e oracle 1 0 0 [] L)
  | measure k l nexts ih =>
    simp only [networkStepLift, observedKrausLeaves, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def, ih]
    congr 1
    refine networkOfFn_congr (fun o => ?_)
    refine List.map_congr_left (fun L _ => ?_)
    rw [← networkStepLiftGate_projector e l o]
    exact networkStepLiftLeaf_prepend e _ 0 0 1 [(k, o.val)] L
  | project Q onFalse onTrue ihFalse ihTrue =>
    simp only [networkStepLift, observedKrausLeaves, List.map_append,
      List.map_map, Function.comp_def, ihFalse, ihTrue]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left (fun L _ => ?_)
      rw [← networkStepLiftGate_one, ← networkStepLiftGate_sub]
      exact networkStepLiftLeaf_prepend e (1 - Q) 0 0 1 [(2, 0)] L
    · exact List.map_congr_left (fun L _ => networkStepLiftLeaf_prepend e Q 0 0 1 [(2, 1)] L)
end Qatlib.Concepts.MbqcFlow.FlowDecision
