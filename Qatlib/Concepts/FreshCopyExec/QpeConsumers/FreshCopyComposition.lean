/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Composition of Fresh-Copy Schedules

This module composes partial swap interactions with fresh copies along finite angle schedules,
following the density matrix evolution setting of [LloydMohseniRebentrost2014]. The operator
runs `freshCopyRun` and `freshCopyReferenceRun` are related to the channel composition
`freshCopyProtocolChannel`.

## Main statements

* `fresh_copy_protocol_cptp_reference` identifies the reference-extended channel and proves
  positivity and trace preservation.
* `freshCopyResourceCounts_eq` counts one copy, partial swap gate, and discard per scheduled
  angle, with zero oracle queries.
* `fresh_copy_schedule_composition_cost` gives sequential composition and the corresponding
  resource counts.

## References

- [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-- The one-gate circuit applying the partial swap matrix at angle `θ` to two registers of
dimension `D`. -/
noncomputable def partialSwapStepCircuit (D : ℕ) (θ : ℝ) : Circuit (Fin D × Fin D) :=
  [Step.gate (partialSwapMatrix D θ)]

/-- The partial swap step circuit is unitary, has zero queries and one gate, and acts by the
partial swap matrix. -/
theorem partial_swap_step_actual_cost (D : ℕ) (θ : ℝ) (ψ : QState (Fin D × Fin D)) :
    IsUnitaryCircuit (partialSwapStepCircuit D θ) ∧ QueryCount (partialSwapStepCircuit D θ) = 0 ∧
    GateCount (partialSwapStepCircuit D θ) = 1 ∧
    Run 1 (partialSwapStepCircuit D θ) ψ = ApplyGate (partialSwapMatrix D θ) ψ := by
  refine ⟨(isUnitaryCircuit_gate _ _).mpr ⟨partialSwapMatrix_unitary D θ,
    isUnitaryCircuit_nil⟩, rfl, rfl, rfl⟩

/-- The output of sequential partial swap steps with fresh copies of `ρ`, applied in the order
of the angle list. -/
noncomputable def freshCopyRun {D : ℕ} (ρ : Operator D) (angles : List ℝ)
    (σ : Operator D) : Operator D :=
  angles.foldl (fun σ θ => partialSwapOutput ρ θ σ) σ

/-- The sequential fresh copy partial swap output on a system with an untouched reference
register of dimension `r`. -/
noncomputable def freshCopyReferenceRun {D : ℕ} (ρ : Operator D) (angles : List ℝ) (r : ℕ)
    (σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  angles.foldl (fun σ θ => partialSwapReferenceOutput ρ θ r σ) σ

/-- The quantum channel obtained by composing the fresh copy partial swap channels in schedule
order, starting from the identity channel. -/
noncomputable def freshCopyProtocolChannel {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (angles : List ℝ) : QuantumChannel D D :=
  angles.foldl (fun ch θ => (partialSwapChannel ρ hρ θ).comp ch) (QuantumChannel.id D)

/-- Starting the channel fold at an arbitrary channel composes the scheduled protocol map after
that initial channel map. -/
private theorem foldl_channel_map_init {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (angles : List ℝ) (b : QuantumChannel D D) :
    (angles.foldl (fun ch θ => (partialSwapChannel ρ hρ θ).comp ch) b).map
      = (freshCopyProtocolChannel ρ hρ angles).map.comp b.map := by
  induction angles generalizing b with
  | nil => rfl
  | cons t rest ih =>
      rw [List.foldl_cons, ih ((partialSwapChannel ρ hρ t).comp b),
        show (freshCopyProtocolChannel ρ hρ (t :: rest)).map
            = ((t :: rest).foldl (fun ch θ => (partialSwapChannel ρ hρ θ).comp ch)
                (QuantumChannel.id D)).map from rfl,
        List.foldl_cons, ih ((partialSwapChannel ρ hρ t).comp (QuantumChannel.id D))]
      rw [show ((partialSwapChannel ρ hρ t).comp b).map
            = (partialSwapChannel ρ hρ t).map.comp b.map from rfl,
        show ((partialSwapChannel ρ hρ t).comp (QuantumChannel.id D)).map
            = (partialSwapChannel ρ hρ t).map.comp (QuantumChannel.id D).map from rfl,
        show (QuantumChannel.id D).map = LinearMap.id from rfl,
        LinearMap.comp_id, ← LinearMap.comp_assoc]

/-- The channel map for an appended schedule applies the first schedule's map followed by the
second schedule's map. -/
theorem freshCopyProtocolChannel_map_append {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (xs ys : List ℝ) :
    (freshCopyProtocolChannel ρ hρ (xs ++ ys)).map
      = (freshCopyProtocolChannel ρ hρ ys).map.comp (freshCopyProtocolChannel ρ hρ xs).map := by
  show ((xs ++ ys).foldl (fun ch θ => (partialSwapChannel ρ hρ θ).comp ch)
      (QuantumChannel.id D)).map
      = (freshCopyProtocolChannel ρ hρ ys).map.comp (freshCopyProtocolChannel ρ hρ xs).map
  rw [List.foldl_append, foldl_channel_map_init]
  rfl

/-- Applying a scheduled channel fold to an operator equals folding the partial swap outputs
after the initial channel's action. -/
private theorem foldl_channel_apply {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (angles : List ℝ) (b : QuantumChannel D D)
    (σ : Operator D) :
    (angles.foldl (fun ch θ => (partialSwapChannel ρ hρ θ).comp ch) b).map σ
      = angles.foldl (fun σ θ => partialSwapOutput ρ θ σ) (b.map σ) := by
  induction angles generalizing b σ with
  | nil => rfl
  | cons t rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      exact congrArg (fun z => rest.foldl (fun σ θ => partialSwapOutput ρ θ σ) z)
        (partialSwapChannel_map ρ hρ t (b.map σ))

/-- The composed fresh copy protocol channel acts on every operator as `freshCopyRun`. -/
theorem freshCopyProtocolChannel_apply {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (angles : List ℝ) (σ : Operator D) :
    (freshCopyProtocolChannel ρ hρ angles).map σ = freshCopyRun ρ angles σ :=
  foldl_channel_apply ρ hρ angles (QuantumChannel.id D) σ

/-- For density-operator copies, tensoring the protocol channel with an identity reference gives
`freshCopyReferenceRun`. This reference run preserves positive semidefiniteness and trace. -/
theorem fresh_copy_protocol_cptp_reference {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (angles : List ℝ) (r : ℕ)
    (σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (freshCopyProtocolChannel ρ hρ angles).map σ = freshCopyReferenceRun ρ angles r σ ∧
    (σ.PosSemidef → (freshCopyReferenceRun ρ angles r σ).PosSemidef) ∧
    Matrix.trace (freshCopyReferenceRun ρ angles r σ) = Matrix.trace σ := by
  induction angles generalizing σ with
  | nil =>
      refine ⟨?_, fun h => h, rfl⟩
      rw [freshCopyReferenceRun]
      rfl
  | cons θ rest ih =>
      have hcomp : tensorLeft (freshCopyProtocolChannel ρ hρ (θ :: rest)).map σ
          = tensorLeft (freshCopyProtocolChannel ρ hρ rest).map
              (partialSwapReferenceOutput ρ θ r σ) := by
        rw [show θ :: rest = [θ] ++ rest from rfl,
          freshCopyProtocolChannel_map_append ρ hρ [θ] rest, tensorLeft_comp]
        have hsingle : (freshCopyProtocolChannel ρ hρ [θ]).map
            = (partialSwapChannel ρ hρ θ).map := by
          rw [freshCopyProtocolChannel, List.foldl_cons, List.foldl_nil]
          show (((partialSwapChannel ρ hρ θ).comp (QuantumChannel.id D))).map
              = (partialSwapChannel ρ hρ θ).map
          rw [show ((partialSwapChannel ρ hρ θ).comp (QuantumChannel.id D)).map
              = (partialSwapChannel ρ hρ θ).map.comp (QuantumChannel.id D).map from rfl,
            show (QuantumChannel.id D).map = LinearMap.id from rfl, LinearMap.comp_id]
        rw [hsingle]
        exact congrArg (tensorLeft (freshCopyProtocolChannel ρ hρ rest).map)
          (partial_swap_actual_reference_bridge ρ hρ θ r σ).symm
      obtain ⟨ih1, ih2, ih3⟩ := ih (partialSwapReferenceOutput ρ θ r σ)
      rw [freshCopyReferenceRun, List.foldl_cons]
      refine ⟨hcomp.trans ih1, ?_, ?_⟩
      · intro hσ
        exact ih2 ((partial_swap_reference_output_formula ρ hρ θ r σ).2.1 hσ)
      · exact ih3.trans (partial_swap_reference_output_formula ρ hρ θ r σ).2.2

/-- The scheduled counts of fresh copies, partial swap gates, discards, and oracle queries,
respectively. -/
noncomputable def freshCopyResourceCounts (D : ℕ) (angles : List ℝ) : ℕ × ℕ × ℕ × ℕ :=
  (angles.length, (angles.map (fun θ => GateCount (partialSwapStepCircuit D θ))).sum,
    angles.length, (angles.map (fun θ => QueryCount (partialSwapStepCircuit D θ))).sum)

/-- A schedule uses one fresh copy, one partial swap gate, and one discard per angle, and has
zero oracle queries. -/
theorem freshCopyResourceCounts_eq (D : ℕ) (angles : List ℝ) :
    freshCopyResourceCounts D angles = (angles.length, angles.length, angles.length, 0) := by
  have hsum1 : ∀ l : List ℝ, (l.map (fun _ => (1 : ℕ))).sum = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons t rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  have hsum0 : ∀ l : List ℝ, (l.map (fun _ => (0 : ℕ))).sum = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons t rest ih =>
        simp only [List.map_cons, List.sum_cons, zero_add]
        exact ih
  have hmap1 : angles.map (fun θ => GateCount (partialSwapStepCircuit D θ))
      = angles.map (fun _ => 1) := by
    apply List.map_congr_left
    intro θ _
    rfl
  have hmap0 : angles.map (fun θ => QueryCount (partialSwapStepCircuit D θ))
      = angles.map (fun _ => (0 : ℕ)) := by
    apply List.map_congr_left
    intro θ _
    rfl
  simp only [freshCopyResourceCounts, hmap1, hmap0, hsum1, hsum0]

/-- Appending two schedules composes their fresh copy runs in order and adds their copy, partial
swap gate, and discard counts. Both the combined and initial schedules have zero oracle
queries. -/
theorem fresh_copy_schedule_composition_cost {D : ℕ} (ρ σ : Operator D) (xs ys : List ℝ) :
    freshCopyRun ρ (xs++ys) σ = freshCopyRun ρ ys (freshCopyRun ρ xs σ) ∧
    freshCopyResourceCounts D (xs++ys) =
      (xs.length+ys.length, xs.length+ys.length, xs.length+ys.length, 0) ∧
    freshCopyResourceCounts D xs = (xs.length,xs.length,xs.length,0) := by
  refine ⟨?_, ?_, freshCopyResourceCounts_eq D xs⟩
  · exact List.foldl_append
  · rw [freshCopyResourceCounts_eq]
    simp only [List.length_append]

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
