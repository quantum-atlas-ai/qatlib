/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpectra04.EndToEnd.WalkApplicationSourceDefs
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution

/-!
# Exact decoding and marked-mass output laws

A finite set of witnesses at each vertex determines a decoder and a success functional. This
module proves decoder soundness, identifies the success mass after the general detection
execution, and packages these facts in `WalkApplicationAccount` for the application setting of
[Szegedy2004].

The list `walkApplicationResidual` records additional application constructions beyond these
decoding and output-law results.

## Main statements

* `generalApplicationExecution_exact`: identifies execution success with the marked
  transition-row mass.
* `clause38_complete`: constructs the decoder and output-law account.
* `clause39_complete`: pairs decoder soundness with the exact execution law.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

namespace Qatlib.Papers.QWalkSpectra04.EndToEnd
namespace WalkApplicationSource

open Matrix
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution
open Qatlib.Papers.QWalkSpectra04.EndToEnd.WalkApplicationSourceDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- If the collision decoder returns `some e` at a vertex, then `e` belongs to that vertex's
witness set. -/
theorem generalCollisionDecoder_some {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (v : V) (e : E)
    (h : generalCollisionDecoder marked v = some e) : e ∈ marked v := by
  by_cases hne : (marked v).Nonempty
  · rw [generalCollisionDecoder, dif_pos hne] at h
    have heq : e = (marked v).min' hne := (Option.some.inj h).symm
    rw [heq]
    exact Finset.min'_mem _ hne
  · rw [generalCollisionDecoder, dif_neg hne] at h
    exact absurd h (by simp)

/-- The collision decoder returns `none` exactly when the vertex's witness set is not nonempty. -/
theorem generalCollisionDecoder_none_iff {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (v : V) :
    generalCollisionDecoder marked v = none ↔ ¬ (marked v).Nonempty := by
  by_cases hne : (marked v).Nonempty
  · rw [generalCollisionDecoder, dif_pos hne]
    simp only [Option.some_ne_none]
    exact ⟨fun hc => absurd hc (by simp), fun h => h hne⟩
  · rw [generalCollisionDecoder, dif_neg hne]
    exact ⟨fun _ => hne, fun _ => rfl⟩

/-- The collision success functional is the sum of squared state-coordinate norms over vertices
with a nonempty witness set. -/
theorem generalCollisionSuccess_eq {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (ψ : QState V) :
    generalCollisionSuccess marked ψ
      = ∑ v, if (marked v).Nonempty then ‖ψ v‖ ^ 2 else 0 := rfl

/-- For a general kernel row state, collision success is the sum of transition weights at
vertices with nonempty witness sets. -/
theorem generalCollisionSuccess_rowState {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    {E : Type} [LinearOrder E] (marked : GeneralVertex V → Finset E) :
    generalCollisionSuccess marked (generalRowState K p)
      = ∑ v, if (marked v).Nonempty then (K.weight p v : ℝ) else 0 := by
  unfold generalCollisionSuccess
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hne : (marked v).Nonempty
  · simp only [if_pos hne]
    have h : 0 ≤ (K.weight p v : ℚ) := K.nonnegative p v
    have h' : 0 ≤ ((K.weight p v : ℚ) : ℝ) := by exact_mod_cast h
    have h'' : 0 ≤ Real.sqrt ((K.weight p v : ℚ) : ℝ) := Real.sqrt_nonneg _
    simp only [generalRowState, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h'']
    exact Real.sq_sqrt h'
  · simp only [if_neg hne]

/-- A matrix action that negates the marked coordinates and fixes the others preserves collision
success when the marked set is exactly the set of vertices with witnesses. -/
theorem generalCollisionSuccess_check {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (S : Finset V) (ψ : QState V)
    (hS : ∀ v, v ∈ S ↔ (marked v).Nonempty)
    (R : Matrix V V ℂ)
    (hR : ∀ v, v ∈ S → (R *ᵥ ψ) v = -ψ v)
    (hR' : ∀ v, v ∉ S → (R *ᵥ ψ) v = ψ v) :
    generalCollisionSuccess (V := V) (E := E) marked (R *ᵥ ψ)
      = generalCollisionSuccess (V := V) (E := E) marked ψ := by
  unfold generalCollisionSuccess
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hne : (marked v).Nonempty
  · have hin : v ∈ S := (hS v).mpr hne
    rw [hR v hin]
    simp
  · have hout : v ∉ S := fun hv' => hne ((hS v).mp hv')
    rw [hR' v hout]

/-- When `S` consists exactly of vertices with nonempty witness sets, the general detection
execution has collision success equal to the transition-row mass on those vertices. -/
theorem generalApplicationExecution_exact {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    {E : Type} [LinearOrder E] (S : Finset (GeneralVertex V))
    (marked : GeneralVertex V → Finset E)
    (hS : ∀ v, v ∈ S ↔ (marked v).Nonempty) :
    generalCollisionSuccess (V := GeneralVertex V) (E := E) marked
        (generalDetectionExecution K p S)
      = ∑ v, if (marked v).Nonempty then (K.weight p v : ℝ) else 0 := by
  calc
    generalCollisionSuccess (V := GeneralVertex V) (E := E) marked
        (generalDetectionExecution K p S)
      = generalCollisionSuccess (V := GeneralVertex V) (E := E) marked
        (generalMarkedReflection S *ᵥ (generalRowState K p)) := by
        unfold generalDetectionExecution
        rw [generalCheckWord_evaluate]
        rw [generalIdealSetupWord_exact]
    _ = generalCollisionSuccess (V := GeneralVertex V) (E := E) marked (generalRowState K p) :=
        generalCollisionSuccess_check (V := GeneralVertex V) (E := E) marked S (generalRowState K p)
          hS (generalMarkedReflection S)
            (fun v hv => by
              rw [generalMarkedReflection_mulVec S (generalRowState K p) v]
              simp [hv])
            (fun v hv => by
              rw [generalMarkedReflection_mulVec S (generalRowState K p) v]
              simp [hv])
    _ = ∑ v, if (marked v).Nonempty then (K.weight p v : ℝ) else 0 :=
        generalCollisionSuccess_rowState K p marked

/-- The list of remaining application constructions concerning data loading, scheduling,
resource accounting, and the printed positive-identity program candidate. -/
def walkApplicationResidual : List String :=
  [ "the Johnson-data data-loading word and its relation to the general compiler are not built here",
    "the unknown-marked-mass schedule is not built here",
    "the fair-bit and elementary-gate ledgers of the application execution are not built here",
    "the printed +I per-K program candidate of Foundations-A03/G39 is not built here" ]

/-- The proposition packaging decoder soundness, exact failure characterization, and the
marked-mass output law of the general detection execution. -/
structure WalkApplicationAccount (V : ℕ) (K : GeneralKernel V) (p : GeneralVertex V)
    {E : Type} [LinearOrder E] (marked : GeneralVertex V → Finset E) : Prop where

  decoderSound : ∀ v e, generalCollisionDecoder marked v = some e → e ∈ marked v

  decoderExact : ∀ v, generalCollisionDecoder marked v = none
      ↔ ¬ (marked v).Nonempty

  outputLaw :
    generalCollisionSuccess (V := GeneralVertex V) (E := E) marked
        (generalDetectionExecution K p (generalMarkedVertices (V := GeneralVertex V) (E := E) marked))
      = ∑ v, if (marked v).Nonempty then (K.weight p v : ℝ) else 0

/-- Every general kernel row and finite witness assignment satisfy `WalkApplicationAccount`. -/
theorem clause38_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    {E : Type} [LinearOrder E] (marked : GeneralVertex V → Finset E) :
    WalkApplicationAccount V K p marked := by
  refine ⟨?_, ?_, ?_⟩
  · intro v e h
    exact generalCollisionDecoder_some marked v e h
  · intro v
    exact generalCollisionDecoder_none_iff marked v
  · exact generalApplicationExecution_exact K p
      (generalMarkedVertices (V := GeneralVertex V) (E := E) marked) marked (by
        intro v
        simp [generalMarkedVertices])

/-- The collision decoder is sound, and the general detection execution for the induced marked
set has success equal to its transition-row mass on vertices with witnesses. -/
theorem clause39_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    {E : Type} [LinearOrder E] (marked : GeneralVertex V → Finset E) :
    (∀ v e, generalCollisionDecoder marked v = some e → e ∈ marked v) ∧
      generalCollisionSuccess (V := GeneralVertex V) (E := E) marked
          (generalDetectionExecution K p (generalMarkedVertices (V := GeneralVertex V) (E := E) marked))
        = ∑ v, if (marked v).Nonempty then (K.weight p v : ℝ) else 0 := by
  exact ⟨fun v e h => generalCollisionDecoder_some marked v e h,
    generalApplicationExecution_exact K p
      (generalMarkedVertices (V := GeneralVertex V) (E := E) marked) marked (by
        intro v
        simp [generalMarkedVertices])⟩

end WalkApplicationSource
end Qatlib.Papers.QWalkSpectra04.EndToEnd
