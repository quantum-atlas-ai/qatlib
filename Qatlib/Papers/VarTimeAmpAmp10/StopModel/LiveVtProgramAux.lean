/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgram

/-!
# Semantics and cost of live program words

This module proves matrix composition, adjoint, legality, and access-time laws for `DataVtStep`
words. It identifies `liveAAWord` with prepared amplitude amplification and establishes legality
and normalization of scheduled cascade prefixes.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `liveAAWord_matrix`: matrix semantics of live amplification.
* `cascadeWord_time`: exact recursive access time.
* `cascadeWord_legal` and `cascadeWord_normalized`: cascade validity.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

noncomputable section
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical
variable {C : Type} [Fintype C] [DecidableEq C]

/-- Folding instruction matrices from an accumulator equals the word matrix multiplied by that
accumulator. -/
private theorem dataVtFold_acc (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep)
    (A : Matrix (VtSpace C) (VtSpace C) ℂ) :
    word.foldl (fun A s => dataVtStepMatrix stages history j₀ s*A) A =
      dataVtWordMatrix stages history j₀ word*A := by
  induction word generalizing A with
  | nil => simp [dataVtWordMatrix]
  | cons s word ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have hc : dataVtWordMatrix stages history j₀ (s::word) =
        dataVtWordMatrix stages history j₀ word*dataVtStepMatrix stages history j₀ s := by
      change word.foldl (fun A s => dataVtStepMatrix stages history j₀ s*A)
        (dataVtStepMatrix stages history j₀ s*1) = _
      rw [ih, mul_one]
    rw [hc, mul_assoc]

/-- The matrix of the empty data-register word is the identity. -/
@[simp] theorem dataVtWordMatrix_nil (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) : dataVtWordMatrix stages history j₀ [] = 1 := rfl

/-- The matrix of a concatenated word is the matrix of the second word multiplied by that of the
first. -/
theorem dataVtWordMatrix_append (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (u v : List DataVtStep) :
    dataVtWordMatrix stages history j₀ (u++v) =
      dataVtWordMatrix stages history j₀ v*dataVtWordMatrix stages history j₀ u := by
  rw [dataVtWordMatrix, List.foldl_append, dataVtFold_acc]
  rfl

/-- The matrix of a singleton word is the matrix of its instruction. -/
@[simp] theorem dataVtWordMatrix_singleton (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (s : DataVtStep) :
    dataVtWordMatrix stages history j₀ [s] = dataVtStepMatrix stages history j₀ s := by
  simp [dataVtWordMatrix]

/-- Every legal instruction has a unitary matrix when the stage sequence is growing-history
legal. -/
theorem dataVtStepMatrix_unitary (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (s : DataVtStep) (hs : DataVtStepLegal stages s) :
    dataVtStepMatrix stages history j₀ s ∈ Matrix.unitaryGroup (VtSpace C) ℂ := by
  have hmark (S : Finset (VtSpace C)) : preparedMark S ∈ Matrix.unitaryGroup (VtSpace C) ℂ :=
    (prepared_aa_reflection_and_access 1 j₀ S (Matrix.unitaryGroup _ _).one_mem).1
  cases s with
  | stageF i =>
    simpa [dataVtStepMatrix, List.getElem?_eq_getElem hs] using (hl.2.2.2 i hs).1
  | stageB i =>
    simpa [dataVtStepMatrix, List.getElem?_eq_getElem hs] using
      conjTranspose_mem_unitaryGroup (hl.2.2.2 i hs).1
  | sourceReflection => exact outerProduct_reflection_unitary (normalized_ket j₀)
  | goodReflection => exact hmark _
  | liveReflection => exact hmark _
  | reachedReflection i => exact hmark _

/-- Every legal data-register word has a unitary matrix for a growing-history legal stage
sequence. -/
theorem dataVtWordMatrix_unitary (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (word : List DataVtStep) (hw : DataVtWordLegal stages word) :
    dataVtWordMatrix stages history j₀ word ∈ Matrix.unitaryGroup (VtSpace C) ℂ := by
  induction word with
  | nil => exact (Matrix.unitaryGroup _ _).one_mem
  | cons s word ih =>
    rw [show s::word = [s]++word from rfl, dataVtWordMatrix_append, dataVtWordMatrix_singleton]
    exact (Matrix.unitaryGroup _ _).mul_mem
      (ih (fun t ht => hw t (List.mem_cons_of_mem s ht)))
      (dataVtStepMatrix_unitary stages history j₀ hl s (hw s List.mem_cons_self))

/-- Replacing an instruction by its inverse preserves its access time. -/
@[simp] theorem dataVtStepTime_inverse (s : DataVtStep) :
    dataVtStepTime (dataVtStepInverse s) = dataVtStepTime s := by cases s <;> rfl

/-- Inverting a data-register word preserves its access time. -/
theorem dataVtWordTime_inverse (word : List DataVtStep) :
    dataVtWordTime (dataVtWordInverse word) = dataVtWordTime word := by
  simp [dataVtWordTime, dataVtWordInverse, List.map_reverse, List.map_map, Function.comp_def]

/-- Access time is additive under concatenation of data-register words. -/
@[simp] theorem dataVtWordTime_append (u v : List DataVtStep) :
    dataVtWordTime (u++v) = dataVtWordTime u+dataVtWordTime v := by
  simp [dataVtWordTime]

/-- The access time of `k` live amplification rounds with preparation is `2 * k + 1` times the
preparation time. -/
theorem liveAAWord_time (word : List DataVtStep) (k : ℕ) :
    dataVtWordTime (liveAAWord word k) = (2*k+1)*dataVtWordTime word := by
  have hr : dataVtWordTime (liveAARound word) = 2*dataVtWordTime word := by
    simp only [liveAARound, dataVtWordTime_append, dataVtWordTime_inverse]
    simp only [dataVtWordTime, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      dataVtStepTime]
    omega
  have hf (n : ℕ) : dataVtWordTime (List.replicate n (liveAARound word)).flatten =
      n*dataVtWordTime (liveAARound word) := by
    induction n with
    | zero => simp [dataVtWordTime]
    | succ n ih => simp [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm]
  rw [liveAAWord, dataVtWordTime_append, hf, hr]
  ring

/-- The next cascade's access time is the previous time plus the next dyadic stage time,
multiplied by the scheduled odd amplification factor. -/
theorem cascadeWord_time (schedule : ℕ → ℕ) (i : ℕ) :
    dataVtWordTime (cascadeWord schedule (i+1)) =
      (2*schedule i+1)*(dataVtWordTime (cascadeWord schedule i)+2^i) := by
  rw [cascadeWord, liveAAWord_time, dataVtWordTime_append]
  rfl

/-- The marking matrix of a finite set is self-adjoint. -/
private theorem data_mark_selfadjoint (S : Finset (VtSpace C)) :
    (preparedMark S)ᴴ = preparedMark S := by
  simp [preparedMark, projector_conjTranspose]

/-- The matrix of an inverse instruction is the conjugate transpose of the original instruction
matrix. -/
theorem dataVtStepMatrix_inverse (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (s : DataVtStep) :
    dataVtStepMatrix stages history j₀ (dataVtStepInverse s) =
      (dataVtStepMatrix stages history j₀ s)ᴴ := by
  cases s with
  | stageF i => rfl
  | stageB i => exact (Matrix.conjTranspose_conjTranspose _).symm
  | sourceReflection => exact (reflectionAbout_conjTranspose
      (isOrthogonalProjector_outerProduct (normalized_ket j₀))).symm
  | goodReflection => exact (data_mark_selfadjoint _).symm
  | liveReflection => exact (data_mark_selfadjoint _).symm
  | reachedReflection i => exact (data_mark_selfadjoint _).symm

/-- The matrix of an inverse word is the conjugate transpose of the original word matrix. -/
theorem dataVtWordMatrix_inverse (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    dataVtWordMatrix stages history j₀ (dataVtWordInverse word) =
      (dataVtWordMatrix stages history j₀ word)ᴴ := by
  induction word with
  | nil => simp [dataVtWordInverse]
  | cons s word ih =>
    have he : dataVtWordInverse (s::word) = dataVtWordInverse word++[dataVtStepInverse s] := by
      simp [dataVtWordInverse]
    rw [he, dataVtWordMatrix_append, dataVtWordMatrix_singleton,
      dataVtStepMatrix_inverse, ih, show s::word = [s]++word from rfl,
      dataVtWordMatrix_append, dataVtWordMatrix_singleton, Matrix.conjTranspose_mul]

omit [DecidableEq C] in

/-- Inverting a legal data-register word preserves legality. -/
theorem dataVtWordInverse_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (word : List DataVtStep) (hw : DataVtWordLegal stages word) :
    DataVtWordLegal stages (dataVtWordInverse word) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  have h := hw t (List.mem_reverse.mp ht)
  cases t <;> exact h

/-- The matrix of one live amplification round equals the prepared amplification iterate for the
word matrix and live set. -/
theorem liveAARound_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    dataVtWordMatrix stages history j₀ (liveAARound word) =
      preparedAAIterate (dataVtWordMatrix stages history j₀ word) j₀ (liveSet C) := by
  simp only [liveAARound, dataVtWordMatrix_append, dataVtWordMatrix_singleton,
    dataVtWordMatrix_inverse, dataVtStepMatrix, preparedAAIterate]
  noncomm_ring

/-- The live amplification word has matrix equal to the `k`th power of the prepared iterate
followed by the preparation matrix. -/
theorem liveAAWord_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) (k : ℕ) :
    dataVtWordMatrix stages history j₀ (liveAAWord word k) =
      (preparedAAIterate (dataVtWordMatrix stages history j₀ word) j₀ (liveSet C))^k *
        dataVtWordMatrix stages history j₀ word := by
  have hr (n : ℕ) : dataVtWordMatrix stages history j₀ (List.replicate n (liveAARound word)).flatten =
      (preparedAAIterate (dataVtWordMatrix stages history j₀ word) j₀ (liveSet C))^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, dataVtWordMatrix_append, ih, liveAARound_matrix,
        pow_succ]
  exact (dataVtWordMatrix_append stages history j₀ _ _).trans (congrArg
    (fun A => A*dataVtWordMatrix stages history j₀ word) (hr k))

/-- For legal stages and preparation, the live amplification word produces the state of the
corresponding prepared amplitude-amplification circuit. -/
theorem liveAAWord_state (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (word : List DataVtStep) (hw : DataVtWordLegal stages word) (k : ℕ) :
    dataVtWordState stages history j₀ (liveAAWord word k) =
      Run (preparedMark (liveSet C))
        (preparedAACircuit (dataVtWordMatrix stages history j₀ word) j₀ k) (Ket j₀) := by
  rw [(prepared_aa_actual_circuit _ j₀ (liveSet C) k
    (dataVtWordMatrix_unitary stages history j₀ hl word hw)).2.2.2]
  simp only [dataVtWordState, liveAAWord_matrix, preparedAAState, ApplyGate, Matrix.mulVec_mulVec]

omit [DecidableEq C] in

/-- Live amplification of a legal preparation word remains legal for every number of rounds. -/
theorem liveAAWord_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (word : List DataVtStep) (hw : DataVtWordLegal stages word) (k : ℕ) :
    DataVtWordLegal stages (liveAAWord word k) := by
  have hr : DataVtWordLegal stages (liveAARound word) := by
    intro s hs
    simp only [liveAARound, List.mem_append, List.mem_singleton] at hs
    rcases hs with ((rfl | hi) | rfl) | hf
    · trivial
    · exact dataVtWordInverse_legal stages word hw s hi
    · trivial
    · exact hw s hf
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hw s hs
  · obtain ⟨w, hw', hs⟩ := List.mem_flatten.mp hs
    have he : w = liveAARound word := (List.mem_replicate.mp hw').2
    exact hr s (he ▸ hs)

omit [DecidableEq C] in

/-- Every cascade prefix whose length is at most the stage count is a legal data-register word. -/
theorem cascadeWord_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (schedule : ℕ → ℕ) (i : ℕ) (hi : i ≤ stages.length) :
    DataVtWordLegal stages (cascadeWord schedule i) := by
  induction i with
  | zero => intro s hs; simp [cascadeWord] at hs
  | succ i ih =>
    apply liveAAWord_legal
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih (by omega) s hs
    · have he := List.mem_singleton.mp hs
      subst s
      exact (by omega : i < stages.length)

/-- For a growing-history legal stage sequence, every valid cascade prefix sends the source ket
to a normalized state. -/
theorem cascadeWord_normalized (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (schedule : ℕ → ℕ) (i : ℕ) (hi : i ≤ stages.length) :
    Normalized (dataVtWordState stages history j₀ (cascadeWord schedule i)) :=
  normalized_applyGate (dataVtWordMatrix_unitary stages history j₀ hl _ (cascadeWord_legal stages schedule i hi))
    (normalized_ket j₀)

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
