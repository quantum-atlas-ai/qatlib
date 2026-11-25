/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinClock
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan

@[expose] public section

/-!
# Spectral reference for the stopped stencil solver

The variable-time construction used in [ChenXueChenEtAl2022], Appendix C.3,
assigns each spectral component to its first accepting threshold. The
reference state below keeps untested components on the clean tape and
keeps each accepted packet on its own clock label, after the same
reciprocal as the executable stage.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath
  (ApplyGate Inner Ket QState TensorGate TensorState applyGate_eq_mulVec_ket applyGate_mul applyGate_one
    ket_apply tensorGate_unitary)
open Qatlib.Foundations.PureStateMath.BornBridge
  (inner_euclidean_fromVec relabelState toEuclidean_fromVec toVec_fromEuclidean
    toVec_fromEuclidean_toEuclidean_fromVec)
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse Projector collapse_apply)
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement (projector_isOrthogonalProjector)
open Qatlib.Foundations.QueryWordCore.Circuit (Run)
open Qatlib.Concepts.GramQueryCore.ModelSemantics (sourceNormal_euclidean_eigenbasis)
open Qatlib.Concepts.LchsSimulation.StaticLchs (norm_applyGate_of_mem_unitaryGroup)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (walk walk_unitary)
open Qatlib.Concepts.QlsReadoutSpec.Amplification (Clause4StoppedStageTransport_answer)
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter (spectralTargetState)
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout (phaseFlagEmbed)
open Qatlib.Concepts.WalkSearch.MultiBandFilter (bandEmbed bandEmbed_sub)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical

variable {n : ℕ} {J M N : Type} [Fintype J] [DecidableEq J]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

/-- The coefficient of a spectral component still running before the given stage. -/
def runningBinWeight (threshold : Fin n → ℝ) (eigenvalue : J → ℝ) (c : J → ℂ) (elapsed : ℕ) (j : J) : ℂ :=
  if ∀ s : Fin n, s.val < elapsed → |eigenvalue j| < threshold s then c j else 0

/-- The coefficient sent to the first accepting bin at the given stage. -/
def acceptingBinWeight (threshold : Fin n → ℝ) (eigenvalue : J → ℝ) (c : J → ℂ) (t : Fin n) (j : J) : ℂ :=
  if threshold t ≤ |eigenvalue j| then runningBinWeight threshold eigenvalue c t.val j else 0

omit [Fintype J] [DecidableEq J] in
/-- A surviving coefficient is split between acceptance at the next test and continued running. -/
theorem running_bin_weight_split (threshold : Fin n → ℝ) (eigenvalue : J → ℝ)
    (c : J → ℂ) (t : Fin n) (j : J) :
    runningBinWeight threshold eigenvalue c t.val j =
      runningBinWeight threshold eigenvalue c (t.val + 1) j + acceptingBinWeight threshold eigenvalue c t j := by
  let before := ∀ s : Fin n, s.val < t.val → |eigenvalue j| < threshold s
  let after := ∀ s : Fin n, s.val < t.val + 1 → |eigenvalue j| < threshold s
  have hAfter : after ↔ before ∧ |eigenvalue j| < threshold t := by
    constructor
    · intro h
      exact ⟨fun s hs => h s (by omega), h t (by omega)⟩
    · rintro ⟨hBefore, hReject⟩ s hs
      by_cases he : s = t
      · simpa only [he] using hReject
      · have hne : s.val ≠ t.val := fun h => he (Fin.ext h)
        exact hBefore s (by omega)
  change (if before then c j else 0) = (if after then c j else 0) +
    (if threshold t ≤ |eigenvalue j| then (if before then c j else 0) else 0)
  by_cases hBefore : before
  · by_cases hReject : |eigenvalue j| < threshold t
    · simp only [ite_eq_left hBefore, ite_eq_left (hAfter.mpr ⟨hBefore, hReject⟩),
        ite_eq_right (not_le.mpr hReject), add_zero]
    · have hNo : ¬after := fun h => hReject (hAfter.mp h).2
      simp only [ite_eq_left hBefore, ite_eq_right hNo, ite_eq_left (le_of_not_gt hReject), zero_add]
  · have hNo : ¬after := fun h => hBefore (hAfter.mp h).1
    simp only [ite_eq_right hBefore, ite_eq_right hNo, ite_self, add_zero]

omit [Fintype J] [DecidableEq J] in
/-- A covered eigenvalue contributes to precisely its first accepting bin. -/
theorem accepting_bin_weight_eq (threshold : Fin n → ℝ) (eigenvalue : J → ℝ) (c : J → ℂ)
    (t : Fin n) (j : J) (hCovered : ∃ s, threshold s ≤ |eigenvalue j|) :
    acceptingBinWeight threshold eigenvalue c t j =
      if t = firstThresholdBin threshold (eigenvalue j) hCovered then c j else 0 := by
  let first := firstThresholdBin threshold (eigenvalue j) hCovered
  have hSpec : threshold first ≤ |eigenvalue j| ∧
      ∀ s < first, |eigenvalue j| < threshold s :=
    first_threshold_bin_spec threshold (eigenvalue j) hCovered
  change acceptingBinWeight threshold eigenvalue c t j = if t = first then c j else 0
  by_cases hFirst : t = first
  · have hAccept : threshold t ≤ |eigenvalue j| := hFirst.symm ▸ hSpec.1
    have hRun : ∀ s : Fin n, s.val < t.val → |eigenvalue j| < threshold s :=
      fun s hs => hSpec.2 s (hFirst ▸ hs)
    simp only [acceptingBinWeight, runningBinWeight, ite_eq_left hAccept, ite_eq_left hRun, ite_eq_left hFirst]
  · by_cases hAccept : threshold t ≤ |eigenvalue j|
    · have hPast : first < t := lt_of_le_of_ne
        (le_of_not_gt fun h => (not_le.mpr (hSpec.2 t h)) hAccept) (fun h => hFirst h.symm)
      have hRun : ¬∀ s : Fin n, s.val < t.val → |eigenvalue j| < threshold s := fun h =>
        (not_le.mpr (h first hPast)) hSpec.1
      simp only [acceptingBinWeight, runningBinWeight, ite_eq_left hAccept, ite_eq_right hRun, ite_eq_right hFirst]
    · simp only [acceptingBinWeight, ite_eq_right hAccept, ite_eq_right hFirst]

/-- The reference clock has clean counter workspaces and can set only the current decision. -/
def binDecisionTape (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (t : Fin n) (b : Bool) : PhaseTape width :=
  fun s => (if s = t then b else false, (⟨0, hWidth s⟩, false))

/-- The rejected reference decision leaves every clock slot clean. -/
theorem bin_decision_tape_false (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (t : Fin n) :
    binDecisionTape width hWidth t false = cleanPhaseTape width hWidth := by
  funext s
  simp [binDecisionTape, cleanPhaseTape]

/-- A reference acceptance sets precisely its own decision bit. -/
theorem bin_decision_tape_true (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (t s : Fin n) :
    (binDecisionTape width hWidth t true s).1 = true ↔ s = t := by
  by_cases h : s = t <;> simp [binDecisionTape, h]

/-- Attach the specified phase label and the clean reciprocal tape to a signal packet. -/
def seededBinState (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ)
    (tape : PhaseTape width) (ψ : QState M) : QState (BinStageWorkspace width condition precision M) :=
  TensorState (Ket tape) (TensorState (Ket (cleanReciprocalTape condition precision)) ψ)

/-- The ideal solver sends the newly accepted packet through the actual reciprocal gate. -/
def idealBinAccepted (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ) (t : Fin n) :
    QState (BinStageWorkspace width condition precision M) :=
  ApplyGate (conditionalBinReciprocal width condition precision (commonBinMass condition precision) t C U)
    (seededBinState width condition precision (binDecisionTape width hWidth t true)
      (∑ j, acceptingBinWeight threshold eigenvalue c t j • v j))

/-- The ideal prefix is the sum of the running packet and all packets accepted so far. -/
def idealBinReference (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ) (elapsed : Fin (n + 1)) :
    QState (BinStageWorkspace width condition precision M) :=
  seededBinState width condition precision (cleanPhaseTape width hWidth)
      (∑ j, runningBinWeight threshold eigenvalue c elapsed.val j • v j) +
    ∑ t ∈ Finset.univ.filter (fun t : Fin n => t.val < elapsed.val),
      idealBinAccepted width hWidth condition threshold precision C U v c eigenvalue t

omit [DecidableEq J] [DecidableEq N] in
/-- At time zero the reference contains exactly the supplied packet on the clean tape. -/
theorem ideal_bin_reference_initial (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ) :
    idealBinReference width hWidth condition threshold precision C U v c eigenvalue 0 =
      seededBinState width condition precision (cleanPhaseTape width hWidth) (∑ j, c j • v j) := by
  simp [idealBinReference, runningBinWeight]

omit [DecidableEq J] [DecidableEq N] in
/-- If the schedule covers the spectrum, the terminal reference contains only emitted packets. -/
theorem ideal_bin_reference_terminal (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ)
    (hCovered : ∀ j, ∃ s, threshold s ≤ |eigenvalue j|) :
    idealBinReference width hWidth condition threshold precision C U v c eigenvalue (Fin.last n) =
      ∑ t, idealBinAccepted width hWidth condition threshold precision C U v c eigenvalue t := by
  have hReject (j : J) : ¬∀ s : Fin n, s.val < n → |eigenvalue j| < threshold s := by
    obtain ⟨s, hs⟩ := hCovered j
    exact fun h => (not_le.mpr (h s s.isLt)) hs
  have hZero : (∑ j, runningBinWeight threshold eigenvalue c n j • v j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [runningBinWeight, ite_eq_right (hReject j), zero_smul]
  have hSeed : seededBinState (M := M) width condition precision (cleanPhaseTape width hWidth) 0 = 0 := by
    funext p
    simp [seededBinState, TensorState]
  simp [idealBinReference, hZero, hSeed]

/-- The other clock slots of the clean input have no accepted decision. -/
private theorem clean_history_running (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (t : Fin n) :
    ¬phaseTapeStopped width t (fun s => cleanPhaseTape width hWidth s.val) := by
  rintro ⟨s, _, hs⟩
  simp [cleanPhaseTape] at hs

omit [Fintype M] [DecidableEq M] in
set_option maxHeartbeats 500000 in
/-- Routing a one-decision reference tape embeds the signal at the clean phase workspaces. -/
private theorem route_seeded_decision (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ) (t : Fin n) (b : Bool) (ψ : QState M) :
    let e := focusPhaseTape (I := ReciprocalTape condition precision × M) width t
    let history : RemainingPhaseTape width t := fun s => cleanPhaseTape width hWidth s.val
    seededBinState width condition precision (binDecisionTape width hWidth t b) ψ =
      relabelState e.symm (TensorState (Ket history) (TensorState (Ket b)
        (bandEmbed (width t) (hWidth t) (TensorState (Ket (cleanReciprocalTape condition precision)) ψ)))) := by
  intro e history
  let tape := binDecisionTape width hWidth t b
  let zero : Fin (width t) := ⟨0, hWidth t⟩
  have hRoute (x : ReciprocalTape condition precision × M) :
      e (tape, x) = (history, (b, (zero, (false, x)))) := by
    apply Prod.ext
    · funext s
      change tape s.val = cleanPhaseTape width hWidth s.val
      simp [tape, binDecisionTape, cleanPhaseTape, s.property]
    · change ((tape t).1, ((tape t).2.1, ((tape t).2.2, x))) = _
      simp [tape, binDecisionTape, zero]
  funext p
  let q := e p
  have hData : q.2.2.2.2 = p.2 := rfl
  have hPhase :
      p.1 = tape ↔ q = (history, (b, (zero, (false, q.2.2.2.2)))) := by
    rw [hData, ← hRoute p.2]
    change p.1 = tape ↔ e p = e (tape, p.2)
    rw [e.injective.eq_iff]
    exact ⟨fun hp => Prod.ext hp rfl, fun hp => congrArg Prod.fst hp⟩
  change Ket tape p.1 * (Ket (cleanReciprocalTape condition precision) p.2.1 * ψ p.2.2) =
    TensorState (Ket history) (TensorState (Ket b)
      (bandEmbed (width t) (hWidth t) (TensorState (Ket (cleanReciprocalTape condition precision)) ψ))) q
  have hKet : Ket tape p.1 = if q = (history, (b, (zero, (false, q.2.2.2.2)))) then 1 else 0 := by
    rw [ket_apply]
    by_cases hp : p.1 = tape
    · rw [ite_eq_left hp, ite_eq_left (hPhase.mp hp)]
    · rw [ite_eq_right hp, ite_eq_right (fun h => hp (hPhase.mpr h))]
  rw [hKet]
  rw [← hData]
  obtain ⟨old, decision, counter, flag, x⟩ := q
  simp only [Prod.mk.injEq, and_true, TensorState, bandEmbed, phaseFlagEmbed, ket_apply]
  by_cases hh : old = history <;> by_cases hb : decision = b <;>
    by_cases hc : counter = zero <;> cases flag <;>
      simp [hh, hb, hc, zero] at *

omit [DecidableEq N] in
set_option maxHeartbeats 500000 in
/-- A conditional reciprocal changes only coefficient and signal coordinates within its phase label. -/
private theorem reciprocal_on_phase_label (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ)
    (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (tape : PhaseTape width) (ψ : QState (ReciprocalTape condition precision × M))
    (p : BinStageWorkspace width condition precision M) (hp : p.1 ≠ tape) :
    ApplyGate (conditionalBinReciprocal width condition precision (commonBinMass condition precision) t C U)
      (TensorState (Ket tape) ψ) p = 0 := by
  rw [conditional_bin_reciprocal_action]
  let e := focusBinReciprocal (M := M) width condition precision t
  have hSlice : (fun q => TensorState (Ket tape) ψ (e.symm ((e p).1, q))) = 0 := by
    funext q
    change Ket tape p.1 * ψ (e.symm ((e p).1, q)).2 = 0
    simp [ket_apply, hp]
  rw [hSlice]
  simp [ApplyGate]

omit [DecidableEq J] [DecidableEq N] in
/-- A packet emitted by the ideal stage is supported on its own acceptance tape. -/
theorem ideal_bin_accepted_supported (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ) (t : Fin n)
    (p : BinStageWorkspace width condition precision M) (hp : p.1 ≠ binDecisionTape width hWidth t true) :
    idealBinAccepted width hWidth condition threshold precision C U v c eigenvalue t p = 0 :=
  reciprocal_on_phase_label width condition precision t C U _ _ p hp

omit [DecidableEq N] in
/-- The reciprocal leaves the unaccepted clean decision label and its entire packet fixed. -/
private theorem reciprocal_on_clean_phase (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ) (t : Fin n) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (ψ : QState M) :
    ApplyGate (conditionalBinReciprocal width condition precision (commonBinMass condition precision) t C U)
      (seededBinState width condition precision (cleanPhaseTape width hWidth) ψ) =
      seededBinState width condition precision (cleanPhaseTape width hWidth) ψ := by
  funext p
  by_cases hp : p.1 = cleanPhaseTape width hWidth
  · have hInactive : ¬firstBinAcceptance (width := width) t p.1 := by
      rw [hp]
      simp [firstBinAcceptance, cleanPhaseTape]
    rw [conditional_bin_reciprocal_action, ite_eq_right hInactive, applyGate_one, Equiv.symm_apply_apply]
  · unfold seededBinState
    rw [reciprocal_on_phase_label width condition precision t C U _ _ p hp]
    simp [TensorState, ket_apply, hp]

omit [DecidableEq J] in
set_option maxHeartbeats 500000 in
/-- A subsequent executable stage fixes the entire accepted reference packet, including its
reciprocal coefficient registers. -/
private theorem later_stage_fixes_ideal_accepted (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ) (s t : Fin n) (hst : s < t) :
    ApplyGate (stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U)
      (idealBinAccepted width hWidth condition threshold precision C U v c eigenvalue s) =
      idealBinAccepted width hWidth condition threshold precision C U v c eigenvalue s := by
  let V := stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U
  let ψ := idealBinAccepted width hWidth condition threshold precision C U v c eigenvalue s
  let S := binStoppedSet (M := M) width condition precision t.val
  have hProject : V * Projector S = Projector S := by
    have h := (bin_stage_legal width condition threshold precision C U hC hSelf hSq hWidth).2 t
    simpa only [bin_stage_oracle_succ, binClockProjection] using h
  have hCollapse : Collapse ψ S = ψ := by
    funext p
    rw [collapse_apply]
    split_ifs with hp
    · rfl
    · have hLabel : p.1 ≠ binDecisionTape width hWidth s true := by
        intro h
        apply hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr
          ⟨s, hst, by rw [h]; exact (bin_decision_tape_true width hWidth s s).2 rfl⟩⟩
      exact (reciprocal_on_phase_label width condition precision s C U _ _ p hLabel).symm
  calc
    ApplyGate V ψ = ApplyGate V (Collapse ψ S) := congrArg (ApplyGate V) hCollapse.symm
    _ = Collapse ψ S := by
      change ApplyGate V (ApplyGate (Projector S) ψ) = ApplyGate (Projector S) ψ
      rw [← applyGate_mul, hProject]
    _ = ψ := hCollapse

omit [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M] in
/-- Appending the clean coefficient tape commutes with a finite spectral sum. -/
private theorem seeded_spectral_sum {R : Type} (κ : QState R) (s : Finset J)
    (v : J → QState M) (c : J → ℂ) :
    ∑ j ∈ s, c j • TensorState κ (v j) = TensorState κ (∑ j ∈ s, c j • v j) := by
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TensorState, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1200000 in
/-- The error on the running part of the ideal prefix is the counted-phase error.
The accepted packet uses the actual reciprocal and the rejected packet keeps the clean tape. -/
private theorem running_reference_stage_error (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1) (t : Fin n)
    (v : J → QState M) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let pos : ∀ s, 0 < width s := fun s => by have := hWidth s; omega
    let running k := seededBinState width condition precision (cleanPhaseTape width pos)
      (∑ j, runningBinWeight threshold eigenvalue c k j • v j)
    let accepted := idealBinAccepted width pos condition threshold precision C U v c eigenvalue t
    ‖toEuclidean_fromVec (ApplyGate (stencilBinStage width condition precision
      (commonBinMass condition precision) t (threshold t) C U) (running t.val) -
      (running (t.val + 1) + accepted))‖ ≤
      Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
        (1 / (2 * Real.sqrt (width t) * η))) := by
  intro pos running accepted
  let history : RemainingPhaseTape width t := fun s => cleanPhaseTape width pos s.val
  let e := focusPhaseTape (I := ReciprocalTape condition precision × M) width t
  let clean := cleanReciprocalTape condition precision
  let extended j := TensorState (Ket clean) (v j)
  let before := runningBinWeight threshold eigenvalue c t.val
  let after := runningBinWeight threshold eigenvalue c (t.val + 1)
  let accepting := acceptingBinWeight threshold eigenvalue c t
  let packet (d : J → ℂ) : QState M := ∑ j, d j • v j
  let embedded (d : J → ℂ) := bandEmbed (width t) (pos t) (TensorState (Ket clean) (packet d))
  have hSplit : packet before = packet after + packet accepting := by
    change (∑ j, before j • v j) = (∑ j, after j • v j) + ∑ j, accepting j • v j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [show before j = after j + accepting j
      from running_bin_weight_split threshold eigenvalue c t j, add_smul]
  have hReject : embedded before - embedded accepting = embedded after := by
    unfold embedded
    rw [← bandEmbed_sub]
    congr 1
    rw [show TensorState (Ket clean) (packet before) - TensorState (Ket clean) (packet accepting) =
        TensorState (Ket clean) (packet before - packet accepting) by
      funext p
      simp [TensorState, mul_sub]]
    rw [hSplit, add_sub_cancel_right]
  have hSeed : bandEmbed (width t) (pos t) (∑ j, before j • extended j) = embedded before := by
    unfold extended embedded packet
    rw [seeded_spectral_sum]
  have hAccept :
      bandEmbed (width t) (pos t) (spectralTargetState extended before
        (Finset.univ.filter fun j => threshold t ≤ |eigenvalue j|)) = embedded accepting := by
    unfold extended embedded packet spectralTargetState
    rw [seeded_spectral_sum]
    apply congrArg (fun x => bandEmbed (width t) (pos t) (TensorState (Ket clean) x))
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : threshold t ≤ |eigenvalue j| <;> simp [hj, accepting, before, acceptingBinWeight]
  have hInput (d : J → ℂ) :
      relabelState e.symm (TensorState (Ket history) (TensorState (Ket false) (embedded d))) =
        seededBinState width condition precision (cleanPhaseTape width pos) (packet d) := by
    symm
    simpa only [bin_decision_tape_false] using
      route_seeded_decision width pos condition precision t false (packet d)
  let yes := seededBinState width condition precision (binDecisionTape width pos t true) (packet accepting)
  have hYes :
      relabelState e.symm (TensorState (Ket history) (TensorState (Ket true) (embedded accepting))) = yes :=
    (route_seeded_decision width pos condition precision t true (packet accepting)).symm
  have hIdeal :
      relabelState e.symm (TensorState (Ket history) (fun p =>
        if p.1 then embedded accepting p.2 else (embedded before - embedded accepting) p.2)) =
      seededBinState width condition precision (cleanPhaseTape width pos) (packet after) + yes := by
    rw [hReject, ← hInput after, ← hYes]
    funext p
    cases h : (e p).2.1 <;> simp [relabelState, TensorState, ket_apply, h]
  obtain ⟨hMassPos, hMass⟩ := common_bin_mass_bounds condition precision
  have hLocal := stencil_bin_stage_running_error width condition precision
    (commonBinMass condition precision) t (threshold t) C U hC hSelf hSq (hWidth t) hMassPos (hMass t)
    history (clean_history_running width pos t) clean v before phase eigenvalue η hη hHalf
    hCos hMargin hOrthogonal hSpectrum
  dsimp only at hLocal
  rw [hSeed, hAccept, hInput, hIdeal] at hLocal
  rw [show ApplyGate (conditionalBinReciprocal width condition precision (commonBinMass condition precision) t C U)
      (seededBinState width condition precision (cleanPhaseTape width pos) (packet after) + yes) =
      running (t.val + 1) + accepted by
    simp only [ApplyGate, Matrix.mulVec_add]
    exact congrArg (fun ψ => ψ + _) (reciprocal_on_clean_phase width pos condition precision t C U (packet after))]
    at hLocal
  exact hLocal

set_option maxHeartbeats 800000 in
/-- Omitting the reciprocal leaves the same error bound for the routed phase decision,
since the full stage applies one common unitary reciprocal to both compared states. -/
private theorem running_phase_reference_error (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1) (t : Fin n)
    (v : J → QState M) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let pos : ∀ s, 0 < width s := fun s => by have := hWidth s; omega
    let W := TensorGate (1 : Matrix (ReciprocalTape condition precision)
      (ReciprocalTape condition precision) ℂ) (walk C U)
    let running k := seededBinState width condition precision (cleanPhaseTape width pos)
      (∑ j, runningBinWeight threshold eigenvalue c k j • v j)
    let accepted := seededBinState width condition precision (binDecisionTape width pos t true)
      (∑ j, acceptingBinWeight threshold eigenvalue c t j • v j)
    ‖toEuclidean_fromVec (ApplyGate (routedMagnitudeStage width t W (threshold t)) (running t.val) -
      (running (t.val + 1) + accepted))‖ ≤
      Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
        (1 / (2 * Real.sqrt (width t) * η))) := by
  intro pos W running accepted
  let reciprocal := conditionalBinReciprocal width condition precision (commonBinMass condition precision) t C U
  let phaseGate := routedMagnitudeStage width t W (threshold t)
  obtain ⟨hMassPos, hMass⟩ := common_bin_mass_bounds condition precision
  have hUnitary : reciprocal ∈ Matrix.unitaryGroup _ ℂ :=
    conditional_bin_reciprocal_unitary width condition precision (commonBinMass condition precision)
      t C U hC hSelf hSq hMassPos (hMass t)
  have hClean : ApplyGate reciprocal (running (t.val + 1)) = running (t.val + 1) :=
    reciprocal_on_clean_phase width pos condition precision t C U _
  have hDifference : ApplyGate reciprocal
      (ApplyGate phaseGate (running t.val) - (running (t.val + 1) + accepted)) =
      ApplyGate (stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U)
        (running t.val) -
        (running (t.val + 1) + idealBinAccepted width pos condition threshold precision C U v c eigenvalue t) := by
    change reciprocal *ᵥ (phaseGate *ᵥ running t.val - (running (t.val + 1) + accepted)) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    rw [show reciprocal *ᵥ running (t.val + 1) = running (t.val + 1) from hClean]; rfl
  rw [← norm_applyGate_of_mem_unitaryGroup hUnitary, hDifference]
  exact running_reference_stage_error width hWidth condition threshold precision C U hC hSelf hSq t
    v c phase eigenvalue η hη hHalf hCos hMargin hOrthogonal hSpectrum

set_option maxHeartbeats 600000 in
/-- The routed phase decision acts as the identity on an entire packet whose tape
already records an earlier acceptance. -/
private theorem phase_stage_fixes_earlier_label (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ) (W : Matrix
      (ReciprocalTape condition precision × M) (ReciprocalTape condition precision × M) ℂ)
    (hW : W ∈ Matrix.unitaryGroup _ ℂ) (threshold : ℝ) (s t : Fin n) (hst : s < t) (ψ : QState M) :
    ApplyGate (routedMagnitudeStage width t W threshold)
      (seededBinState width condition precision (binDecisionTape width hWidth s true) ψ) =
    seededBinState width condition precision (binDecisionTape width hWidth s true) ψ := by
  let V := routedMagnitudeStage width t W threshold
  let seeded := seededBinState width condition precision (binDecisionTape width hWidth s true) ψ
  let S := binStoppedSet (M := M) width condition precision t.val
  let P := Projector S
  have hV : V ∈ Matrix.unitaryGroup _ ℂ := routed_magnitude_stage_unitary width t W hW (hWidth t) threshold
  have hProject : V * P = P := by
    apply ((Clause4StoppedStageTransport_answer.1 _ P V (projector_isOrthogonalProjector S) hV).1).mpr
    change Projector S * V = Projector S
    ext p q
    simp only [Projector, Matrix.diagonal_mul, Matrix.diagonal_apply]
    by_cases hp : p ∈ S
    · have hStopped : ∃ u, u < t ∧ (p.1 u).1 = true :=
        (Finset.mem_filter.mp hp).2.resolve_left (Nat.not_le_of_lt t.isLt)
      have he := routed_magnitude_stage_stopped width t W threshold (Ket q) p.1 p.2 hStopped
      rw [applyGate_eq_mulVec_ket, ket_apply] at he
      simpa only [hp, ite_true, one_mul] using he
    · simp [hp]
  have hCollapse : Collapse seeded S = seeded := by
    funext p
    rw [collapse_apply]
    split_ifs with hp
    · rfl
    · have hLabel : p.1 ≠ binDecisionTape width hWidth s true := by
        intro he
        apply hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨s, hst, by
          rw [he]
          exact (bin_decision_tape_true width hWidth s s).2 rfl⟩⟩
      simp [seeded, seededBinState, TensorState, ket_apply, hLabel]
  calc
    ApplyGate V seeded = ApplyGate V (Collapse seeded S) := congrArg (ApplyGate V) hCollapse.symm
    _ = Collapse seeded S := by
      change ApplyGate V (ApplyGate P seeded) = ApplyGate P seeded
      rw [← applyGate_mul, hProject]
    _ = seeded := hCollapse

/-- The phase-only reference keeps the rejected coefficients on the clean tape and
labels the accepted coefficients by their first accepting stage. -/
def idealPhaseBinReference (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (v : J → QState M) (c : J → ℂ)
    (eigenvalue : J → ℝ) (elapsed : Fin (n + 1)) : QState (BinStageWorkspace width condition precision M) :=
  seededBinState width condition precision (cleanPhaseTape width hWidth)
      (∑ j, runningBinWeight threshold eigenvalue c elapsed.val j • v j) +
    ∑ t ∈ Finset.univ.filter (fun t : Fin n => t.val < elapsed.val),
      seededBinState width condition precision (binDecisionTape width hWidth t true)
        (∑ j, acceptingBinWeight threshold eigenvalue c t j • v j)

set_option maxHeartbeats 900000 in
/-- After running all ordered phase tests, the actual word approximates the ideal labelled
spectral state. Only the still-running coefficients contribute to each stage's error. -/
theorem stencil_bin_phase_preparation_error (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (v : J → QState M) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (η : Fin n → ℝ) (hη : ∀ t, 0 < η t) (hHalf : ∀ t, η t ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ t j, 2 * Real.pi * η t < abs (|eigenvalue j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let pos : ∀ s, 0 < width s := fun s => by have := hWidth s; omega
    let W := TensorGate (1 : Matrix (ReciprocalTape condition precision)
      (ReciprocalTape condition precision) ℂ) (walk C U)
    let input := seededBinState width condition precision (cleanPhaseTape width pos) (∑ j, c j • v j)
    let output := idealPhaseBinReference width pos condition threshold precision v c eigenvalue (Fin.last n)
    ‖toEuclidean_fromVec (Run 1 (stencilPhaseProgram width threshold W) input - output)‖ ≤
      ∑ t, Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
        (1 / (2 * Real.sqrt (width t) * η t))) := by
  intro pos W input output
  let V t := routedMagnitudeStage width t W (threshold t)
  let ρ := idealPhaseBinReference width pos condition threshold precision v c eigenvalue
  have hW : W ∈ Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) (Matrix.mem_unitaryGroup_iff'.2 (walk_unitary C U hC hSelf hSq))
  have hStart : ρ 0 = input := by simp [ρ, input, idealPhaseBinReference, runningBinWeight]
  change ‖toEuclidean_fromVec (Run 1 (stencilPhaseProgram width threshold W) input - ρ (Fin.last n))‖ ≤ _
  rw [← hStart]
  apply ordered_stage_error V ρ _
    (fun t => routed_magnitude_stage_unitary width t W hW (pos t) (threshold t))
  intro t
  let stillRunning k := seededBinState width condition precision (cleanPhaseTape width pos)
    (∑ j, runningBinWeight threshold eigenvalue c k j • v j)
  let emitted s := seededBinState width condition precision (binDecisionTape width pos s true)
    (∑ j, acceptingBinWeight threshold eigenvalue c s j • v j)
  let prior := Finset.univ.filter fun s : Fin n => s.val < t.val
  have hStages : (Finset.univ.filter fun s : Fin n => s.val < t.val + 1) = insert t prior := by
    ext s
    by_cases h : s = t
    · subst s
      simp
    · have hne : s.val ≠ t.val := fun he => h (Fin.ext he)
      simp only [prior, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, h, false_or]
      omega
  have hPrior : ApplyGate (V t) (∑ s ∈ prior, emitted s) = ∑ s ∈ prior, emitted s := by
    simp only [ApplyGate, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact phase_stage_fixes_earlier_label width pos condition precision W hW (threshold t)
      s t (Finset.mem_filter.mp hs).2 _
  change ‖toEuclidean_fromVec (ApplyGate (V t) (stillRunning t.val + ∑ s ∈ prior, emitted s) -
    (stillRunning (t.val + 1) + ∑ s ∈ Finset.univ.filter (fun s : Fin n => s.val < t.val + 1), emitted s))‖ ≤ _
  rw [hStages, Finset.sum_insert (show t ∉ prior by simp [prior])]
  rw [show ApplyGate (V t) (stillRunning t.val + ∑ s ∈ prior, emitted s) =
      ApplyGate (V t) (stillRunning t.val) + ∑ s ∈ prior, emitted s by
    change V t *ᵥ _ = V t *ᵥ stillRunning t.val + _
    rw [Matrix.mulVec_add]
    exact congrArg (fun x => ApplyGate (V t) (stillRunning t.val) + x) hPrior]
  rw [show ApplyGate (V t) (stillRunning t.val) + (∑ s ∈ prior, emitted s) -
      (stillRunning (t.val + 1) + (emitted t + ∑ s ∈ prior, emitted s)) =
      ApplyGate (V t) (stillRunning t.val) - (stillRunning (t.val + 1) + emitted t) by abel]
  exact running_phase_reference_error width hWidth condition threshold precision C U hC hSelf hSq t
    v c phase eigenvalue (η t) (hη t) (hHalf t) hCos (hMargin t) hOrthogonal hSpectrum

set_option maxHeartbeats 1000000 in
/-- Applying an actual stage to the ideal prefix incurs error only on the still-running
spectral packet. Earlier acceptances are fixed, including their coefficient workspaces. -/
theorem ideal_bin_reference_stage_error (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1) (t : Fin n)
    (v : J → QState M) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let pos : ∀ s, 0 < width s := fun s => by have := hWidth s; omega
    let reference := idealBinReference width pos condition threshold precision C U v c eigenvalue
    ‖toEuclidean_fromVec (ApplyGate (stencilBinStage width condition precision
      (commonBinMass condition precision) t (threshold t) C U) (reference t.castSucc) - reference t.succ)‖ ≤
      Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
        (1 / (2 * Real.sqrt (width t) * η))) := by
  intro pos reference
  let stage := stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U
  let emitted := idealBinAccepted width pos condition threshold precision C U v c eigenvalue
  let stillRunning k := seededBinState width condition precision (cleanPhaseTape width pos)
    (∑ j, runningBinWeight threshold eigenvalue c k j • v j)
  let prior := Finset.univ.filter fun s : Fin n => s.val < t.val
  have hStages : (Finset.univ.filter fun s : Fin n => s.val < t.val + 1) = insert t prior := by
    ext s
    by_cases h : s = t
    · subst s
      simp
    · have hne : s.val ≠ t.val := fun he => h (Fin.ext he)
      simp only [prior, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, h, false_or]
      omega
  have hPrior : ApplyGate stage (∑ s ∈ prior, emitted s) = ∑ s ∈ prior, emitted s := by
    simp only [ApplyGate, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hst : s < t := (Finset.mem_filter.mp hs).2
    exact later_stage_fixes_ideal_accepted width pos condition threshold precision C U hC hSelf hSq
      v c eigenvalue s t hst
  change ‖toEuclidean_fromVec (ApplyGate stage (stillRunning t.val + ∑ s ∈ prior, emitted s) -
    (stillRunning (t.val + 1) + ∑ s ∈ Finset.univ.filter (fun s : Fin n => s.val < t.val + 1), emitted s))‖ ≤ _
  rw [hStages, Finset.sum_insert (show t ∉ prior by simp [prior])]
  rw [show ApplyGate stage (stillRunning t.val + ∑ s ∈ prior, emitted s) =
      ApplyGate stage (stillRunning t.val) + ∑ s ∈ prior, emitted s by
    change stage *ᵥ _ = stage *ᵥ stillRunning t.val + _
    rw [Matrix.mulVec_add]
    exact congrArg (fun ψ => ApplyGate stage (stillRunning t.val) + ψ) hPrior]
  rw [show ApplyGate stage (stillRunning t.val) + (∑ s ∈ prior, emitted s) -
      (stillRunning (t.val + 1) + (emitted t + ∑ s ∈ prior, emitted s)) =
      ApplyGate stage (stillRunning t.val) - (stillRunning (t.val + 1) + emitted t) by abel]
  exact running_reference_stage_error width hWidth condition threshold precision C U hC hSelf hSq t
    v c phase eigenvalue η hη hHalf hCos hMargin hOrthogonal hSpectrum

set_option maxHeartbeats 1000000 in
/-- For a spectral expansion of the QRAM residual, the actual encoded stencil program
approximates the explicit first-acceptance reference. The bound sums the classification errors
weighted by the spectral mass that is still running at each stage. -/
theorem stencil_bin_spectral_reference_error {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (v : J → QState (StencilWorkspace depth geometry.stencilSize columns)) (c : J → ℂ)
    (phase eigenvalue : J → ℝ) (η : Fin n → ℝ)
    (hη : ∀ t, 0 < η t) (hHalf : ∀ t, η t ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ t j, 2 * Real.pi * η t < abs (|eigenvalue j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch)
      (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch) *ᵥ v j =
        Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (hInput : (∑ j, c j • v j) = stencilWalkFrame depth rowScratch columnScratch *ᵥ liftedResidual residual) :
    let pos : ∀ s, 0 < width s := fun s => by have := hWidth s; omega
    let reference := idealBinReference width pos condition threshold precision
      (stencilWalkFrame depth rowScratch columnScratch)
      (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch) v c eigenvalue
    ‖toEuclidean_fromVec (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width pos condition threshold precision - reference (Fin.last n))‖ ≤
      ∑ t, Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
        (1 / (2 * Real.sqrt (width t) * η t))) := by
  intro pos reference
  let C := stencilWalkFrame depth rowScratch columnScratch
  let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
  obtain ⟨hC, hSelf, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hStart : reference 0 = stencilBinInput rowScratch columnScratch residual width pos condition precision := by
    change idealBinReference width pos condition threshold precision C U v c eigenvalue 0 = _
    rw [ideal_bin_reference_initial, hInput]
    rfl
  apply stencil_bin_output_error geometry coefficients entryScale rowScratch columnScratch residual
    width pos condition threshold precision hScale hEntry hColumns reference _ hStart
  intro t
  exact ideal_bin_reference_stage_error width hWidth condition threshold precision C U hC hSelf hSq t
    v c phase eigenvalue (η t) (hη t) (hHalf t) hCos (hMargin t) hOrthogonal hSpectrum

set_option maxHeartbeats 700000 in
/-- A single orthonormal phase basis of a unitary expands every packet in the same
coordinates. The real part of a unit-modulus eigenvalue is the cosine tested by the phase word. -/
theorem unitary_phase_basis (W : Matrix M M ℂ) (hW : W ∈ Matrix.unitaryGroup M ℂ) :
    ∃ (v : M → QState M) (c : QState M → M → ℂ) (phase eigenvalue : M → ℝ),
      (∀ j l, Inner (v j) (v l) = if j = l then 1 else 0) ∧
      (∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) ∧
      (∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j) ∧
      ∀ ψ, (∑ j, c ψ j • v j) = ψ := by
  have hLeft : Wᴴ * W = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hW
  have hRight : W * Wᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hW
  obtain ⟨basis, z, hBasis⟩ := sourceNormal_euclidean_eigenbasis M W (hLeft.trans hRight.symm)
  let v j := toVec_fromEuclidean (basis j)
  let c (ψ : QState M) j := basis.repr (toEuclidean_fromVec ψ) j
  let phase j := (z j).arg / (2 * Real.pi)
  have hEigen (j : M) : W *ᵥ v j = z j • v j :=
    congrArg toVec_fromEuclidean (hBasis j)
  have hNorm (j : M) : ‖z j‖ = 1 := by
    have h := norm_applyGate_of_mem_unitaryGroup hW (v j)
    change ‖toEuclidean_fromVec (W *ᵥ v j)‖ = ‖toEuclidean_fromVec (v j)‖ at h
    rw [hEigen] at h
    change ‖z j • basis j‖ = ‖basis j‖ at h
    simpa only [norm_smul, basis.orthonormal.norm_eq_one, mul_one] using h
  have hAngle (j : M) : 2 * Real.pi * phase j = (z j).arg := by
    dsimp only [phase]
    field_simp [Real.pi_ne_zero]
  refine ⟨v, c, phase, fun j => (z j).re, ?_, ?_, ?_, ?_⟩
  · intro j l
    rw [← inner_euclidean_fromVec, show toEuclidean_fromVec (v j) = basis j from rfl,
      show toEuclidean_fromVec (v l) = basis l from rfl]
    exact (orthonormal_iff_ite.mp basis.orthonormal) j l
  · intro j
    rw [hEigen]
    have hCast : 2 * Real.pi * Complex.I * (phase j : ℂ) = ((z j).arg : ℂ) * Complex.I := by
      calc
        _ = ((2 * Real.pi * phase j : ℝ) : ℂ) * Complex.I := by push_cast; ring
        _ = _ := by rw [hAngle]
    rw [hCast, show Complex.exp (((z j).arg : ℂ) * Complex.I) = z j by
      simpa only [hNorm, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I (z j)]
  · intro j
    have hn : z j ≠ 0 := by
      intro h
      have hz := hNorm j
      simp [h] at hz
    rw [hAngle, Complex.cos_arg hn, hNorm, div_one]
  · intro ψ
    have h := congrArg toVec_fromEuclidean (basis.sum_repr (toEuclidean_fromVec ψ))
    rw [toVec_fromEuclidean_toEuclidean_fromVec] at h
    simpa only [toVec_fromEuclidean, WithLp.ofLp_sum, WithLp.ofLp_smul, v, c] using h

set_option maxHeartbeats 700000 in
/-- The actual QRAM residual in the stencil frame admits a spectral phase expansion of the
actual encoded walk. The expansion includes endpoint phases through the unitary eigenbasis. -/
theorem stencil_qram_residual_phase_expansion {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns) :
    let M := StencilWorkspace depth geometry.stencilSize columns
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    ∃ (v : M → QState M) (c : M → ℂ) (phase eigenvalue : M → ℝ),
      (∀ j l, Inner (v j) (v l) = if j = l then 1 else 0) ∧
      (∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) ∧
      (∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j) ∧
      (∑ j, c j • v j) = C *ᵥ liftedResidual residual := by
  intro M C U
  obtain ⟨hC, hSelf, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  obtain ⟨v, c, phase, eigenvalue, hOrthogonal, hWalk, hCos, hComplete⟩ :=
    unitary_phase_basis (walk C U) (Matrix.mem_unitaryGroup_iff'.mpr (walk_unitary C U hC hSelf hSq))
  exact ⟨v, c (C *ᵥ liftedResidual residual), phase, eigenvalue, hOrthogonal, hWalk, hCos, hComplete _⟩

end Qatlib.Papers.QFVMChen22.TimeStep
