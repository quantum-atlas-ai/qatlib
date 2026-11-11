/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportStat
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportAux

/-!
# Cascade prefix transport theorem

This module establishes `CascadePrefixTransport` for legal growing-history runs. The proof
propagates the live component and a reached bad remainder through stage execution and
amplification, while retaining legality, normalization, and the time recurrence.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `cascadePrefixTransport_answer`: proof of the cascade transport contract.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical

/-- Scheduled cascades satisfy the prefix invariants, time recurrence, and final good-component
proportionality in `CascadePrefixTransport`, corresponding to Algorithms 1–2 and equations
(4)–(6) of [Ambainis2012]. -/
theorem cascadePrefixTransport_answer : CascadePrefixTransport := by
  intro C _ _ stages history hl j₀ hj hs schedule
  have hinv : ∀ i, i ≤ stages.length →
      ∃ (a : ℂ) (b : QState (VtSpace C)),
        dataVtWordState stages history j₀ (cascadeWord schedule i) =
          a • Collapse (vtState stages i (Ket j₀)) (liveSet C)+b ∧
        (∀ p, b p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history i) ∧
        Collapse b (liveSet C) = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      have hmem : j₀ ∈ liveSet C := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      have hc : Collapse (Ket j₀) (liveSet C) = Ket j₀ := by
        funext p
        by_cases hp : p = j₀
        · subst p; simp [collapse_apply, hmem]
        · simp [collapse_apply, Ket, hp]
      refine ⟨1, 0, ?_, ?_, ?_⟩
      · simp [cascadeWord, dataVtWordState, vtState, vtRunMatrix, hc, applyGate_one]
      · intro p hp; exact False.elim (hp rfl)
      · funext p; simp [collapse_apply]
    | succ i ih =>
      intro hi
      have hil : i < stages.length := by omega
      obtain ⟨a, b, he, hb, _⟩ := ih (by omega)
      let word := cascadeWord schedule i++[DataVtStep.stageF i]
      have hw : DataVtWordLegal stages word := by
        intro s h
        rcases List.mem_append.mp h with h | h
        · exact cascadeWord_legal stages schedule i (by omega) s h
        · obtain rfl := List.mem_singleton.mp h
          exact hil
      obtain ⟨b', hstage, hb'⟩ := growing_stage_live_transport stages history j₀ hl hs i hil a b hb
      have hp : preparedAAState (dataVtWordMatrix stages history j₀ word) j₀ =
          a • Collapse (vtState stages (i+1) (Ket j₀)) (liveSet C)+b' := by
        change dataVtWordState stages history j₀ word = _
        dsimp [word, dataVtWordState]
        rw [dataVtWordMatrix_append, dataVtWordMatrix_singleton, applyGate_mul]
        change ApplyGate (stages.getD i 1)
            (dataVtWordState stages history j₀ (cascadeWord schedule i)) = _
        rw [List.getD_eq_getElem _ _ hil, he]
        exact hstage
      have hzero := collapse_bad_live_zero b' (fun p h => (hb' p h).1)
      obtain ⟨c, d, hout⟩ := live_aa_transport _ j₀
        (dataVtWordMatrix_unitary stages history j₀ hl word hw) (schedule i) _ b' a hp hzero
      have hbs : ∀ p, (d • b') p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history (i+1) := by
        intro p h
        apply hb' p
        intro h0
        exact h (by simp [Pi.smul_apply, h0])
      refine ⟨c*a, d • b', ?_, hbs, collapse_bad_live_zero _ (fun p h => (hbs p h).1)⟩
      rw [cascadeWord, liveAAWord_state stages history j₀ hl word hw]
      rw [(prepared_aa_actual_circuit _ j₀ (liveSet C) (schedule i)
        (dataVtWordMatrix_unitary stages history j₀ hl word hw)).2.2.2]
      exact hout
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact ⟨cascadeWord_legal stages schedule i hi,
      cascadeWord_normalized stages history j₀ hl schedule i hi, hinv i hi⟩
  · intro i _
    exact cascadeWord_time schedule i
  · obtain ⟨a, b, he, hb, _⟩ := hinv stages.length le_rfl
    refine ⟨a, ?_⟩
    rw [he]
    funext p
    by_cases hp : p ∈ goodSet C
    · have hlive : p ∈ liveSet C := Finset.mem_union_left _ hp
      have hb0 : b p = 0 := by
        by_contra hn
        have hbad := (nonlive_iff_bad p).mpr (hb p hn).1
        exact hbad hlive
      simp [collapse_apply, hp, hlive, hb0]
    · simp [collapse_apply, hp]

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
