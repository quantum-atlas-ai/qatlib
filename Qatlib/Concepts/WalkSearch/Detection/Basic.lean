/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.Spectral.BipartiteTauCorrespondenceConsumers
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralBounds

/-!
# Szegedy detection guarantees

The module exposes the corrected Szegedy detector's program semantics and instruction counts,
together with its relation to the unmarked bipartite walk and discriminant. It records zero
detection for empty marked sets and a threshold-event bound for nonempty marked mass.

`source_theorem_two_random_power_detection` gives constant average detection probability over a
sufficiently long range of positive walk powers, with explicit resource bounds. See
[Szegedy2004] for the mathematical background.

## Main statements

* `source_find_marked_program`: unitary semantics and exact counts.
* `source_section_seven_unmarked_bridge`: the bipartite-walk identity.
* `source_theorem_two_random_power_detection`: average success and resource bounds.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.WalkSearch.Detection.Basic

/-- Given a transition matrix and a unitary row preparation, the detector program is unitary,
produces the marked interference state, and has counts `(4 * K + 1, 4 * K + 1, 4 * K + 2)`.
See [Szegedy2004]. -/
theorem source_find_marked_program
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (j : I)
    (U : Matrix (I × I) (I × I) ℂ) (K : ℕ)
    (hP : IsTransitionMatrix P)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    detectionEvaluate U S (detectionProgram j K) ∈ Matrix.unitaryGroup (DetectionSpace I) ℂ ∧
    detectionEvaluate U S (detectionProgram j K) *ᵥ detectionStart j =
      detectionMarkGate S *ᵥ
        detectionInterference (correctedMarkedWalk P S) (detectionInitial P) K ∧
    detectionCounts (detectionProgram j K) = (4 * K + 1, 4 * K + 1, 4 * K + 2) :=
  corrected_szegedy_actual_detector_and_counts I P S j U K hP hU hp

/-- Each of the detector's row-query, marker, and fixed-gate counts is at most `4 * K + 2`. See
[Szegedy2004]. -/
theorem source_find_marked_instruction_bound
    (I : Type) [DecidableEq I] (j : I) (K : ℕ) :
    (detectionCounts (detectionProgram j K)).1 ≤ 4 * K + 2 ∧
    (detectionCounts (detectionProgram j K)).2.1 ≤ 4 * K + 2 ∧
    (detectionCounts (detectionProgram j K)).2.2 ≤ 4 * K + 2 := by
  rw [detectionProgram_actual_counts]
  refine ⟨?_, ?_, ?_⟩
  · show 4 * K + 1 ≤ 4 * K + 2
    omega
  · show 4 * K + 1 ≤ 4 * K + 2
    omega
  · show 4 * K + 2 ≤ 4 * K + 2
    omega

/-- For a symmetric transition matrix, identifies the corrected marked walk with the bipartite
walk of the unmarked row frame and its swapped frame, and identifies its discriminant with
the stated off-diagonal principal-matrix blocks. See [Szegedy2004]. -/
theorem source_section_seven_unmarked_bridge
    (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ) (S : Finset I)
    (hP : IsTransitionMatrix P) (hsym : ∀ i j, P i j = P j i) :
    correctedMarkedWalk P S =
        bipartiteWalk (unmarkedRowFrame P S) (SwapGate * unmarkedRowFrame P S) ∧
    bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate * unmarkedRowFrame P S) =
      Matrix.fromBlocks 0 (unmarkedPrincipal P S) (unmarkedPrincipal P S) 0 :=
  corrected_marked_walk_bipartite_bridge I P S hP hsym

/-- For a symmetric transition matrix and a unitary row preparation, the detector accepts with
probability zero for an empty marked set at every power. See [Szegedy2004]. -/
theorem source_section_seven_empty_interference
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ) (K : ℕ)
    (hP : IsTransitionMatrix P) (hsym : ∀ i l, P i l = P l i)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    detectionProbability U ∅ j K = 0 :=
  corrected_szegedy_empty_mark_one_sided I P j U K hP hsym hU hp

/-- Under the stated symmetric-chain gap assumptions and positive marked fraction, the corrected
walk's threshold mass at `lemma3Length` is at least `1 / 6`. See [Szegedy2004]. -/
theorem source_section_seven_threshold_event
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (ha : 0 < markedFraction S) :
    (1 / 6 : ℝ) ≤ lemma3ThresholdMass (correctedMarkedWalk P S)
      (detectionUnmarkedInitial P S) (lemma3Length δ (markedFraction S)) := by
  have hth := lemma3_threshold_event P S δ (lemma3Length δ (markedFraction S))
    hδ hδ1 hgap ha rfl
  have hLpos' : (0 : ℝ) < (lemma3Length δ (markedFraction S) : ℝ) := by
    exact_mod_cast hth.1
  unfold lemma3ThresholdMass
  rw [le_div_iff₀ hLpos']
  have hring : (1 / 6 : ℝ) * ((lemma3Length δ (markedFraction S) : ℝ)) =
      ((lemma3Length δ (markedFraction S) : ℝ)) / 6 := by ring
  rw [hring]
  exact hth.2

/-- For a symmetric transition matrix and a unitary row preparation, the average detection
probability for an empty marked set is zero over any range of positive powers. See
[Szegedy2004]. -/
theorem source_theorem_two_empty_marks
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ) (L : ℕ)
    (hP : IsTransitionMatrix P) (hsym : ∀ i l, P i l = P l i)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (∑ k : Fin L, detectionProbability U ∅ j (k.val + 1)) / (L : ℝ) = 0 := by
  have hzero : (∑ k : Fin L, detectionProbability U ∅ j (k.val + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact corrected_szegedy_empty_mark_one_sided I P j U (k.val + 1) hP hsym hU hp
  rw [hzero, zero_div]

/-- Under the stated gap, marked-fraction, and unitary-preparation assumptions, `L ≥ 1000 / sqrt
(δ * ε)` gives average detection probability at least `1 / 32`, with row-query and marker
counts at most `4 * L + 1` and fixed-gate count at most `4 * L + 2`. See [Szegedy2004]. -/
theorem source_theorem_two_random_power_detection
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S)
    (hL : 0 < L) (hscale : 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ))
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hp : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (1 / 32 : ℝ) ≤
        (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ) ∧
    (∀ k : Fin L,
      (detectionCounts (detectionProgram j (k.val + 1))).1 ≤ 4 * L + 1 ∧
      (detectionCounts (detectionProgram j (k.val + 1))).2.1 ≤ 4 * L + 1 ∧
      (detectionCounts (detectionProgram j (k.val + 1))).2.2 ≤ 4 * L + 2) :=
  corrected_szegedy_actual_random_power_detection I P S δ ε L j U
    hδ hδ1 hgap hε hεp hL hscale hU hp

end Qatlib.Concepts.WalkSearch.Detection.Basic
