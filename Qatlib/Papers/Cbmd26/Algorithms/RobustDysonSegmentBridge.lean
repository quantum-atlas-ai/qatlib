/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CoherentFreshWordBridge
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation

/-!
# Robust Amplification of Dyson Segments

`robustDysonWord` expands coherent oblivious amplitude amplification around a normalization-two
block encoding. For a unitary target and approximation error `δ ≤ 1`, it gives normalization
one, block-encoding error at most `5 * δ`, and workspace defect at most `sqrt (10 * δ)`.

`concatenateDysonWords` composes amplified segments in a shared frame. Choosing
`dysonSharedSegmentAccuracy m ε` controls the total workspace error, while
`freshDysonSegmentedWord` supplies exact query and gate counts for the fresh-register Taylor
implementation used in the CBMD algorithms of [WangEtAl2026].

## Main statements

* `robust_dyson_segment` gives the amplified encoding, workspace error, and threefold body-query
  cost.
* `fresh_dyson_amplified_counted` uses `3 * K` queries and `6 * K + 13` fixed gates.
* `dyson_segments_shared_frame` bounds the combined encoding error by `5 * m ^ 2 * δ` and
  workspace defect by `m * sqrt (10 * δ)`.
* `fresh_dyson_segments_counted` gives `3 * m * K` queries, `m * (6 * K + 13)` gates, and
  workspace error at most `ε`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

/-- For `0 ≤ δ ≤ 1`, the coherent oblivious amplitude amplification error is at most `5 * δ`. -/
theorem dyson_coherentOAAError_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    coherentOAAError δ ≤ 5 * δ := by
  have hs : δ ^ 2 ≤ δ := by nlinarith
  unfold coherentOAAError
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]

/-- Expands the coherent oblivious amplitude amplification word at frame `R` by substituting the
given Dyson body circuit. -/
def robustDysonWord {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (body : List (AdjointStep H)) (R : Matrix H I ℂ) :
    List (AdjointStep H) := substituteAdjointCircuit body (coherentOAAWord R)

/-- Amplifying a well-formed normalization-two encoding of a unitary target with `δ ≤ 1` yields
normalization one, error `5 * δ`, and workspace defect at most `sqrt (10 * δ)`. The expanded
word uses three times the body queries and `4 + 3 * adjointGateCount body` fixed gates. -/
theorem robust_dyson_segment {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (body : List (AdjointStep H))
    (V : Matrix I I ℂ) (R : Matrix H I ℂ) {δ : ℝ}
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hbody : WellFormedAdjointCircuit body)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : BlockEncoding V (evaluate O body) R R 2 δ) (hδ1 : δ ≤ 1) :
    WellFormedAdjointCircuit (robustDysonWord body R) ∧
    BlockEncoding V (evaluate O (robustDysonWord body R)) R R 1 (5 * δ) ∧
    adjointQueryCount (robustDysonWord body R) = 3 * adjointQueryCount body ∧
    adjointGateCount (robustDysonWord body R) = 4 + 3 * adjointGateCount body ∧
    ‖evaluate O (robustDysonWord body R) * R - R * V‖ ≤ Real.sqrt (10 * δ) := by
  obtain ⟨he, hq, hg, hw⟩ := coherent_oaa_expanded_subroutine O body R hbody h.right_isometry
  obtain ⟨hc0, hc⟩ := coherent_oaa_compressed_error V (evaluate O body) R δ hV h
  have hb : BlockEncoding V (evaluate O (robustDysonWord body R)) R R 1 (5 * δ) := by
    refine ⟨hw.evaluate_unitary hO, h.left_isometry, h.right_isometry,
      by norm_num, mul_nonneg (by norm_num) h.error_nonneg, ?_⟩
    simpa only [one_smul, robustDysonWord, he, norm_sub_rev] using!
      hc.trans (dyson_coherentOAAError_le h.error_nonneg hδ1)
  refine ⟨hw, hb, hq, hg, ?_⟩
  convert! shared_frame_defect V (evaluate O (robustDysonWord body R)) R (5 * δ) hV hb using 1
  congr 1
  ring

section Fresh
variable {A J I : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I]

private instance robustFreshWorkspaceDecEq (K : ℕ) :
    DecidableEq (FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (FreshSignals A K) (Bool × (J × (A × I)))
    (freshSignalsDecidableEq A K) inferInstance

private instance robustFreshLabelWorkspaceDecEq (K : ℕ) :
    DecidableEq (TaylorWordLabel J K × FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (TaylorWordLabel J K) (FreshQueryWorkspace A J I K)
    inferInstance (robustFreshWorkspaceDecEq K)

/-- The robustly amplified fresh-register Taylor LCU word, using padded coefficients and the
clean Taylor-label frame. -/
def freshDysonAmplifiedWord (j₀ : J) (a₀ : A) (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) :
    List (AdjointStep (TaylorWordLabel J K × FreshQueryWorkspace A J I K)) :=
  robustDysonWord
    (coherentFreshLCUWord j₀ (taylorEmptyLabel J K) K
      (routedFreshChoices j₀ K K le_rfl) (routedPaddedCoefficients K a))
    (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ a₀ K))

/-- A fresh Taylor LCU approximation of a unitary target, with coefficient mass at most two and
error `δ ≤ 1`, yields a well-formed normalization-one encoding of error `5 * δ` and
workspace defect at most `sqrt (10 * δ)`. Its amplified word uses `3 * K` queries and `6 * K
+ 13` fixed gates. -/
theorem fresh_dyson_amplified_counted (j₀ : J) (a₀ : A) (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ) (V : Matrix I I ℂ) {δ : ℝ}
    (ha : coefficientMass a ≤ 2)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀))
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (herr : ‖V - ∑ w : (Σ l : Fin (K + 1), Fin l.val → J),
      a w • taylorBranchWord B K K le_rfl (.inl w)‖ ≤ δ) (hδ1 : δ ≤ 1) :
    let O := parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U)
    let R := tagFrame (taylorEmptyLabel J K) (freshWordFrame (I := I) j₀ a₀ K)
    let cs := freshDysonAmplifiedWord (I := I) j₀ a₀ K a
    WellFormedAdjointCircuit cs ∧ O ∈ Matrix.unitaryGroup _ ℂ ∧
    BlockEncoding V (evaluate O cs) R R 1 (5 * δ) ∧
    adjointQueryCount cs = 3 * K ∧ adjointGateCount cs = 6 * K + 13 ∧
    ‖evaluate O cs * R - R * V‖ ≤ Real.sqrt (10 * δ) := by
  obtain ⟨hw, hO, hb, hq, hg⟩ := coherent_fresh_padded_lcu_counted j₀ a₀ K a B U ha henc
  have hδ : 0 ≤ δ := (norm_nonneg _).trans herr
  have hp := hb.perturb hδ herr
  simp only [zero_add] at hp
  obtain ⟨hw', hb', hq', hg', he'⟩ := robust_dyson_segment _ _ V _ hO hw hV hp hδ1
  (try dsimp only)
  refine ⟨hw', hO, hb', ?_, ?_, he'⟩
  · simpa only [freshDysonAmplifiedWord, hq] using! hq'
  · change adjointGateCount (robustDysonWord _ _) = _
    rw [hg', hg]
    omega

end Fresh

section Composition
variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Concatenates the segment words indexed by the supplied list of segment labels. -/
def concatenateDysonWords {m : ℕ} (cs : Fin m → List (AdjointStep H))
    (is : List (Fin m)) : List (AdjointStep H) := is.flatMap cs

/-- Evaluating the concatenated Dyson word equals evaluation of the corresponding list of
segment-evaluation matrices. -/
theorem concatenateDysonWords_evaluate {m : ℕ} (O : Matrix H H ℂ)
    (cs : Fin m → List (AdjointStep H)) (is : List (Fin m)) :
    evaluate O (concatenateDysonWords cs is) =
      unitaryFamilyEvaluate (fun i => evaluate O (cs i)) is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [concatenateDysonWords, List.flatMap_cons, evaluate_append,
      unitaryFamilyEvaluate, ← ih]

omit [Fintype H] [DecidableEq H] in

/-- The query and fixed-gate counts of a concatenated Dyson word are the sums of the
corresponding counts along its index list. -/
theorem concatenateDysonWords_cost {m : ℕ} (cs : Fin m → List (AdjointStep H))
    (is : List (Fin m)) :
    adjointQueryCount (concatenateDysonWords cs is) =
      (is.map (fun i => adjointQueryCount (cs i))).sum ∧
    adjointGateCount (concatenateDysonWords cs is) =
      (is.map (fun i => adjointGateCount (cs i))).sum := by
  induction is with
  | nil => exact ⟨rfl, rfl⟩
  | cons i is ih =>
    simpa only [concatenateDysonWords, List.flatMap_cons, adjointQueryCount_append,
      adjointGateCount_append, List.map_cons, List.sum_cons] using!
      And.intro (congrArg (adjointQueryCount (cs i) + ·) ih.1)
        (congrArg (adjointGateCount (cs i) + ·) ih.2)

/-- Concatenating well-formed Dyson segment words gives a well-formed adjoint circuit. -/
theorem concatenateDysonWords_wellFormed {m : ℕ} (cs : Fin m → List (AdjointStep H))
    (hs : ∀ i, WellFormedAdjointCircuit (cs i)) (is : List (Fin m)) :
    WellFormedAdjointCircuit (concatenateDysonWords cs is) := by
  induction is with
  | nil => intro c hc; simp [concatenateDysonWords] at hc
  | cons i is ih => exact Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append (hs i) ih

/-- Composing `m` unitary-target segment encodings on one isometric frame, each with
normalization one and error `5 * δ`, gives encoding error at most `5 * m ^ 2 * δ`. The
combined workspace defect is at most `m * sqrt (10 * δ)`. -/
theorem dyson_segments_shared_frame {m : ℕ} (O : Matrix H H ℂ)
    (cs : Fin m → List (AdjointStep H)) (V : Fin m → Matrix I I ℂ)
    (R : Matrix H I ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (hR : IsIsometry R)
    (hs : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ ∧
      BlockEncoding (V i) (evaluate O (cs i)) R R 1 (5 * δ)) :
    BlockEncoding (unitaryFamilyEvaluate V (unitaryFamilyWord m))
      (evaluate O (concatenateDysonWords cs (unitaryFamilyWord m)))
      R R 1 (5 * (m : ℝ) ^ 2 * δ) ∧
    ‖evaluate O (concatenateDysonWords cs (unitaryFamilyWord m)) * R -
      R * unitaryFamilyEvaluate V (unitaryFamilyWord m)‖ ≤
      (m : ℝ) * Real.sqrt (10 * δ) := by
  have he : sharedAncillaWordError (fun _ : Fin m => 5 * δ) = 5 * (m : ℝ) ^ 2 * δ := by
    simp only [sharedAncillaWordError, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_pow]
    rw [Real.sq_sqrt (show 0 ≤ 5 * δ by positivity)]
    ring
  have hb := shared_ancilla_heterogeneous_word_encoding H I m V
    (fun i => evaluate O (cs i)) R (fun _ => 5 * δ) hR hs
  rw [he, ← concatenateDysonWords_evaluate] at hb
  refine ⟨hb, ?_⟩
  have hf := shared_frame_defect _ _ R _
    (unitaryFamilyEvaluate_unitary V (fun i => (hs i).1) _) hb
  have hr : Real.sqrt (2 * (5 * (m : ℝ) ^ 2 * δ)) =
      (m : ℝ) * Real.sqrt (10 * δ) := by
    rw [show 2 * (5 * (m : ℝ) ^ 2 * δ) = (m : ℝ) ^ 2 * (10 * δ) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  rwa [hr] at hf

/-- The per-segment approximation tolerance `ε ^ 2 / (10 * m ^ 2)` for a target workspace error
`ε` across `m` shared-frame segments. -/
def dysonSharedSegmentAccuracy (m : ℕ) (ε : ℝ) : ℝ := ε ^ 2 / (10 * (m : ℝ) ^ 2)

/-- For positive `m` and `0 < ε ≤ 1`, the chosen segment tolerance is positive, at most one, and
satisfies `m * sqrt (10 * dysonSharedSegmentAccuracy m ε) = ε`. -/
theorem dysonSharedSegmentAccuracy_bounds {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < dysonSharedSegmentAccuracy m ε ∧ dysonSharedSegmentAccuracy m ε ≤ 1 ∧
      (m : ℝ) * Real.sqrt (10 * dysonSharedSegmentAccuracy m ε) = ε := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hd : (0 : ℝ) < 10 * (m : ℝ) ^ 2 := by positivity
  refine ⟨div_pos (sq_pos_of_pos hε) hd, ?_, ?_⟩
  · apply (div_le_one hd).mpr
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  · have he : 10 * dysonSharedSegmentAccuracy m ε = (ε / (m : ℝ)) ^ 2 := by
      unfold dysonSharedSegmentAccuracy
      field_simp
    rw [he, Real.sqrt_sq (div_nonneg hε.le hm0.le)]
    field_simp

/-- For positive `m` and `0 < ε ≤ 1`, segment encodings with error `5 *
dysonSharedSegmentAccuracy m ε` have combined workspace defect at most `ε`. -/
theorem dyson_segments_chosen_workspace_error {m : ℕ} (hm : 0 < m)
    (O : Matrix H H ℂ) (cs : Fin m → List (AdjointStep H))
    (V : Fin m → Matrix I I ℂ) (R : Matrix H I ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : IsIsometry R)
    (hs : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ ∧
      BlockEncoding (V i) (evaluate O (cs i)) R R 1
        (5 * dysonSharedSegmentAccuracy m ε)) :
    ‖evaluate O (concatenateDysonWords cs (unitaryFamilyWord m)) * R -
      R * unitaryFamilyEvaluate V (unitaryFamilyWord m)‖ ≤ ε := by
  obtain ⟨hd, _, he⟩ := dysonSharedSegmentAccuracy_bounds hm hε hε1
  have h := (dyson_segments_shared_frame O cs V R hd.le hR hs).2
  rwa [he] at h

end Composition

section FreshFamily
variable {A J I : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I]

/-- Concatenates the amplified fresh-register Taylor LCU words for the segment coefficient
family in `unitaryFamilyWord` order. -/
def freshDysonSegmentedWord (j₀ : J) (a₀ : A) (K : ℕ) {m : ℕ}
    (a : Fin m → (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) :
    List (AdjointStep (TaylorWordLabel J K × FreshQueryWorkspace A J I K)) :=
  concatenateDysonWords (fun i => freshDysonAmplifiedWord (I := I) j₀ a₀ K (a i))
    (unitaryFamilyWord m)

/-- Under the chosen per-segment tolerance and coefficient-mass bound, the segmented fresh Dyson
word is well formed and encodes the unitary segment product with normalization one, error `ε
^ 2 / 2`, and workspace defect at most `ε`. It uses `3 * m * K` queries and `m * (6 * K +
13)` fixed gates. -/
theorem fresh_dyson_segments_counted (j₀ : J) (a₀ : A) (K : ℕ)
    {m : ℕ} (hm : 0 < m)
    (a : Fin m → (Σ l : Fin (K + 1), Fin l.val → J) → ℂ)
    (B : J → Matrix I I ℂ) (U : J → Matrix (A × I) (A × I) ℂ)
    (V : Fin m → Matrix I I ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : ∀ i, coefficientMass (a i) ≤ 2)
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀))
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ)
    (herr : ∀ i, ‖V i - ∑ w : (Σ l : Fin (K + 1), Fin l.val → J),
      a i w • taylorBranchWord B K K le_rfl (.inl w)‖ ≤ dysonSharedSegmentAccuracy m ε) :
    let O := parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U)
    let R := tagFrame (taylorEmptyLabel J K) (freshWordFrame (I := I) j₀ a₀ K)
    let cs := freshDysonSegmentedWord (I := I) j₀ a₀ K a
    WellFormedAdjointCircuit cs ∧ O ∈ Matrix.unitaryGroup _ ℂ ∧
    BlockEncoding (unitaryFamilyEvaluate V (unitaryFamilyWord m)) (evaluate O cs)
      R R 1 (ε ^ 2 / 2) ∧
    adjointQueryCount cs = 3 * m * K ∧
    adjointGateCount cs = m * (6 * K + 13) ∧
    ‖evaluate O cs * R - R * unitaryFamilyEvaluate V (unitaryFamilyWord m)‖ ≤ ε := by
  obtain ⟨hd, hd1, he⟩ := dysonSharedSegmentAccuracy_bounds hm hε hε1
  let O := parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U)
  let R := tagFrame (taylorEmptyLabel J K) (freshWordFrame (I := I) j₀ a₀ K)
  let cs := fun i => freshDysonAmplifiedWord (I := I) j₀ a₀ K (a i)
  have hs i := fresh_dyson_amplified_counted j₀ a₀ K (a i) B U (V i)
    (ha i) henc (hV i) (herr i) hd1
  have hs' : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ ∧
      BlockEncoding (V i) (evaluate O (cs i)) R R 1 (5 * dysonSharedSegmentAccuracy m ε) :=
    fun i => ⟨hV i, (hs i).2.2.1⟩
  have hR : IsIsometry R := (hs ⟨0, hm⟩).2.2.1.right_isometry
  obtain ⟨hb, hf⟩ := dyson_segments_shared_frame O cs V R hd.le hR hs'
  have he' : 5 * (m : ℝ) ^ 2 * dysonSharedSegmentAccuracy m ε = ε ^ 2 / 2 := by
    unfold dysonSharedSegmentAccuracy
    have hm0 : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
    field_simp
    ring
  rw [he'] at hb
  rw [he] at hf
  have hq : ∀ i, adjointQueryCount (cs i) = 3 * K := fun i => (hs i).2.2.2.1
  have hg : ∀ i, adjointGateCount (cs i) = 6 * K + 13 := fun i => (hs i).2.2.2.2.1
  have hc := concatenateDysonWords_cost cs (unitaryFamilyWord m)
  (try dsimp only)
  refine ⟨concatenateDysonWords_wellFormed cs (fun i => (hs i).1) _,
    (hs ⟨0, hm⟩).2.1, hb, ?_, ?_, hf⟩
  · change adjointQueryCount (concatenateDysonWords cs (unitaryFamilyWord m)) = _
    rw [hc.1]
    simp [unitaryFamilyWord, List.map_ofFn, hq]
    ring
  · change adjointGateCount (concatenateDysonWords cs (unitaryFamilyWord m)) = _
    rw [hc.2]
    simp [unitaryFamilyWord, List.map_ofFn, hg]

end FreshFamily
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
