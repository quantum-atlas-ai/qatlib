/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CoherentSampleBridge

/-!
# Common normalization of sample encodings

Introduces `reindexAdjointWord` and coherent Boolean padding through `coherentPaddingWord`.
Padding raises a block-encoding normalization to a common bound while retaining its error, and
gives uniformly normalized sample and first-order words from an original matrix oracle. These
results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `commonNormalization_blockEncoding`: raises the normalization using a Boolean LCU.
* `original_oracle_common_first_order`: packages first-order sample encodings and their exact
  circuit costs.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Foundations.InstrumentCore.Measurement
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

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

section Reindex
variable {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Reindexes the gate matrix of an adjoint instruction while preserving forward and backward
query tags. -/
def reindexAdjointStep (e : K ≃ H) : AdjointStep H → AdjointStep K
  | .gate V => .gate (V.submatrix e e)
  | .forward => .forward
  | .backward => .backward

/-- Reindexes every instruction of an adjoint word along an equivalence of basis types. -/
def reindexAdjointWord (e : K ≃ H) (cs : List (AdjointStep H)) : List (AdjointStep K) :=
  cs.map (reindexAdjointStep e)

/-- Evaluating a reindexed word against the reindexed oracle equals reindexing the original
evaluation. -/
theorem reindexAdjointWord_evaluate (e : K ≃ H) (U : Matrix H H ℂ)
    (cs : List (AdjointStep H)) :
    evaluate (U.submatrix e e) (reindexAdjointWord e cs) =
      (evaluate U cs).submatrix e e := by
  induction cs with
  | nil => simp [reindexAdjointWord, evaluate, Matrix.submatrix_one_equiv]
  | cons c cs ih =>
    change instructionMatrix (U.submatrix e e) (reindexAdjointStep e c) *
      evaluate (U.submatrix e e) (reindexAdjointWord e cs) =
      (instructionMatrix U c * evaluate U cs).submatrix e e
    rw [ih, ← Matrix.submatrix_mul_equiv _ _ e e e]
    cases c <;> simp [reindexAdjointStep, instructionMatrix, Matrix.conjTranspose_submatrix]

omit [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] in

/-- Reindexing preserves both the query count and the gate count of an adjoint word. -/
theorem reindexAdjointWord_cost (e : K ≃ H) (cs : List (AdjointStep H)) :
    adjointQueryCount (reindexAdjointWord e cs) = adjointQueryCount cs ∧
    adjointGateCount (reindexAdjointWord e cs) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [reindexAdjointWord, reindexAdjointStep,
      adjointQueryCount, adjointGateCount] at ih ⊢ <;> exact ih

/-- Reindexing preserves well-formedness of adjoint circuits. -/
theorem reindexAdjointWord_wellFormed (e : K ≃ H) {cs : List (AdjointStep H)}
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (reindexAdjointWord e cs) := by
  induction cs with
  | nil => simp [reindexAdjointWord]
  | cons c cs ih =>
    cases c <;> simp only [reindexAdjointWord, List.map_cons, reindexAdjointStep,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨relabelGate_mem_unitary hcs.1 e.symm, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs
end Reindex

section Padding
variable {J H I : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I]

/-- Defines the Boolean coefficients `(r + 1) / 2` and `(r - 1) / 2` used for normalization
padding. -/
def paddingCoefficients (r : ℝ) (b : Bool) : ℂ :=
  if b then ((r - 1) / 2 : ℝ) else ((r + 1) / 2 : ℝ)

/-- For `r` in the unit interval, the padding coefficients have total absolute mass one. -/
theorem paddingCoefficients_mass (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    coefficientMass (paddingCoefficients r) = 1 := by
  simp only [coefficientMass, Fintype.sum_bool, paddingCoefficients, Bool.false_eq_true,
    ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
  ring

/-- The two padding coefficients sum to `r`. -/
theorem paddingCoefficients_sum (r : ℝ) :
    (∑ b, paddingCoefficients r b) = (r : ℂ) := by
  simp [paddingCoefficients]
  ring

/-- Adds a Boolean spectator register to a selected word and reorders the registers. -/
def insertPaddingWord (cs : List (AdjointStep (J × H))) :
    List (AdjointStep (J × (Bool × H))) :=
  reindexAdjointWord (controlSpectatorEquiv J H).symm (spectatorLiftWord Bool cs)

/-- If a word evaluates to `select V`, inserting padding evaluates to the selected family of
Boolean spectator lifts of `V`. -/
theorem insertPaddingWord_evaluate (O : Matrix H H ℂ)
    (cs : List (AdjointStep (J × H))) (V : J → Matrix H H ℂ)
    (he : evaluate (parallelOracle O) cs = select V) :
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) O))
        (insertPaddingWord cs) = select (fun j => parallelOracle (J := Bool) (V j)) := by
  have ho : parallelOracle (J := J) (parallelOracle (J := Bool) O) =
      (parallelOracle (J := Bool) (parallelOracle (J := J) O)).submatrix
        (controlSpectatorEquiv J H).symm (controlSpectatorEquiv J H).symm := by
    ext ⟨j, b, i⟩ ⟨k, c, l⟩
    by_cases hj : j = k <;> by_cases hb : b = c <;>
      simp [parallelOracle, select, controlSpectatorEquiv, hj, hb]
  rw [ho, insertPaddingWord, reindexAdjointWord_evaluate, spectatorLiftWord_evaluate, he]
  ext ⟨j, b, i⟩ ⟨k, c, l⟩
  by_cases hj : j = k <;> by_cases hb : b = c <;>
    simp [parallelOracle, select, controlSpectatorEquiv, hj, hb]

omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in

/-- Inserting the padding register preserves query and gate counts. -/
theorem insertPaddingWord_cost (cs : List (AdjointStep (J × H))) :
    adjointQueryCount (insertPaddingWord cs) = adjointQueryCount cs ∧
    adjointGateCount (insertPaddingWord cs) = adjointGateCount cs := by
  exact ⟨(reindexAdjointWord_cost _ _).1.trans (spectatorLiftWord_cost _ _).1,
    (reindexAdjointWord_cost _ _).2.trans (spectatorLiftWord_cost _ _).2⟩

/-- Inserting the padding register preserves well-formedness. -/
theorem insertPaddingWord_wellFormed {cs : List (AdjointStep (J × H))}
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (insertPaddingWord cs) :=
  reindexAdjointWord_wellFormed _ (spectatorLiftWord_wellFormed Bool hcs)

/-- Surrounds a word with label-controlled coefficient preparation and phase gates for Boolean
normalization padding. -/
def coherentPaddingWord (r : J → ℝ) (cs : List (AdjointStep (J × H))) :
    List (AdjointStep (J × (Bool × H))) :=
  [.gate (select (fun j => (prepareRegister (I := H)
      (coefficientPrepare (paddingCoefficients (r j)) false))ᴴ)),
    .gate (select (fun j => coefficientLabelPhase (W := H) (paddingCoefficients (r j))))] ++
    insertPaddingWord cs ++
  [.gate (select (fun j => prepareRegister (I := H)
    (coefficientPrepare (paddingCoefficients (r j)) false)))]

/-- Coherent padding evaluates to the selected family of padding LCU unitaries. -/
theorem coherentPaddingWord_evaluate (r : J → ℝ) (O : Matrix H H ℂ)
    (cs : List (AdjointStep (J × H))) (V : J → Matrix H H ℂ)
    (he : evaluate (parallelOracle O) cs = select V) :
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) O))
        (coherentPaddingWord r cs) =
      select (fun j => coefficientLCUUnitary (paddingCoefficients (r j))
        (fun _ : Bool => V j) false) := by
  have hphase : ∀ j, coefficientLabelPhase (paddingCoefficients (r j)) *
      parallelOracle (J := Bool) (V j) =
      select (phaseAbsorbed (paddingCoefficients (r j)) (fun _ : Bool => V j)) := by
    intro j
    rw [coefficientLabelPhase, parallelOracle, parallel_select_mul]
    congr 1
    funext b
    simp [phaseAbsorbed]
  simp only [coherentPaddingWord, evaluate_append, evaluate, instructionMatrix,
    Matrix.mul_one, insertPaddingWord_evaluate O cs V he, parallel_select_mul]
  congr 1
  funext j
  rw [Matrix.mul_assoc _ (coefficientLabelPhase _) (parallelOracle _), hphase]
  rfl

omit [Fintype J] [Fintype H] [Fintype I] [DecidableEq I] in

/-- Coherent padding preserves the query count and adds exactly three gates. -/
theorem coherentPaddingWord_cost (r : J → ℝ) (cs : List (AdjointStep (J × H))) :
    adjointQueryCount (coherentPaddingWord r cs) = adjointQueryCount cs ∧
    adjointGateCount (coherentPaddingWord r cs) = adjointGateCount cs + 3 := by
  simp [coherentPaddingWord, (insertPaddingWord_cost cs).1,
    (insertPaddingWord_cost cs).2, adjointQueryCount, adjointGateCount]

/-- Coherent padding of a well-formed word is well formed when every padding ratio lies in the
unit interval. -/
theorem coherentPaddingWord_wellFormed (r : J → ℝ)
    (hr : ∀ j, r j ∈ Set.Icc (0 : ℝ) 1) {cs : List (AdjointStep (J × H))}
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (coherentPaddingWord r cs) := by
  have hp := fun j => prepareRegister_unitary (I := H)
    (coefficientPrepare_unitary (paddingCoefficients (r j)) false
      (by rw [paddingCoefficients_mass _ (hr j).1 (hr j).2]; norm_num))
  unfold coherentPaddingWord
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨select_unitary _ (fun j => adjoint_unitary (hp j)),
        select_unitary _ (fun j => coefficientLabelPhase_unitary _)⟩
    · exact insertPaddingWord_wellFormed hcs
  · simpa using select_unitary _ hp

/-- Compressing the padding LCU on the false-tagged frame multiplies the original compression by
`r` for `0 ≤ r ≤ 1`. -/
theorem padding_compress (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (V : Matrix H H ℂ) (F : Matrix H I ℂ) :
    compress (tagFrame false F)
        (coefficientLCUUnitary (paddingCoefficients r) (fun _ : Bool => V) false)
        (tagFrame false F) = (r : ℂ) • compress F V F := by
  have hm := paddingCoefficients_mass r hr0 hr1
  rw [compress_tagFrame, coefficientLCUUnitary_compress _ _ _ (by rw [hm]; norm_num), hm]
  simp only [Complex.ofReal_one, div_one, ← Finset.sum_smul, paddingCoefficients_sum]
  simp only [Matrix.mul_smul, Matrix.smul_mul, compress]

/-- A block encoding with normalization `β ≤ Λ` yields a padded block encoding with
normalization `Λ` and the same error. -/
theorem commonNormalization_blockEncoding (A : Matrix I I ℂ) (V : Matrix H H ℂ)
    (F : Matrix H I ℂ) (β Λ ε : ℝ) (henc : BlockEncoding A V F F β ε)
    (hβΛ : β ≤ Λ) :
    BlockEncoding A
      (coefficientLCUUnitary (paddingCoefficients (β / Λ)) (fun _ : Bool => V) false)
      (tagFrame false F) (tagFrame false F) Λ ε := by
  have hΛ : 0 < Λ := henc.normalization_pos.trans_le hβΛ
  have hr0 : 0 ≤ β / Λ := div_nonneg henc.normalization_pos.le hΛ.le
  have hr1 : β / Λ ≤ 1 := (div_le_one hΛ).2 hβΛ
  refine ⟨coefficientLCUUnitary_unitary _ _ _
    (by rw [paddingCoefficients_mass _ hr0 hr1]; norm_num) (fun _ => henc.unitary),
    tagFrame_isIsometry false F henc.left_isometry,
    tagFrame_isIsometry false F henc.right_isometry, hΛ, henc.error_nonneg, ?_⟩
  rw [padding_compress _ hr0 hr1]
  have he : Λ • ((β / Λ : ℝ) : ℂ) • compress F V F = β • compress F V F := by
    ext i k
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div]
    have hn : (Λ : ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
    field_simp
  rw [he]
  exact henc.error_le

end Padding

section Samples
variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

/-- Pads a sample input unitary using the ratio `α * sqrt (1 + s²) / Λ`. -/
def paddedSampleInputUnitary (U : Matrix W W ℂ) (α Λ s : ℝ) :
    Matrix (Bool × (Bool × W)) (Bool × (Bool × W)) ℂ :=
  coefficientLCUUnitary (paddingCoefficients (α * Real.sqrt (1 + s ^ 2) / Λ))
    (fun _ : Bool => sampleInputUnitary U α s) false

/-- Coherently pads the sample input word to the proposed common normalization `Λ`. -/
def paddedSampleInputWord (α Λ : ℝ) (s : J → ℝ) :
    List (AdjointStep (J × (Bool × (Bool × W)))) :=
  coherentPaddingWord (fun j => α * Real.sqrt (1 + (s j) ^ 2) / Λ)
    (coherentSampleInputWord α s)

/-- Pads a first-order input unitary using the ratio `α * sqrt (1 + s²) / Λ`. -/
def paddedFirstOrderInputUnitary (U : Matrix W W ℂ) (α Λ s : ℝ) :
    Matrix (Bool × (Bool × W)) (Bool × (Bool × W)) ℂ :=
  coefficientLCUUnitary (paddingCoefficients (α * Real.sqrt (1 + s ^ 2) / Λ))
    (fun _ : Bool => firstOrderInputUnitary U α s) false

/-- Coherently pads the first-order input word to the proposed common normalization `Λ`. -/
def paddedFirstOrderInputWord (α Λ : ℝ) (s : J → ℝ) :
    List (AdjointStep (J × (Bool × (Bool × W)))) :=
  coherentPaddingWord (fun j => α * Real.sqrt (1 + (s j) ^ 2) / Λ)
    (coherentFirstOrderInputWord α s)

/-- The padded sample input word evaluates to the selected family of padded sample unitaries. -/
theorem paddedSampleInputWord_evaluate (α Λ : ℝ) (s : J → ℝ) (U : Matrix W W ℂ) :
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) (controlOracle U)))
        (paddedSampleInputWord α Λ s) =
      select (fun j => paddedSampleInputUnitary U α Λ (s j)) :=
  coherentPaddingWord_evaluate _ _ _ _ (coherentSampleInputWord_evaluate α s U)

/-- The padded first-order input word evaluates to the selected family of padded first-order
unitaries. -/
theorem paddedFirstOrderInputWord_evaluate (α Λ : ℝ) (s : J → ℝ) (U : Matrix W W ℂ) :
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) (controlOracle U)))
        (paddedFirstOrderInputWord α Λ s) =
      select (fun j => paddedFirstOrderInputUnitary U α Λ (s j)) :=
  coherentPaddingWord_evaluate _ _ _ _ (coherentFirstOrderInputWord_evaluate α s U)

omit [Fintype J] [Fintype W] [Fintype I] [DecidableEq I] in

/-- The padded sample input word uses exactly two queries and eight gates. -/
theorem paddedSampleInputWord_cost (α Λ : ℝ) (s : J → ℝ) :
    adjointQueryCount (paddedSampleInputWord (W := W) α Λ s) = 2 ∧
    adjointGateCount (paddedSampleInputWord (W := W) α Λ s) = 8 := by
  obtain ⟨hq, hg⟩ := coherentPaddingWord_cost
    (fun j => α * Real.sqrt (1 + (s j) ^ 2) / Λ) (coherentSampleInputWord (W := W) α s)
  rw [(coherentSampleInputWord_cost α s).1] at hq
  rw [(coherentSampleInputWord_cost α s).2] at hg
  exact ⟨hq, hg⟩

omit [Fintype J] [Fintype W] [Fintype I] [DecidableEq I] in

/-- The padded first-order input word uses exactly two queries and eight gates. -/
theorem paddedFirstOrderInputWord_cost (α Λ : ℝ) (s : J → ℝ) :
    adjointQueryCount (paddedFirstOrderInputWord (W := W) α Λ s) = 2 ∧
    adjointGateCount (paddedFirstOrderInputWord (W := W) α Λ s) = 8 := by
  obtain ⟨hq, hg⟩ := coherentPaddingWord_cost
    (fun j => α * Real.sqrt (1 + (s j) ^ 2) / Λ) (coherentFirstOrderInputWord (W := W) α s)
  rw [(coherentFirstOrderInputWord_cost α s).1] at hq
  rw [(coherentFirstOrderInputWord_cost α s).2] at hg
  exact ⟨hq, hg⟩

/-- Positive normalizations and the pointwise sample bound make the padded sample input word
well formed. -/
theorem paddedSampleInputWord_wellFormed (α Λ : ℝ) (s : J → ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j) ^ 2) ≤ Λ) :
    WellFormedAdjointCircuit (paddedSampleInputWord (W := W) α Λ s) := by
  apply coherentPaddingWord_wellFormed _ _ (coherentSampleInputWord_wellFormed α s hα)
  intro j
  exact ⟨div_nonneg (mul_nonneg hα.le (Real.sqrt_nonneg _)) hΛ.le,
    (div_le_one hΛ).2 (hbound j)⟩

/-- Positive normalizations and the pointwise sample bound make the padded first-order input
word well formed. -/
theorem paddedFirstOrderInputWord_wellFormed (α Λ : ℝ) (s : J → ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j) ^ 2) ≤ Λ) :
    WellFormedAdjointCircuit (paddedFirstOrderInputWord (W := W) α Λ s) := by
  apply coherentPaddingWord_wellFormed _ _ (coherentFirstOrderInputWord_wellFormed α s hα)
  intro j
  exact ⟨div_nonneg (mul_nonneg hα.le (Real.sqrt_nonneg _)) hΛ.le,
    (div_le_one hΛ).2 (hbound j)⟩

/-- An original block encoding of `L + iH` yields well-formed selected encodings of `L + sH`
with normalization `Λ`, error `ε * sqrt (1 + s²)`, two queries, and eight gates
[WangEtAl2026]. -/
theorem original_oracle_common_sample (L H : Matrix I I ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian) (U : Matrix W W ℂ)
    (R : Matrix W I ℂ) (α Λ ε : ℝ) (s : J → ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α ε)
    (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j) ^ 2) ≤ Λ) :
    WellFormedAdjointCircuit (paddedSampleInputWord (W := W) α Λ s) ∧
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) (controlOracle U)))
        (paddedSampleInputWord α Λ s) =
      select (fun j => paddedSampleInputUnitary U α Λ (s j)) ∧
    (∀ j, BlockEncoding (L + (s j : ℂ) • H) (paddedSampleInputUnitary U α Λ (s j))
      (tagFrame false (tagFrame false R)) (tagFrame false (tagFrame false R))
      Λ (ε * Real.sqrt (1 + (s j) ^ 2))) ∧
    adjointQueryCount (paddedSampleInputWord (W := W) α Λ s) = 2 ∧
    adjointGateCount (paddedSampleInputWord (W := W) α Λ s) = 8 := by
  refine ⟨paddedSampleInputWord_wellFormed α Λ s henc.normalization_pos hΛ hbound,
    paddedSampleInputWord_evaluate α Λ s U, ?_, paddedSampleInputWord_cost α Λ s⟩
  intro j
  exact commonNormalization_blockEncoding _ _ _ _ Λ _
    (original_oracle_sample_blockEncoding L H hL hH U R α ε (s j) henc) (hbound j)

/-- An original block encoding of `L + iH` yields well-formed selected encodings of `H + sL`
with normalization `Λ`, error `ε * sqrt (1 + s²)`, two queries, and eight gates
[WangEtAl2026]. -/
theorem original_oracle_common_first_order (L H : Matrix I I ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian) (U : Matrix W W ℂ)
    (R : Matrix W I ℂ) (α Λ ε : ℝ) (s : J → ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α ε)
    (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j) ^ 2) ≤ Λ) :
    WellFormedAdjointCircuit (paddedFirstOrderInputWord (W := W) α Λ s) ∧
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) (controlOracle U)))
        (paddedFirstOrderInputWord α Λ s) =
      select (fun j => paddedFirstOrderInputUnitary U α Λ (s j)) ∧
    (∀ j, BlockEncoding (H + (s j : ℂ) • L) (paddedFirstOrderInputUnitary U α Λ (s j))
      (tagFrame false (tagFrame false R)) (tagFrame false (tagFrame false R))
      Λ (ε * Real.sqrt (1 + (s j) ^ 2))) ∧
    adjointQueryCount (paddedFirstOrderInputWord (W := W) α Λ s) = 2 ∧
    adjointGateCount (paddedFirstOrderInputWord (W := W) α Λ s) = 8 := by
  refine ⟨paddedFirstOrderInputWord_wellFormed α Λ s henc.normalization_pos hΛ hbound,
    paddedFirstOrderInputWord_evaluate α Λ s U, ?_, paddedFirstOrderInputWord_cost α Λ s⟩
  intro j
  exact commonNormalization_blockEncoding _ _ _ _ Λ _
    (original_oracle_first_order_blockEncoding L H hL hH U R α ε (s j) henc) (hbound j)

end Samples
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
