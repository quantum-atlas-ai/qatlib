/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanEndpoint
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeWeightedResolventConsumer
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.CleanWordLCU
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.NativeWeightedLCUSlot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Native Endpoint Diagnosis

The same emitted instruction list satisfies `diagnosis_weight_counts` with the displayed gate and query accounting.
-/
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {J T I : Type} [Fintype J] [DecidableEq J]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

/-- The finite construction in `NativeEndpointDiagnosis` satisfies `abstract_classical_pue` under the displayed hypotheses. -/
theorem abstract_classical_pue
    [outer : DecidableEq (J × T)]
    (L : Matrix T I ℂ) (O : Matrix (J × T) (J × T) ℂ)
    (W : List (AdjointStep (J × T))) (Y : J → Matrix I I ℂ)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d)
    (hL : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L) (hW : evaluate O W ∈ unitaryGroup (J × T) ℂ)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ L) (evaluate O W)
      ((1 : Matrix J J ℂ) ⊗ₖ L) = select Y) :
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) • Y j)
      (evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W))
      (tagFrame j₀ L) (tagFrame j₀ L) := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  exact (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.clean_word_lcu_encoding_cost L O W Y d j₀ hmass hL hW hblock).1

variable {H : Type} [Fintype H] [DecidableEq H]

/-- Typeclass instance for diagnosis Outer Dec Eq in the native endpoint diagnosis model. -/
local instance diagnosisOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- The finite construction in `NativeEndpointDiagnosis` satisfies `diagnosis_endpoint_pue` under the displayed hypotheses. -/
theorem diagnosis_endpoint_pue (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) • cleanEndpointBlock b A α ps p slack j)
      (evaluate (cleanEndpointOracle (J := J) b U)
        (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ (cleanEndpointBody b hb F ps p slack)))
      (tagFrame j₀ (cleanEndpointFrame b hb F)) (tagFrame j₀ (cleanEndpointFrame b hb F)) := by
  exact abstract_classical_pue (cleanEndpointFrame b hb F)
    (cleanEndpointOracle (J := J) b U) (cleanEndpointBody b hb F ps p slack)
    (cleanEndpointBlock b A α ps p slack) d j₀ hmass
    (endpoint_frame_isometry b hb F hbe.left_isometry)
    (endpoint_word_unitary b hb F A U α hbe ps p slack)
    (endpoint_block b hb F A U α hbe ps p slack)

/- UNVERIFIED: this combined consumer did not finish local checking within
the bounded attempt. It uses the product instance for the inner index, as
the resolvent consumer does; the cost helper was private in its source module.
/-- The same emitted instruction list satisfies `diagnosis_weight_counts` with the displayed gate and query accounting. -/
private theorem diagnosis_weight_counts {T : Type} [Fintype T] [DecidableEq T]
    (d : J → ℂ) (j₀ : J) (W : List (AdjointStep (J × T))) :
    adjointQueryCount (weightedLCUSlotWord d j₀ W) = adjointQueryCount W ∧
    adjointGateCount (weightedLCUSlotWord d j₀ W) = adjointGateCount W + 3 := by
  let body := weightedLCUSlotBody d W
  let cs := scaledLCUAdjointWord (H := T) d j₀
  have h := substitute_adjoint_evaluate_cost (1 : Matrix (J × T) (J × T) ℂ) body cs
  constructor
  · change adjointQueryCount (substituteAdjointCircuit body cs) = _
    rw [h.2.1]
    simp [cs, scaledLCUAdjointWord, adjointQueryCount, body, weightedLCUSlotBody]
  · change adjointGateCount (substituteAdjointCircuit body cs) = _
    rw [h.2.2.1]
    simp [cs, scaledLCUAdjointWord, adjointQueryCount, adjointGateCount, body,
      weightedLCUSlotBody]
    omega

/-- The actual weighted word simultaneously supplies the resolvent error
bound and the count of original oracle queries. Known-instruction count
uses ideal matrix macros; it is not a finite-gate synthesis estimate. -/
theorem diagnosis_weighted_resolvent_cost
    (b : ℕ) (hb : 0 < b)
    (ps : J → Fin 7 → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (weights : J → ℂ) (j₀ : J)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α B : ℝ) (r K : J → ℝ) (z : J → ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : ∀ j, α + ‖z j‖ ≤ B) (hr : ∀ j, 0 < r j)
    (hsep : ∀ j w, w ∈ matrixNumericalRange A → r j ≤ ‖z j-w‖)
    (hK : ∀ j, jointResolventCondition B (r j) ≤ K j)
    (hsmall : ∀ j, nativeCoefficientError (ps j) (p j) (slack j) α B (z j) ≤
      1/(4*(K j)^2))
    (hmass : 0 < coefficientMass weights) :
    BlockEncoding (∑ j, weights j • matrixResolvent A (z j))
      (evaluate (parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U)))
        (weightedLCUSlotWord weights j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)))
      (tagFrame j₀ (uniformNeumannFrame b hb (nativeDataFrame F)))
      (tagFrame j₀ (uniformNeumannFrame b hb (nativeDataFrame F)))
      (((b : ℝ)/B) * coefficientMass weights)
      (∑ j, ‖weights j‖ *
        (((2*(K j)^2+4*(K j)^3) *
          nativeCoefficientError (ps j) (p j) (slack j) α B (z j) +
          reciprocalError (jointResolventCondition B (r j))⁻¹ b) / B)) ∧
    adjointQueryCount (weightedLCUSlotWord weights j₀
      (nativeMultiNodeRelabeledWord b hb F ps p slack)) = 2*b-1 ∧
    adjointGateCount (weightedLCUSlotWord weights j₀
      (nativeMultiNodeRelabeledWord b hb F ps p slack)) = 2*b+(2*b-1)*3+3 := by
  refine ⟨?_, ?_, ?_⟩
  · apply weighted_original_resolvent_of_clean_word b hb ps p slack weights j₀ A U F α B r K z
      hbe hB hbound hr hsep hK hsmall hmass
    exact diagnosis_endpoint_pue b hb F A U α hbe ps p slack weights j₀ hmass
  · have hc := diagnosis_weight_counts weights j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)
    have hr := nativeMultiNodeRelabeledWord_cost b hb F ps p slack U
    exact hc.1.trans hr.1
  · have hc := diagnosis_weight_counts weights j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)
    have hr := nativeMultiNodeRelabeledWord_cost b hb F ps p slack U
    exact hc.2.trans (by rw [hr.2])
-/

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
