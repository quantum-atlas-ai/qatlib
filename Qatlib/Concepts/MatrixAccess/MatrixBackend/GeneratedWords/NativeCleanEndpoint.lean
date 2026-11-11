/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanNeumannParts
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Checked frame, word and clean-block bridges, consumed by the generated
multi-node endpoint. Historical combined PUE candidates remain in comments
for diagnosis; they are not declarations or claimed proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for endpoint Branch Dec Eq in the native clean endpoint model. -/
local instance endpointBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for endpoint Outer Dec Eq in the native clean endpoint model. -/
local instance endpointOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- Construction for clean Endpoint Frame in the native clean endpoint model. -/
def cleanEndpointFrame (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ) :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)

/-- Construction for clean Endpoint Oracle in the native clean endpoint model. -/
def cleanEndpointOracle (b : ℕ) (U : Matrix H H ℂ) :=
  parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U))

/-- Construction for clean Endpoint Body in the native clean endpoint model. -/
def cleanEndpointBody (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :=
  nativeMultiNodeRelabeledWord b hb F ps p slack

/-- Construction for clean Endpoint Block in the native clean endpoint model. -/
def cleanEndpointBlock (b : ℕ) (A : Matrix I I ℂ) (α : ℝ)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    J → Matrix I I ℂ := fun j =>
  ((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
    (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
      (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b

/- UNVERIFIED candidate retained for diagnosis.
/-- The actual shared-oracle word, weighted by ideal known macros, encodes
the weighted Neumann blocks. No whole-space SELECT assumption is needed. -/
theorem nativeCleanEndpoint_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) • cleanEndpointBlock b A α ps p slack j)
      (evaluate (cleanEndpointOracle (J := J) b U)
        (weightedLCUSlotWord d j₀ (cleanEndpointBody b hb F ps p slack)))
      (tagFrame j₀ (cleanEndpointFrame b hb F)) (tagFrame j₀ (cleanEndpointFrame b hb F)) ∧
    adjointQueryCount (weightedLCUSlotWord d j₀ (cleanEndpointBody b hb F ps p slack)) = 2*b-1 ∧
    adjointGateCount (weightedLCUSlotWord d j₀ (cleanEndpointBody b hb F ps p slack)) =
      2*b+(2*b-1)*3+3 := by
  have hf : IsIsometry (cleanEndpointFrame b hb F) := by
    exact nativeCleanSingleFrame_isometry b hb F hbe.left_isometry
  have hu : evaluate (cleanEndpointOracle (J := J) b U)
      (cleanEndpointBody b hb F ps p slack) ∈ unitaryGroup _ ℂ := by
    exact nativeCleanRelabeledWord_unitary b hb F A U α hbe ps p slack
  have hc : compress ((1 : Matrix J J ℂ) ⊗ₖ cleanEndpointFrame b hb F)
      (evaluate (cleanEndpointOracle (J := J) b U) (cleanEndpointBody b hb F ps p slack))
      ((1 : Matrix J J ℂ) ⊗ₖ cleanEndpointFrame b hb F) =
      select (cleanEndpointBlock b A α ps p slack) := by
    exact nativeMultiNodeRelabeled_clean_block b hb F A U α hbe ps p slack
  have h := clean_word_lcu_encoding_cost (cleanEndpointFrame b hb F)
    (cleanEndpointOracle (J := J) b U) (cleanEndpointBody b hb F ps p slack)
    (cleanEndpointBlock b A α ps p slack) d j₀ hmass hf hu hc
  have hcost := nativeCleanNeumannWeight_cost b hb F ps p slack d j₀ U
  exact ⟨h.1, hcost.1, hcost.2⟩
-/

/-- The actual endpoint frame remains isometric whenever its original input frame is isometric. -/
theorem endpoint_frame_isometry (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (cleanEndpointFrame b hb F) :=
  nativeCleanSingleFrame_isometry b hb F hF

/-- The actual finite word or frame satisfies `endpoint_word_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem endpoint_word_unitary (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    evaluate (cleanEndpointOracle (J := J) b U)
      (cleanEndpointBody b hb F ps p slack) ∈ unitaryGroup _ ℂ :=
  nativeCleanRelabeledWord_unitary b hb F A U α hbe ps p slack

/-- The finite construction in `NativeCleanEndpoint` satisfies `endpoint_block` under the displayed hypotheses. -/
theorem endpoint_block (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    compress ((1 : Matrix J J ℂ) ⊗ₖ cleanEndpointFrame b hb F)
      (evaluate (cleanEndpointOracle (J := J) b U) (cleanEndpointBody b hb F ps p slack))
      ((1 : Matrix J J ℂ) ⊗ₖ cleanEndpointFrame b hb F) =
      select (cleanEndpointBlock b A α ps p slack) :=
  nativeMultiNodeRelabeled_clean_block b hb F A U α hbe ps p slack

/- UNVERIFIED: concrete specialization of the generic clean-word PUE times out.
/-- The finite construction in `NativeCleanEndpoint` satisfies `nativeCleanEndpoint_pue` under the displayed hypotheses. -/
theorem nativeCleanEndpoint_pue (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) • cleanEndpointBlock b A α ps p slack j)
      (evaluate (cleanEndpointOracle (J := J) b U)
        (weightedLCUSlotWord d j₀ (cleanEndpointBody b hb F ps p slack)))
      (tagFrame j₀ (cleanEndpointFrame b hb F)) (tagFrame j₀ (cleanEndpointFrame b hb F)) := by
  exact (clean_word_lcu_encoding_cost (cleanEndpointFrame b hb F)
    (cleanEndpointOracle (J := J) b U) (cleanEndpointBody b hb F ps p slack)
    (cleanEndpointBlock b A α ps p slack) d j₀ hmass
    (endpoint_frame_isometry b hb F hbe.left_isometry)
    (endpoint_word_unitary b hb F A U α hbe ps p slack)
    (endpoint_block b hb F A U α hbe ps p slack)).1
-/

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
