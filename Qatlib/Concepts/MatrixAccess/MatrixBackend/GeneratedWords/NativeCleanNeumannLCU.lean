/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanActualNeumann
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.CleanWordLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanBlockLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Oracle-unitarity bridge and an unverified weighted-endpoint draft.
The endpoint remains commented: specialization exceeds the heartbeat limit. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for clean LCUBranch Dec Eq in the native clean neumann lcu model. -/
local instance cleanLCUBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for clean LCUOuter Dec Eq in the native clean neumann lcu model. -/
local instance cleanLCUOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for clean LCUInner Dec Eq in the native clean neumann lcu model. -/
local instance cleanLCUInnerDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _

/-- The actual finite word or frame satisfies `unitaryDecEqTransport` with all displayed legality, input and workspace hypotheses. -/
private theorem unitaryDecEqTransport {D : Type} [Fintype D]
    (d₁ d₂ : DecidableEq D) (V : Matrix D D ℂ) :
    V ∈ @Matrix.unitaryGroup D d₁ _ ℂ _ _ →
      V ∈ @Matrix.unitaryGroup D d₂ _ ℂ _ _ := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  exact id

/-- The actual finite word or frame satisfies `genericLabelNeumannOracle_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem genericLabelNeumannOracle_unitary {T : Type} [Fintype T] [DecidableEq T]
    (b : ℕ) (V : Matrix T T ℂ) (hV : V ∈ unitaryGroup T ℂ) :
    parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b V) ∈
      unitaryGroup (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × T)) ℂ := by
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  intro j
  apply tensorGate_unitary (unitaryGroup _ ℂ).one_mem
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  intro k
  exact hV

/-- The same original controlled oracle, lifted to the flag and label spaces,
is unitary whenever the original block-encoding oracle is unitary. -/
theorem nativeCleanNeumannOracle_unitary (b : ℕ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)) ∈
      unitaryGroup (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) ℂ := by
  let D := J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))
  have hu := genericLabelNeumannOracle_unitary (J := J) b (nativeDataQuery U)
    (nativeDataQuery_unitary U hU)
  exact unitaryDecEqTransport _ (inferInstance : DecidableEq D) _ hu

/- UNVERIFIED DRAFT: the following endpoint still times out at whnf.

/-- The actual original-query word, surrounded by ideal weight macros, encodes
the weighted sum of its per-node Neumann polynomials. No global whole-word
SELECT is assumed; query and known macro counts refer to this same word. -/
theorem nativeCleanNeumannLCU_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    let L := uniformNeumannFrame b hb (nativeDataFrame F)
    let O := parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U))
    let R := nativeMultiNodeRelabeledWord b hb F ps p slack
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) •
        (((b : ℂ)⁻¹) • leftDefectNeumann
          (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
            (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b))
      (evaluate O (weightedLCUSlotWord d j₀ R)) (tagFrame j₀ L) (tagFrame j₀ L) ∧
    O ∈ unitaryGroup _ ℂ ∧
    adjointQueryCount (weightedLCUSlotWord d j₀ R) = 2*b-1 ∧
    adjointGateCount (weightedLCUSlotWord d j₀ R) = 2*b+(2*b-1)*3+3 := by
  dsimp only
  let T := NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))
  let L : Matrix T I ℂ := uniformNeumannFrame b hb (nativeDataFrame F)
  let O : Matrix (J × T) (J × T) ℂ :=
    parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U))
  let R : List (AdjointStep (J × T)) := nativeMultiNodeRelabeledWord b hb F ps p slack
  let Y : J → Matrix I I ℂ := fun j => ((b : ℂ)⁻¹) • leftDefectNeumann
    (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
      (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b
  have hL : IsIsometry L := by
    change IsIsometry (freshNeumannFrame (b-1)
      (encodingFiber (I := Reg 6 × H) (⟨0,hb⟩ : Fin b) * nativeDataFrame F))
    unfold freshNeumannFrame
    exact IsIsometry.mul (encodingFiber_isIsometry _)
      (IsIsometry.mul (encodingFiber_isIsometry _) (nativeDataFrame_isometry F hbe.left_isometry))
  have hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ L) (evaluate O R)
      ((1 : Matrix J J ℂ) ⊗ₖ L) = select Y :=
    nativeMultiNodeRelabeled_clean_block b hb F A U α hbe ps p slack
  have hraw := (nativeMultiNodeNeumann_per_label b hb F A U α hbe ps p slack).1.unitary
  have hR : evaluate O R ∈ unitaryGroup (J × T) ℂ := by
    change evaluate _ (nativeMultiNodeRelabeledWord b hb F ps p slack) ∈ _
    rw [nativeMultiNodeRelabeledWord_evaluate]
    exact relabelGate_mem_unitary hraw _
  have hc := clean_word_lcu_encoding_cost L O R Y d j₀ hmass hL hR hblock
  have hcost := nativeMultiNodeRelabeledWord_cost b hb F ps p slack U
  refine ⟨?_, nativeCleanNeumannOracle_unitary b U hbe.unitary, ?_, ?_⟩
  · exact hc.1
  · exact hc.2.1.trans hcost.1
  · exact hc.2.2.1.trans (by rw [hcost.2])
-/

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
