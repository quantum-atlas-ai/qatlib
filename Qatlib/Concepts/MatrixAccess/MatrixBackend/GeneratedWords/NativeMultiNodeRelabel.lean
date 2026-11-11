/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeNeumann
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Fixed reindexing of the actual multi-node Neumann word.  This is a
representation change, not a synthesis of wire swaps or a proof that the
whole word is the SELECT of the single-node words. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix


variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for multinode Relabel Inner Dec Eq in the native multi node relabel model. -/
local instance multinodeRelabelInnerDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _
/-- Typeclass instance for multinode Relabel Outer Dec Eq in the native multi node relabel model. -/
local instance multinodeRelabelOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- Move the node register in front of the entire Neumann workspace. -/
def nativeMultiNodeLabelEquiv (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H))) ≃
      J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H)) where
  toFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  invFun y := (y.2.1, (y.2.2.1, (y.1, y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The relabeled actual word; queries remain queries, with all known gates
carried by the same fixed wire reindexing. -/
def nativeMultiNodeRelabeledWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    List (AdjointStep (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H)))) :=
  phaseLiftWord (relabelGate (nativeMultiNodeLabelEquiv (J := J) (H := H) b))
    (nativeMultiNodeNeumannWord b hb F ps p slack)

omit [DecidableEq I] in
/-- Reindexing preserves the known-macro and original-query ledger. -/
theorem nativeMultiNodeRelabeledWord_cost (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (U : Matrix H H ℂ) :
    adjointQueryCount (nativeMultiNodeRelabeledWord b hb F ps p slack) = 2*b-1 ∧
    adjointGateCount (nativeMultiNodeRelabeledWord b hb F ps p slack) = 2*b+(2*b-1)*3 := by
  have h := nativeMultiNodeNeumann_evaluate_cost b hb F ps p slack U
  have hc := phaseLiftWord_counts (relabelGate (nativeMultiNodeLabelEquiv (J := J) (H := H) b))
    (nativeMultiNodeNeumannWord b hb F ps p slack)
  exact ⟨hc.1.trans h.2.1, hc.2.trans h.2.2⟩

omit [Fintype J] [Fintype H] [DecidableEq H] in
/-- The common charged oracle stays the same oracle on every node after the
fixed reindexing. -/
theorem nativeMultiNodeRelabeledOracle (b : ℕ) (U : Matrix (Reg 6 × H) (Reg 6 × H) ℂ) :
    relabelGate (nativeMultiNodeLabelEquiv (J := J) (H := H) b)
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) U)) =
      parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U) := by
  classical
  ext ⟨j,f,k,h⟩ ⟨l,g,m,i⟩
  simp [relabelGate, nativeMultiNodeLabelEquiv, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, parallelOracle, select, TensorGate, Matrix.one_apply,
    ite_mul, mul_ite]
  split_ifs <;> simp_all

omit [DecidableEq I] in
/-- Actual evaluated matrices are carried by the same fixed reindexing.  This
does not by itself prove that the result is a SELECT of whole node words. -/
theorem nativeMultiNodeRelabeledWord_evaluate (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (U : Matrix H H ℂ) :
    evaluate (parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)))
      (nativeMultiNodeRelabeledWord b hb F ps p slack) =
      relabelGate (nativeMultiNodeLabelEquiv (J := J) (H := H) b)
        (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U)))
          (nativeMultiNodeNeumannWord b hb F ps p slack)) := by
  classical
  let e := nativeMultiNodeLabelEquiv (J := J) (H := H) b
  have h1 : relabelGate e 1 = 1 := Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one e
  have hm : ∀ U V, relabelGate e (U*V) = relabelGate e U * relabelGate e V :=
    fun U V => Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul e U V
  have ha : ∀ U, relabelGate e Uᴴ = (relabelGate e U)ᴴ := by
    intro U
    simp only [relabelGate, Matrix.conjTranspose_reindex]
  have h := phaseLiftWord_evaluate (relabelGate e) h1 hm ha
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U)))
    (nativeMultiNodeNeumannWord b hb F ps p slack)
  simpa only [nativeMultiNodeRelabeledWord, e, nativeMultiNodeRelabeledOracle] using h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
