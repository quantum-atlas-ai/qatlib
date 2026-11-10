/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetwork
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Qatlib
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

structure RecordConditionedFamily (D s : ℕ) where

  kraus : Fin s → Operator D

  correct : Fin s → Operator D

def RecordConditionedFamily.complete {D s : ℕ} (K : RecordConditionedFamily D s) : Prop :=
  ∑ k, (K.kraus k)ᴴ * (K.kraus k) = 1

def RecordConditionedFamily.correct_unitary {D s : ℕ}
    (K : RecordConditionedFamily D s) : Prop :=
  ∀ k, K.correct k ∈ Matrix.unitaryGroup (Fin D) ℂ

theorem RecordConditionedFamily.instrument_total {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (A : Operator D) :
    Matrix.trace (∑ k, conjBranch (K.kraus k) A) = Matrix.trace A := by
  have hstep : ∀ k : Fin s,
      Matrix.trace (conjBranch (K.kraus k) A)
        = Matrix.trace ((K.kraus k)ᴴ * (K.kraus k) * A) := by
    intro k
    rw [conjBranch_apply]
    have h2 : ((K.kraus k) * A * (K.kraus k)ᴴ).trace
        = ((K.kraus k)ᴴ * ((K.kraus k) * A)).trace :=
      Matrix.trace_mul_comm (R := ℂ) ((K.kraus k) * A) (K.kraus k)ᴴ
    rw [h2, ← Matrix.mul_assoc]
  rw [Matrix.trace_sum]
  calc ∑ k, Matrix.trace (conjBranch (K.kraus k) A)
      = ∑ k, Matrix.trace ((K.kraus k)ᴴ * (K.kraus k) * A) := by
        refine Finset.sum_congr rfl (fun k _ => hstep k)
    _ = ∑ k, Matrix.trace (A * ((K.kraus k)ᴴ * (K.kraus k))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact Matrix.trace_mul_comm (R := ℂ) ((K.kraus k)ᴴ * (K.kraus k)) A
    _ = Matrix.trace ((∑ k, (K.kraus k)ᴴ * (K.kraus k)) * A) := by
        calc ∑ k, Matrix.trace (A * ((K.kraus k)ᴴ * (K.kraus k)))
            = Matrix.trace (∑ k, A * ((K.kraus k)ᴴ * (K.kraus k))) := by
              rw [Matrix.trace_sum]
            _ = Matrix.trace (A * (∑ k, (K.kraus k)ᴴ * (K.kraus k))) := by
              rw [Finset.mul_sum]
            _ = Matrix.trace (((∑ k, (K.kraus k)ᴴ * (K.kraus k)) * A)) := by
              exact Matrix.trace_mul_comm (R := ℂ) A (∑ k, (K.kraus k)ᴴ * (K.kraus k))
    _ = Matrix.trace A := by rw [hK, Matrix.one_mul]

noncomputable def RecordConditionedFamily.instrument {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) : Instrument (Fin s) D D :=
  Instrument.ofBranches (fun k => conjBranch (K.kraus k))
    (fun k => completelyPositive_conjBranch (K.kraus k))
    (fun A => K.instrument_total hK A)

noncomputable def RecordConditionedFamily.corrected {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary) :
    Instrument (Fin s) D D :=
  conditionalUnitaryInstrument (K.instrument hK) K.correct hU

noncomputable def RecordConditionedFamily.localBranch {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : Operator D) (k : Fin s) : Operator D :=
  (K.corrected hK hU).branch k ρ

noncomputable def RecordConditionedFamily.branch {D R s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : LocalJoint D R) (k : Fin s) : LocalJoint D R :=
  tensorLeft ((K.corrected hK hU).branch k) ρ

noncomputable def RecordConditionedFamily.forget {D R s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : LocalJoint D R) : LocalJoint D R :=
  ∑ k, K.branch hK hU ρ k

theorem RecordConditionedFamily.corrected_branch {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : Operator D) (k : Fin s) :
    (K.corrected hK hU).branch k ρ
      = (K.correct k) * ((K.kraus k) * ρ * (K.kraus k)ᴴ) * (K.correct k)ᴴ := by
  rw [RecordConditionedFamily.corrected, conditionalUnitaryInstrument_branch]
  simp only [RecordConditionedFamily.instrument, Instrument.ofBranches, conjBranch_apply]

theorem RecordConditionedFamily.localBranch_eq {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : Operator D) (k : Fin s) :
    K.localBranch hK hU ρ k
      = ((K.correct k) * (K.kraus k)) * ρ * ((K.correct k) * (K.kraus k))ᴴ := by
  rw [RecordConditionedFamily.localBranch, RecordConditionedFamily.corrected_branch]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem RecordConditionedFamily.corrected_is_general {D R s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : LocalJoint D R) (k : Fin s) :
    K.branch hK hU ρ k = tensorLeft ((K.corrected hK hU).branch k) ρ :=
  rfl

structure CorrectedNetworkLedger (records pairs : ℕ) where

  slot : Fin records → Fin pairs

  slot_injective : Function.Injective slot

  factoryGates : ℕ

  correctionGates : ℕ

def CorrectedNetworkLedger.price {records pairs : ℕ}
    (L : CorrectedNetworkLedger records pairs) : ℕ :=
  L.factoryGates + L.correctionGates

def canonicalLedger (records pairs : ℕ) (h : records ≤ pairs) :
    CorrectedNetworkLedger records pairs where
  slot := fun i => ⟨i.val, by omega⟩
  slot_injective := by
    intro a b hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  factoryGates := 2 * pairs
  correctionGates := records

def teleportTypeCode (n k : ℕ) : Fin n × Fin n → List Bool :=
  quditMessage n k

def codeExtension {M : Type} (w : M → List Bool) (C : ℕ) (m : M) : Fin C → Bool :=
  fun i => (w m).getD i.val false

structure PrefixFreeCode (M : Type) (C : ℕ) where

  word : M → List Bool

  word_le : ∀ m, (word m).length ≤ C

  prefix_free : PrefixFree word

def redundantFixedWidth (r w : ℕ) (m : Fin (2 ^ w)) : List Bool :=
  quditEncode (r * w) m.val

end Qatlib.Concepts.FiniteLocc.LOCCProgram
