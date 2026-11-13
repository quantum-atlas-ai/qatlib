/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetwork
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation

/-!
# Record-conditioned measurement families

`RecordConditionedFamily` packages a finite Kraus family with a correction operator for each
classical record. Completeness and unitarity hypotheses turn it into an instrument, a corrected
instrument, and branches extended to an untouched reference system, using the finite-dimensional
measurement formalism of [Watrous2018].

The module also defines `CorrectedNetworkLedger` for injective resource-slot assignments and
elementary bounded and prefix-free message-code data.

## Main statements

* `RecordConditionedFamily.instrument_total`: Kraus completeness preserves total trace.
* `RecordConditionedFamily.localBranch_eq`: a corrected branch has effective Kraus operator
  given by correction times measurement.
* `canonicalLedger`: assigns distinct resource slots when the number of records is at most the
  number of pairs.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- A finite family of measurement Kraus operators together with one correction operator for
each classical record. -/
structure RecordConditionedFamily (D s : ℕ) where

  kraus : Fin s → Operator D

  correct : Fin s → Operator D

/-- The Kraus completeness condition: the sum of `kraus k` adjoint times `kraus k` is the
identity. -/
def RecordConditionedFamily.complete {D s : ℕ} (K : RecordConditionedFamily D s) : Prop :=
  ∑ k, (K.kraus k)ᴴ * (K.kraus k) = 1

/-- The condition that every record-dependent correction operator is unitary. -/
def RecordConditionedFamily.correct_unitary {D s : ℕ}
    (K : RecordConditionedFamily D s) : Prop :=
  ∀ k, K.correct k ∈ Matrix.unitaryGroup (Fin D) ℂ

/-- Completeness of the Kraus family implies that the sum of its conjugation branches preserves
the trace of every operator. -/
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

/-- Constructs the instrument of Kraus conjugation branches from the family's completeness
proof. -/
noncomputable def RecordConditionedFamily.instrument {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) : Instrument (Fin s) D D :=
  Instrument.ofBranches (fun k => conjBranch (K.kraus k))
    (fun k => completelyPositive_conjBranch (K.kraus k))
    (fun A => K.instrument_total hK A)

/-- Constructs the instrument obtained by applying the record-dependent unitary correction after
each Kraus branch. -/
noncomputable def RecordConditionedFamily.corrected {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary) :
    Instrument (Fin s) D D :=
  conditionalUnitaryInstrument (K.instrument hK) K.correct hU

/-- Evaluates a corrected instrument branch on a local operator. -/
noncomputable def RecordConditionedFamily.localBranch {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : Operator D) (k : Fin s) : Operator D :=
  (K.corrected hK hU).branch k ρ

/-- Extends a corrected branch to a joint operator by acting on the local factor and leaving the
reference factor untouched. -/
noncomputable def RecordConditionedFamily.branch {D R s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : LocalJoint D R) (k : Fin s) : LocalJoint D R :=
  tensorLeft ((K.corrected hK hU).branch k) ρ

/-- Sums the corrected reference-extended branches over all records. -/
noncomputable def RecordConditionedFamily.forget {D R s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : LocalJoint D R) : LocalJoint D R :=
  ∑ k, K.branch hK hU ρ k

/-- Expands a corrected branch as Kraus conjugation followed by conjugation by the
record-dependent correction. -/
theorem RecordConditionedFamily.corrected_branch {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : Operator D) (k : Fin s) :
    (K.corrected hK hU).branch k ρ
      = (K.correct k) * ((K.kraus k) * ρ * (K.kraus k)ᴴ) * (K.correct k)ᴴ := by
  rw [RecordConditionedFamily.corrected, conditionalUnitaryInstrument_branch]
  simp only [RecordConditionedFamily.instrument, Instrument.ofBranches, conjBranch_apply]

/-- A local corrected branch is conjugation by the product of the correction and Kraus
operators. -/
theorem RecordConditionedFamily.localBranch_eq {D s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : Operator D) (k : Fin s) :
    K.localBranch hK hU ρ k
      = ((K.correct k) * (K.kraus k)) * ρ * ((K.correct k) * (K.kraus k))ᴴ := by
  rw [RecordConditionedFamily.localBranch, RecordConditionedFamily.corrected_branch]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The reference-extended corrected branch is `tensorLeft` applied to the corresponding
corrected instrument branch. -/
theorem RecordConditionedFamily.corrected_is_general {D R s : ℕ}
    (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
    (ρ : LocalJoint D R) (k : Fin s) :
    K.branch hK hU ρ k = tensorLeft ((K.corrected hK hU).branch k) ρ :=
  rfl

/-- An injective assignment of records to pair slots together with factory-gate and
correction-gate charges. -/
structure CorrectedNetworkLedger (records pairs : ℕ) where

  slot : Fin records → Fin pairs

  slot_injective : Function.Injective slot

  factoryGates : ℕ

  correctionGates : ℕ

/-- Adds the factory-gate and correction-gate charges in a corrected-network ledger. -/
def CorrectedNetworkLedger.price {records pairs : ℕ}
    (L : CorrectedNetworkLedger records pairs) : ℕ :=
  L.factoryGates + L.correctionGates

/-- Constructs a ledger by assigning each record to the pair slot with the same index, assuming
`records ≤ pairs`. -/
def canonicalLedger (records pairs : ℕ) (h : records ≤ pairs) :
    CorrectedNetworkLedger records pairs where
  slot := fun i => ⟨i.val, by omega⟩
  slot_injective := by
    intro a b hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  factoryGates := 2 * pairs
  correctionGates := records

/-- Encodes a pair of qudit teleportation outcomes as a Boolean message using `quditMessage`. -/
def teleportTypeCode (n k : ℕ) : Fin n × Fin n → List Bool :=
  quditMessage n k

/-- Extends a Boolean codeword to `Fin C` by reading its bits and padding missing positions with
`false`. -/
def codeExtension {M : Type} (w : M → List Bool) (C : ℕ) (m : M) : Fin C → Bool :=
  fun i => (w m).getD i.val false

/-- A code assigning each message a Boolean word of length at most `C`, with a proof that the
code is prefix-free. -/
structure PrefixFreeCode (M : Type) (C : ℕ) where

  word : M → List Bool

  word_le : ∀ m, (word m).length ≤ C

  prefix_free : PrefixFree word

/-- Encodes the natural value of a `w`-bit message at width `r * w`. -/
def redundantFixedWidth (r w : ℕ) (m : Fin (2 ^ w)) : List Bool :=
  quditEncode (r * w) m.val

end Qatlib.Concepts.FiniteLocc.LOCCProgram
