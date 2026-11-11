/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.NoSignalCode.QuantumMessageCount
import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement

/-!
# Message counting for local instrument codes

Local unitary encoding on one subsystem preserves the other subsystem's marginal. With a
complete local Kraus family, the resulting conditional operators therefore have a common sum
independent of the encoded symbol.

`local_instrument_exact_code_card_le` uses this property to bound the number of exactly decoded
symbols by the number of classical instrument outcomes. This supplies a local instrument form of
the communication obstruction discussed in [BennettEtAl1993Teleportation].

## Main statements

* `local_unitary_preserves_marginal` proves marginal invariance under a unitary on the traced
  subsystem.
* `local_instrument_exact_code_card_le` bounds exact code cardinality by the number of
  instrument messages.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.NoSignalCode
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.FiniteLocc.LOCCProgram

/-- Conjugating a joint operator by a unitary on the second subsystem leaves its partial trace
over that subsystem unchanged. -/
theorem local_unitary_preserves_marginal {D E : ℕ}
    (U : Operator E) (hU : U ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (TensorGate (1 : Operator D) U * ρ *
      (TensorGate (1 : Operator D) U)ᴴ) = PartialTrace ρ := by
  have hc : ∑ _i : Fin 1, Uᴴ * U = (1 : Operator E) := by
    simpa only [Fin.sum_univ_one] using!
      (Matrix.mem_unitaryGroup_iff'.mp hU : Uᴴ * U = 1)
  simpa only [Fin.sum_univ_one] using!
    partialTrace_right_instrument (fun _i : Fin 1 => U) hc ρ

/-- With a positive shared operator of normalized marginal, local unitary encoding, a complete
`k` outcome Kraus family, and exact conditional POVM decoding, the source alphabet has at
most `k` elements [BennettEtAl1993Teleportation]. -/
theorem local_instrument_exact_code_card_le
    {X : Type} [Fintype X] [DecidableEq X] {D E k : ℕ} (x₀ : X)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace (PartialTrace ρ) = 1)
    (U : X → Operator E) (hU : ∀ x, U x ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (K : Fin k → Operator E) (hK : ∑ m, (K m)ᴴ * K m = 1)
    (F : Fin k → FinitePOVM X D)
    (hdecode : ∀ x,
      ∑ m, (Matrix.trace ((F m).effect x *
        PartialTrace (TensorGate (1 : Operator D) (K m * U x) * ρ *
          (TensorGate (1 : Operator D) (K m * U x))ᴴ))).re = 1) :
    Fintype.card X ≤ k := by
  let τ := fun x m => PartialTrace
    (TensorGate (1 : Operator D) (K m * U x) * ρ *
      (TensorGate (1 : Operator D) (K m * U x))ᴴ)
  have hpos : ∀ x m, (τ x m).PosSemidef := by
    intro x m
    apply partialTrace_posSemidef
    exact hρ.mul_mul_conjTranspose_same _
  have hcommon : ∀ x, ∑ m, τ x m = PartialTrace ρ := by
    intro x
    have hKU : ∑ m, (K m * U x)ᴴ * (K m * U x) = 1 := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_sum]
      have hinner : (∑ m, (K m)ᴴ * (K m * U x)) = U x := by
        simp_rw [← Matrix.mul_assoc]
        rw [← Matrix.sum_mul, hK, Matrix.one_mul]
      rw [hinner]
      exact Matrix.mem_unitaryGroup_iff'.mp (hU x)
    change (∑ m, PartialTrace _) = _
    rw [← partialTrace_sum]
    exact partialTrace_right_instrument (fun m => K m * U x) hKU ρ
  simpa using! quantum_assemblage_message_count x₀ τ (PartialTrace ρ) F hpos hcommon htrace hdecode

end Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
