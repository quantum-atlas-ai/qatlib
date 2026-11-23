/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssRecovery.ParityCircuit
public import Qatlib.Concepts.CodingDecoding.CssRecovery.CodingDecoding
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-! # Executed parity check and one propagated gate fault -/

namespace QatlibTests.ParityCircuit

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CodingDecoding.CssRecovery
open scoped Matrix

/-- Two explicit CNOTs compute the equality check of a two-qubit repetition code. -/
def word : List (ParityGate 2 1) := [⟨0, 0⟩, ⟨1, 0⟩]

/-- The actual circuit defines the Z check matrix of the example. -/
def code : CssData (Fin 2) (Fin 0) (Fin 1) where
  hX := 0
  hZ := circuitCheck word
  hcompat := by funext i; exact Fin.elim0 i

/-- The first location of this particular two-gate word. -/
def firstGate : Fin word.length := ⟨0, by decide +kernel⟩

/-- The prescribed fault at the first gate flips the second data qubit. -/
def flips (i : Fin word.length) : Joint 2 1 :=
  if i = firstGate then (fun j => if j = 1 then 1 else 0, 0) else 0

/-- The second CNOT propagates the fault into the ancillary syndrome. -/
theorem propagated :
    faultRun word (faultsAt word flips {firstGate}) 0 = (fun j => if j = 1 then 1 else 0, 1) := by
  decide +kernel

/-- Preparing and measuring the actual circuit gives the same branch as projecting onto the
syndrome of its Z-check matrix. -/
theorem ideal_branch (η : Bits 1) :
    readAfter (parityOp word) η =
      Matrix.diagonal (fun x : Bits 2 => if code.hZ *ᵥ x = η then (1 : ℂ) else 0) :=
  parity_branch word η

/-- The branch of the actual circuit instrument consumes the checked Kraus operator. -/
theorem ideal_instrument (η : Bits 1) (ρ : Operator (Fintype.card (Bits 2))) :
    (parityInstr word).branch η ρ = parityKraus word η * ρ * (parityKraus word η)ᴴ :=
  parity_outcome word η ρ

/-- With zero input and a fault after the first CNOT, the sole surviving ancilla outcome is
one and the surviving data label has its second bit flipped. -/
theorem noisy_outcome :
    readAfter (faultyOp word (faultsAt word flips {firstGate})) (1 : Bits 1)
      (fun j => if j = 1 then 1 else 0) 0 = 1 := by
  rw [faulty_branch, propagated]
  simp

/-- The actual propagated residual of every single-location fault has weight at most one. -/
theorem gadget_tolerant : (parityGadget code word flips).IsFaultTolerantAt 1 := by
  apply gadget_bound
  decide +kernel

/-- The example decoder flips the second data bit when the CNOT readout reports odd parity. -/
def decoder : RecoveryProgram code where
  corr η := (fun j => if j = 1 then η.2 0 else 0, 0)
  decodeTime := fun _ => 1

/-- The observed syndrome repairs the actual propagated first-location fault. -/
theorem noisy_decoded :
    residualFromObserved decoder ((faultRun word (faultsAt word flips {firstGate}) 0).1, 0)
      (0, (faultRun word (faultsAt word flips {firstGate}) 0).2) = 0 := by
  rw [propagated]
  decide +kernel

/-! ## The seven-qubit Steane code

`steaneData` is the `[[7, 1, 3]]` CSS code: both check matrices are the Hamming
parity-check matrix, one qubit is encoded, and both the X-logical and Z-logical
distances are exactly three. The distance is the infimum of a nonempty set of
logical weights, not the empty-set value `⊤`. -/

/-- A weight-three Steane vector supported on qubits `0`, `1`, and `3`. -/
def steaneLogical : Fin 7 → ZMod 2 :=
  fun i => if i = 0 ∨ i = 1 ∨ i = 3 then 1 else 0

/-- The exhibited Steane vector has Hamming weight three. -/
theorem steaneLogical_weight : bitWeight steaneLogical = 3 := by
  decide +kernel

/-- Columns `0`, `1`, and `3` of the Steane matrix sum to zero. -/
theorem steaneLogical_kernel : steaneH *ᵥ steaneLogical = 0 := by
  decide +kernel

/-- The weight-three vector is outside the eight-element row space. -/
theorem steaneLogical_not_row (c : Fin 3 → ZMod 2) : steaneHᵀ *ᵥ c ≠ steaneLogical := by
  revert c
  decide +kernel

/-- The weight-three vector is not a stabilizer row. -/
theorem steaneLogical_not_stabilizer :
    steaneLogical ∉ LinearMap.range (Matrix.mulVecLin steaneHᵀ) := by
  intro ⟨c, hc⟩
  apply steaneLogical_not_row c
  simpa [Matrix.mulVec_transpose] using hc

/-- No Steane codeword of weight at most two exists except zero. -/
theorem steane_low_kernel :
    ∀ z : Fin 7 → ZMod 2, steaneH *ᵥ z = 0 → bitWeight z ≤ 2 → z = 0 := by
  decide +kernel

/-- Weights of nontrivial Steane logical vectors. Both X and Z checks use `steaneH`. -/
def steaneLogicalWeights : Set ℕ∞ :=
  {w : ℕ∞ | ∃ z : Fin 7 → ZMod 2, steaneH *ᵥ z = 0 ∧
    z ∉ LinearMap.range (Matrix.mulVecLin steaneHᵀ) ∧ (bitWeight z : ℕ∞) = w}

/-- The logical-weight infimum equals three because a weight-three logical exists and no
lighter nonzero kernel vector does. -/
theorem steaneLogicalWeights_sInf : sInf steaneLogicalWeights = 3 := by
  classical
  apply le_antisymm
  · apply sInf_le
    refine ⟨steaneLogical, steaneLogical_kernel, steaneLogical_not_stabilizer, ?_⟩
    exact_mod_cast steaneLogical_weight
  · apply le_sInf
    rintro w ⟨z, hker, hout, rfl⟩
    have hge : 3 ≤ bitWeight z := by
      by_contra hlt
      have hw : bitWeight z ≤ 2 := Nat.lt_succ_iff.mp (lt_of_not_ge hlt)
      have hz0 : z = 0 := steane_low_kernel z hker hw
      apply hout
      subst hz0
      refine ⟨0, ?_⟩
      simp
    exact_mod_cast hge

/-- The Steane code encodes one qubit. -/
theorem steane_encoded_pos : 0 < steaneData.encodedQubits := by
  rw [steaneData_encodedQubits]
  decide

/-- Z-logical distance of the Steane code is three. -/
theorem steane_zLogicalDistance :
    sInf {w : ℕ∞ | ∃ z : Fin 7 → ZMod 2, steaneData.hX *ᵥ z = 0 ∧
      z ∉ LinearMap.range (Matrix.mulVecLin steaneData.hZᵀ) ∧
      (bitWeight z : ℕ∞) = w} = 3 := by
  rw [show steaneData.hX = steaneH from rfl, show steaneData.hZ = steaneH from rfl]
  exact steaneLogicalWeights_sInf

/-- X-logical distance of the Steane code is three. -/
theorem steane_xLogicalDistance :
    sInf {w : ℕ∞ | ∃ x : Fin 7 → ZMod 2, steaneData.hZ *ᵥ x = 0 ∧
      x ∉ LinearMap.range (Matrix.mulVecLin steaneData.hXᵀ) ∧
      (bitWeight x : ℕ∞) = w} = 3 := by
  rw [show steaneData.hX = steaneH from rfl, show steaneData.hZ = steaneH from rfl]
  exact steaneLogicalWeights_sInf

/-- The CSS distance is the minimum of the two logical distances, hence exactly three. -/
theorem steane_cssDistance : cssDistance steaneData = 3 := by
  unfold cssDistance
  rw [steane_zLogicalDistance, steane_xLogicalDistance]
  exact min_self _

/-- Twelve CNOTs realize the Steane check matrix. Qubit `0` is read only by the last gate. -/
def steaneWord : List (ParityGate 7 3) :=
  [⟨3, 0⟩, ⟨4, 0⟩, ⟨6, 0⟩,
   ⟨1, 1⟩, ⟨3, 1⟩, ⟨5, 1⟩, ⟨6, 1⟩,
   ⟨2, 2⟩, ⟨4, 2⟩, ⟨5, 2⟩, ⟨6, 2⟩,
   ⟨0, 0⟩]

/-- The executed CNOT word is the Steane Z-check matrix. -/
theorem steaneWord_check : circuitCheck steaneWord = steaneData.hZ := by
  decide +kernel

/-- The first gate, after which the data fault is inserted. -/
def steaneFaultGate : Fin steaneWord.length := ⟨0, by decide +kernel⟩

/-- The fault after the first gate flips data qubit `0` and no ancilla. -/
def steaneFlips (i : Fin steaneWord.length) : Joint 7 3 :=
  if i = steaneFaultGate then (fun j => if j = 0 then 1 else 0, 0) else 0

/-- The later CNOT on qubit `0` copies that fault into ancilla `0`. -/
theorem steanePropagated :
    faultRun steaneWord (faultsAt steaneWord steaneFlips {steaneFaultGate}) 0 =
      (fun j => if j = 0 then 1 else 0, fun a => if a = 0 then 1 else 0) := by
  decide +kernel

/-- `fault_decode` turns the propagated Steane fault into a stabilizer residual. -/
theorem steaneFaultDecode :
    IsStabilizerLabel steaneData
      (residualFromObserved steaneDecoder
        ((faultRun steaneWord (faultsAt steaneWord steaneFlips {steaneFaultGate}) 0).1, 0)
        (0, (faultRun steaneWord (faultsAt steaneWord steaneFlips {steaneFaultGate}) 0).2)) := by
  apply fault_decode steaneData steaneWord steaneWord_check steaneFlips
    (by
      intro i
      fin_cases i <;> decide +kernel)
    {steaneFaultGate} (by decide +kernel)
    steaneDecoder steaneDecoder_singleShot
  rw [steanePropagated]
  decide +kernel

end QatlibTests.ParityCircuit
