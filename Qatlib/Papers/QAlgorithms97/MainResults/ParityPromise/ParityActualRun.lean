/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise
import Qatlib.Papers.QAlgorithms97.MainResults.AffineCoefficients

/-!
# The parity promise: actual run of the generalised Fig. 4 network (Sect. 3)

Paper: R. Cleve, A. Ekert, C. Macchiavello, M. Mosca, *Quantum Algorithms
Revisited*, arXiv:quant-ph/9708016 (fixed PDF `quant-ph_9708016.pdf`).
Section 3, p. 8: an `m`-qubit auxiliary register initialised in
`(|0⟩−|1⟩)^{⊗m}` lets one run of the Fig. 4 network decide the
constant-or-balanced range-parity promise.

The conditional promise analysis lives in the promoted module
`Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise`.  This module adds
the actual-execution layer: the full-output XOR word `affineWord n m` run
against the real oracle `outputOracle f` from physical registers reproduces
the parity Deutsch–Jozsa state exactly, and one real oracle invocation
decides the promise with certainty.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise

open Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise
open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
open Qatlib.Papers.QAlgorithms97.MainResults.AffineCoefficients
open Qatlib.Papers.QAlgorithms97.MainResults.OracleInterfaces

/-- Selecting every output coordinate gives precisely the parity phase of the full output string. -/
theorem all_output_character {m : ℕ} (y : Reg m) :
    (if bitParity y then (-1 : ℂ) else 1) = binaryCharacter (fun _ => true) y := by
  rw [← bit_character, binaryCharacter_dot]
  change ZMod.stdAddChar (bitVal (boolParity y)) = _
  rw [bitVal_boolParity]
  simp only [bitVal, if_true, one_mul]

/-- The actual full-output XOR word reduces to the parity DJ state, retaining all m answer qubits. -/
theorem parityPromise_actual_run {n m : ℕ} (f : Reg n → Reg m) :
    Run (outputOracle f) (affineWord n m)
      (TensorState (Ket (ZeroStr n)) (Ket (fun _ => true))) =
        TensorState (djFinalState (parityFun f)) (outputAnswer (fun _ => true)) := by
  have hzero : djAfterH n = Uniform (Reg n) := by
    rw [← dj_afterH_apply, applyGate_hadamardN_ket_zero]
  have hp : (fun x => binaryCharacter (fun _ => true) (f x) * Uniform (Reg n) x) =
      djPhaseState (parityFun f) := by
    funext x
    rw [djPhaseState, hzero, phaseOracle_apply]
    change _ = (if bitParity (f x) then (-1 : ℂ) else 1) * Uniform (Reg n) x
    rw [all_output_character]
  simp only [affineWord, Run, applyGate_tensorGate, applyGate_hadamardN_ket_zero]
  change ApplyGate (TensorGate (HadamardN n) 1)
    (Run (outputOracle f) [Step.query]
      (TensorState (Uniform (Reg n)) (outputAnswer (fun _ => true)))) = _
  rw [outputOracle_kickback, applyGate_tensorGate, applyGate_one, hp]
  rfl

/-- One real multi-output oracle invocation decides the parity promise with certainty, from fully prepared physical registers. -/
theorem parityPromise_actual_readout {n m : ℕ} (f : Reg n → Reg m) :
    (ParityConstant f →
      MeasureProb (Run (outputOracle f) (affineWord n m)
        (TensorState (Ket (ZeroStr n)) (Ket (fun _ => true))))
        ({ZeroStr n} ×ˢ (Finset.univ : Finset (Reg m))) = 1) ∧
    (ParityBalanced f →
      MeasureProb (Run (outputOracle f) (affineWord n m)
        (TensorState (Ket (ZeroStr n)) (Ket (fun _ => true))))
        ({ZeroStr n} ×ˢ (Finset.univ : Finset (Reg m))) = 0 ∧
      MeasureProb (Run (outputOracle f) (affineWord n m)
        (TensorState (Ket (ZeroStr n)) (Ket (fun _ => true))))
        ((Finset.univ.erase (ZeroStr n)) ×ˢ (Finset.univ : Finset (Reg m))) = 1) ∧
    QueryCount (affineWord n m) = 1 := by
  simp only [parityPromise_actual_run, measureProb_tensorState_left (outputAnswer_normalized _)]
  exact ⟨(parityPromise_one_run f).1, (parityPromise_one_run f).2.1, rfl⟩

end Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise
