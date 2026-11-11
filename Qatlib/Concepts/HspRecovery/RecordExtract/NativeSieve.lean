/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.NativeEndpoint
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw

/-!
# Native dihedral oracle and instruction semantics

This module verifies the native oracle and gate interfaces used for the dihedral sieve setting
of [Kuperberg2005]. The oracle preserves address and tag bits, is involutive, and gives a
unitary matrix; native instruction lists therefore produce normalized runs.

An explicit generator constructs the empty program. That program succeeds for modulus one and
fails on the displayed modulus-two reflection oracle. The local-letter decoder also exposes each
instruction as a query or a local gate with bounded controlled-phase exponent.

## Main statements

* `nativeOracle_unitary` and `nativeCircuit_unitary`: unitarity of native execution.
* `native_period_one`: a constructed zero-query program for modulus one.
* `nativeEmpty_period_two_failure`: failure of the empty program at the displayed modulus-two
  instance.
* `nativeLocalLetter_semantics`: correspondence between decoded letters and native instructions.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false


open Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib

/-- A valid address-bit index retains its numeric value when embedded as a native wire. -/
theorem nativeWire_val_address (N o w : ℕ) (i : Fin (sourceAddressBits N)) :
    (nativeWire N o w i.val).val = i.val := by
  apply Nat.mod_eq_of_lt
  unfold nativeWidth
  omega

/-- The native oracle permutation preserves each address bit. -/
theorem nativeOracle_address_bit (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o)
    (x : Reg (nativeWidth N o w)) (i : Fin (sourceAddressBits N)) :
    nativeOraclePermutation N o w f x (nativeWire N o w i.val) =
      x (nativeWire N o w i.val) := by
  simp only [nativeOraclePermutation, nativeWire_val_address]
  split_ifs with h
  · omega
  · rfl

/-- The native oracle permutation preserves the decoded address. -/
theorem nativeOracle_address (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o)
    (x : Reg (nativeWidth N o w)) :
    nativeAddress N o w (nativeOraclePermutation N o w f x) = nativeAddress N o w x := by
  simp only [nativeAddress, nativeOracle_address_bit]

/-- The native oracle permutation preserves the tag bit. -/
theorem nativeOracle_tag (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o)
    (x : Reg (nativeWidth N o w)) :
    nativeOraclePermutation N o w f x (nativeWire N o w (sourceAddressBits N)) =
      x (nativeWire N o w (sourceAddressBits N)) := by
  have hwire : (nativeWire N o w (sourceAddressBits N)).val = sourceAddressBits N := by
    apply Nat.mod_eq_of_lt
    unfold nativeWidth
    omega
  simp only [nativeOraclePermutation, hwire]
  split_ifs with h
  · omega
  · rfl

/-- Applying the native oracle permutation twice returns the original register. -/
theorem nativeOraclePermutation_involutive (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) :
    Function.Involutive (nativeOraclePermutation N o w f) := by
  intro x
  funext i
  rw [nativeOraclePermutation]
  simp only [nativeOracle_address, nativeOracle_tag]
  simp only [nativeOraclePermutation]
  split_ifs <;> simp

/-- The matrix of the native oracle is unitary. -/
theorem nativeOracle_unitary (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) :
    nativeOracle N o w f ∈ Matrix.unitaryGroup (Reg (nativeWidth N o w)) ℂ :=
  permMatrix_unitary (nativeOraclePermutation_involutive N o w f)

/-- Every decoded native instruction forms a unitary single-instruction circuit. -/
theorem nativeInstruction_unitary (N o w t : ℕ) :
    IsUnitaryCircuit [nativeInstruction N o w t] := by
  unfold nativeInstruction
  split_ifs <;> simp [localGateMatrix_unitary]

/-- Every native instruction list defines a unitary circuit. -/
theorem nativeCircuit_unitary (N o w : ℕ) (code : List ℕ) :
    IsUnitaryCircuit (nativeCircuit N o w code) := by
  intro U hU
  obtain ⟨t, _ht, he⟩ := List.mem_map.mp hU
  exact nativeInstruction_unitary N o w t U (by simp [he])

/-- Running a native circuit with its native oracle from the all-false basis state produces a
normalized state. -/
theorem nativeRun_normalized (N o w : ℕ) (code : List ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) :
    Normalized (Run (nativeOracle N o w f) (nativeCircuit N o w code)
      (Ket (fun _ => false))) :=
  (nativeCircuit_unitary N o w code).normalized_run (nativeOracle_unitary N o w f)
    (normalized_ket _)

/-- The source generator that empties its input stack and leaves the encoding of zero workspace
and an empty instruction list. -/
def nativeEmptyGenerator : SourceGenerator 0 1 := fun _ =>
  .peek 0 (fun _ head => if head.isSome then 1 else 0)
    (.branch (fun v => v == 1)
      (.pop 0 (fun v _ => v) (.goto (fun _ => 0)))
      (.push 0 (fun _ => none) (.push 0 (fun _ => none) .halt)))

/-- Starting from the supplied stack, the empty-program generator halts after `xs.length + 1`
steps with control value zero and stack `[none, none]`. -/
theorem nativeEmptyGenerator_run (xs : List (Option Bool)) (v : Fin 2) :
    sourceGeneratorRun nativeEmptyGenerator (xs.length + 1)
      (⟨some 0, v, Function.update (fun _ => []) 0 xs⟩ : SourceGeneratorCfg 0 1) =
      ⟨none, 0, Function.update (fun _ => []) 0 [none, none]⟩ := by
  induction xs generalizing v with
  | nil =>
    simp [sourceGeneratorRun, nativeEmptyGenerator, Turing.TM2.step, Turing.TM2.stepAux]
  | cons x xs ih =>
    simpa [sourceGeneratorRun, nativeEmptyGenerator, Turing.TM2.step, Turing.TM2.stepAux]
      using ih 1

/-- The empty-program generator constructs the zero-workspace empty native program within the
stated encoded-input-length bound. -/
theorem nativeEmptyGenerator_constructed (N o : ℕ) :
    NativeConstructed nativeEmptyGenerator N o 0 [] ((sourceEncodeNats [N, o]).length + 1) := by
  unfold NativeConstructed sourceGeneratorStart
  rw [show Turing.TM2.init 0 (sourceEncodeNats [N, o]) =
    (⟨some 0, 0, Function.update (fun _ => []) 0 (sourceEncodeNats [N, o])⟩ :
      SourceGeneratorCfg 0 1) from rfl, nativeEmptyGenerator_run]
  simp [sourceEncodeProgram, sourceEncodeNats, sourceEncodeNat]

/-- The empty native program has slope-output probability one exactly for a slope with
representative zero, and zero otherwise. -/
theorem nativeEmpty_probability (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) (s : ZMod N) :
    nativeSlopeProbability N o w [] f s = if s.val = 0 then 1 else 0 := by
  classical
  have he : (0 = s.val) ↔ s = 0 := eq_comm.trans (ZMod.val_eq_zero s)
  simp [nativeSlopeProbability, nativeCircuit, MeasureProb, bornProb_ket, nativeAddress,
    he]

/-- At modulus one, the empty-program generator constructs a unitary zero-query program with
slope-output probability one for every oracle and slope. -/
theorem native_period_one (o : ℕ) :
    ∃ (w t : ℕ) (code : List ℕ),
      NativeConstructed nativeEmptyGenerator 1 o w code t ∧
      IsUnitaryCircuit (nativeCircuit 1 o w code) ∧
      QueryCount (nativeCircuit 1 o w code) = 0 ∧
      ∀ (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg 1 → Reg o) (s : ZMod 1),
        nativeSlopeProbability 1 o w code f s = 1 := by
  refine ⟨0, (sourceEncodeNats [1, o]).length + 1, [],
    nativeEmptyGenerator_constructed 1 o, nativeCircuit_unitary 1 o 0 [], rfl, ?_⟩
  intro f s
  have hs : s = 0 := Subsingleton.elim _ _
  simp [nativeEmpty_probability, hs]

/-- The one-bit oracle at modulus two returning the exclusive-or of the rotation-label parity
and the Boolean tag. -/
def nativeParityOracle (p : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg 2) : Reg 1 :=
  fun _ => decide (p.1.val = 1) ^^ p.2

/-- The native parity oracle hides the reflection with parameter one at modulus two. -/
theorem nativeParityOracle_hides :
    Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReflectionHides 2 nativeParityOracle 1 := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

/-- The empty native program has zero probability of outputting the hidden slope one for
`nativeParityOracle`. -/
theorem nativeEmpty_period_two_failure :
    nativeSlopeProbability 2 1 0 [] nativeParityOracle 1 = 0 := by
  rw [nativeEmpty_probability]
  norm_num

/-- Decode an instruction number as either an oracle query or a local Hadamard,
controlled-phase, or swap gate. -/
def nativeLocalLetter (N o w t : ℕ) : Option (LocalQFTGate (nativeWidth N o w)) :=
  if t % 4 = 0 then none else
  if t % 4 = 1 then some (.h (nativeWire N o w (t / 4))) else
  if t % 4 = 2 then some (.cp
    (nativeWire N o w (t / 4)) (nativeWire N o w (t / (4 * nativeWidth N o w)))
    ((t / (4 * nativeWidth N o w ^ 2)) % 4)
    (decide ((t / (16 * nativeWidth N o w ^ 2)) % 2 = 1))) else
  some (.swap (nativeWire N o w (t / 4))
    (nativeWire N o w (t / (4 * nativeWidth N o w))))

/-- Interpreting the optional local-gate letter, with `none` as a query, gives exactly the
corresponding native instruction. -/
theorem nativeLocalLetter_semantics (N o w t : ℕ) :
    nativeInstruction N o w t =
      (nativeLocalLetter N o w t).elim Step.query (fun g => Step.gate (localGateMatrix g)) := by
  unfold nativeLocalLetter nativeInstruction
  split_ifs <;> rfl

/-- Every controlled-phase gate returned by the native local-letter decoder has exponent at most
three. -/
theorem nativeLocalLetter_phase_bound (N o w t : ℕ)
    (a b : Fin (nativeWidth N o w)) (e : ℕ) (neg : Bool)
    (h : nativeLocalLetter N o w t = some (.cp a b e neg)) : e ≤ 3 := by
  unfold nativeLocalLetter at h
  split_ifs at h <;> cases h
  omega

end Qatlib.Concepts.HspRecovery.RecordExtract
