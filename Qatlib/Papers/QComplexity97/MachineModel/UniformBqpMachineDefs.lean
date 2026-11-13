/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs

/-!
# Uniform circuit generator definitions

This module supplies explicit Turing-machine data for uniform finite-gate circuit families in
the setting of [BernsteinVazirani1997]. It defines the small example `echoMachine` and the
prefix-legal gate lists packaged by `GateProgram`.

The transition function `genStepCore` scans a unary input and emits the encoding of a bounded
gate prefix. The functions `genEncode` and `genDecode` represent its structured control data by
finite labels, and `gateProgramGenerator` packages the resulting machine with polynomial
resource parameters.

## Main statements

* `GateProgram.staircase_legal`: a prefix of length `n` is legal on `n + 1` wires.
* `genDecode_encode`: decoding an encoded control record recovers the record.
* `gateProgramGenerator`: constructs a generator from a prefix-legal gate program.
* `FiniteGateCode.isExactFiniteDigit`: marks each finite gate-code constructor as supported.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace UniformBqpMachine

open Turing

/-- The eleven control states of the example circuit-encoding Turing machine. -/
inductive Echo where
  | scan
  | widthBit
  | widthStep
  | termBit
  | termStep
  | gateBit0
  | gateStep
  | gateBit1
  | rewind
  | back
  | done
  deriving DecidableEq, Repr

/-- Assigns each `Echo` control state its label in `Fin 11`. -/
def Echo.val : Echo → Fin (10 + 1)
  | .scan => 0
  | .widthBit => 1
  | .widthStep => 2
  | .termBit => 3
  | .termStep => 4
  | .gateBit0 => 5
  | .gateStep => 6
  | .gateBit1 => 7
  | .rewind => 8
  | .back => 9
  | .done => 10

/-- The eleven-label Turing machine that scans unary input, writes the fixed suffix for the
example gate word, and rewinds to its beginning. -/
def echoMachine : Turing.TM0.Machine (Option Bool) (Fin (10 + 1)) := fun q a =>
  match q.val with
  | 0 => if a = some true then
      some ⟨Echo.val .scan, Turing.TM0.Stmt.move Turing.Dir.right⟩
    else if a = none then
      some ⟨Echo.val .widthBit, Turing.TM0.Stmt.write none⟩
    else none
  | 1 => some ⟨Echo.val .widthStep, Turing.TM0.Stmt.write (some true)⟩
  | 2 => some ⟨Echo.val .termBit, Turing.TM0.Stmt.move Turing.Dir.right⟩
  | 3 => some ⟨Echo.val .termStep, Turing.TM0.Stmt.write (some false)⟩
  | 4 => some ⟨Echo.val .gateBit0, Turing.TM0.Stmt.move Turing.Dir.right⟩
  | 5 => some ⟨Echo.val .gateStep, Turing.TM0.Stmt.write (some false)⟩
  | 6 => some ⟨Echo.val .gateBit1, Turing.TM0.Stmt.move Turing.Dir.right⟩
  | 7 => some ⟨Echo.val .rewind, Turing.TM0.Stmt.write (some false)⟩
  | 8 => if a = none then
      some ⟨Echo.val .back, Turing.TM0.Stmt.write none⟩
    else
      some ⟨Echo.val .rewind, Turing.TM0.Stmt.move Turing.Dir.left⟩
  | 9 => some ⟨Echo.val .done, Turing.TM0.Stmt.move Turing.Dir.right⟩
  | _ => none

/-- Packages `echoMachine` as a `UniformBqpGenerator` with control bound `10` and linear time,
word, and space parameters. -/
def echoGenerator : UniformBqpGenerator where
  controlBound := 10
  machine := echoMachine
  timeCoefficient := 14
  timeDegree := 1
  wordCoefficient := 1
  wordDegree := 1
  spaceCoefficient := 2
  spaceDegree := 1

/-- The Hadamard gate code acting on wire `0`. -/
def echoGate : FiniteGateCode := .h 0

/-- The circuit word of width `n + 1` containing the single gate `echoGate`. -/
def echoWord (n : ℕ) : ℕ × List FiniteGateCode := (n + 1, [echoGate])

/-- The Boolean encoding of the width-`n + 1` word containing `echoGate`. -/
def echoEncoding (n : ℕ) : List Bool := encodeUniformBqpWord (n + 1) [echoGate]

/-- The step-count expression `2 * n + 14` used for the example generator. -/
def echoSteps (n : ℕ) : ℕ := 2 * n + 14

/-- Finite amplitude data representing `s * sqrt 2 / 2` with zero imaginary part. -/
def hadamardDigit (s : ℤ) : FiniteDigitAmplitude := ⟨s, 0, true, 1⟩

/-- Finite amplitude data representing the integer `s` with zero imaginary part. -/
def xDigit (s : ℤ) : FiniteDigitAmplitude := ⟨s, 0, false, 0⟩

/-- Finite amplitude data representing the integer `s` for controlled-NOT matrix entries. -/
def cnotDigit (s : ℤ) : FiniteDigitAmplitude := ⟨s, 0, false, 0⟩

/-- Finite amplitude data representing `(1 + I) * sqrt 2 / 2`. -/
def tDigit : FiniteDigitAmplitude := ⟨1, 1, true, 1⟩

/-- Finite amplitude data representing `(1 - I) * sqrt 2 / 2`. -/
def tAdjDigit : FiniteDigitAmplitude := ⟨1, -1, true, 1⟩

/-- A finite gate list whose prefix of length `i + 1` is legal on `i + 1` wires for every
natural number `i`. -/
structure GateProgram where

  gates : List FiniteGateCode

  staircase : ∀ i : ℕ, finiteWordLegal (i + 1) (gates.take (i + 1)) = true

/-- The number of gates in a `GateProgram`. -/
def GateProgram.gateCount (P : GateProgram) : ℕ := P.gates.length

/-- Concatenates the finite gate-code encodings of the first `r` gates of `P`. -/
def GateProgram.prefixBits (P : GateProgram) (r : ℕ) : List Bool :=
  (P.gates.take r).flatMap encodeFiniteGateCode

/-- The number of bits in the encoding of the first `r` gates of `P`. -/
def GateProgram.prefixBitCount (P : GateProgram) (r : ℕ) : ℕ :=
  (P.prefixBits r).length

/-- Concatenates the finite gate-code encodings of all gates of `P`. -/
def GateProgram.programBits (P : GateProgram) : List Bool :=
  P.gates.flatMap encodeFiniteGateCode

/-- The number of bits in the complete gate-program encoding. -/
def GateProgram.bitCount (P : GateProgram) : ℕ := P.programBits.length

/-- Taking at least the length of a list returns the whole list. -/
theorem take_eq_self_of_length_le {α : Type} (l : List α) (n : ℕ) (h : l.length ≤ n) :
    l.take n = l := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.length_cons] at h
      have h' : t.length ≤ n := by omega
      show List.take (n + 1) (a :: t) = a :: t
      rw [List.take_succ_cons, ih n h']

/-- Capping a take count at the list length does not change the resulting prefix. -/
theorem take_min_length {α : Type} (l : List α) (n : ℕ) :
    l.take (min n l.length) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), List.take_length, take_eq_self_of_length_le l n (by omega)]

/-- The bit count of any encoded gate prefix is at most the complete program bit count. -/
theorem GateProgram.prefixBitCount_le (P : GateProgram) (r : ℕ) :
    P.prefixBitCount r ≤ P.bitCount := by
  have hbits : (P.gates.take r).flatMap encodeFiniteGateCode ++
      (P.gates.drop r).flatMap encodeFiniteGateCode = P.gates.flatMap encodeFiniteGateCode := by
    rw [← List.flatMap_append, List.take_append_drop]
  have hlen : P.prefixBitCount r + ((P.gates.drop r).flatMap encodeFiniteGateCode).length
      = P.bitCount := by
    rw [GateProgram.prefixBitCount, GateProgram.bitCount, GateProgram.programBits,
      GateProgram.prefixBits, ← hbits, List.length_append]
  omega

/-- Capping a gate-prefix length at `P.gateCount` does not change the prefix. -/
theorem GateProgram.take_min_eq (P : GateProgram) (n : ℕ) :
    P.gates.take (min n P.gateCount) = P.gates.take n :=
  take_min_length P.gates n

/-- The encoded prefix at `min n P.gateCount` is the concatenated encoding of `P.gates.take n`. -/
theorem GateProgram.prefixBits_min (P : GateProgram) (n : ℕ) :
    P.prefixBits (min n P.gateCount) = (P.gates.take n).flatMap encodeFiniteGateCode := by
  rw [GateProgram.prefixBits, GateProgram.take_min_eq]

/-- A gate code legal on `n` wires remains legal on `n + 1` wires. -/
theorem finiteCodeLegal_succ {n : ℕ} {g : FiniteGateCode} (hg : finiteCodeLegal n g = true) :
    finiteCodeLegal (n + 1) g = true := by
  cases g with
  | h w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | x w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | t w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | tdg w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | cx c t =>
    have hct : c < n ∧ t < n ∧ c ≠ t := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega

/-- A gate word legal on `n` wires remains legal on `n + 1` wires. -/
theorem finiteWordLegal_succ {n : ℕ} {gs : List FiniteGateCode}
    (hg : finiteWordLegal n gs = true) : finiteWordLegal (n + 1) gs = true := by
  rw [finiteWordLegal, List.all_eq_true] at hg
  rw [finiteWordLegal, List.all_eq_true]
  intro g hmem
  exact finiteCodeLegal_succ (hg g hmem)

/-- A gate code legal on `n` wires remains legal on any number `m` of wires with `n ≤ m`. -/
theorem finiteCodeLegal_mono {n : ℕ} {g : FiniteGateCode} (hg : finiteCodeLegal n g = true)
    {m : ℕ} (hm : n ≤ m) : finiteCodeLegal m g = true := by
  cases g with
  | h w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | x w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | t w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | tdg w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega
  | cx c t =>
    have hct : c < n ∧ t < n ∧ c ≠ t := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal]
    omega

/-- Padding a wire index at cutoff `0` shifts it from `w` to `w + k`. -/
theorem padWire_zero (k w : ℕ) : padWire 0 k w = w + k := by
  simp [padWire]

/-- Shifting every wire of a gate legal on `n` wires by `n` gives a gate legal on `2 * n` wires. -/
theorem finiteCodeLegal_pad (n : ℕ) {g : FiniteGateCode} (hg : finiteCodeLegal n g = true) :
    finiteCodeLegal (2 * n) (padFiniteCode 0 n g) = true := by
  cases g with
  | h w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal, padFiniteCode, padWire]
    omega
  | x w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal, padFiniteCode, padWire]
    omega
  | t w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal, padFiniteCode, padWire]
    omega
  | tdg w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal, padFiniteCode, padWire]
    omega
  | cx c t =>
    have hct : c < n ∧ t < n ∧ c ≠ t := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeLegal, padFiniteCode, padWire]
    omega

/-- The first `n` gates of a gate program are legal on `n + 1` wires. -/
theorem GateProgram.staircase_legal (P : GateProgram) (n : ℕ) :
    finiteWordLegal (n + 1) (P.gates.take n) = true := by
  cases n with
  | zero => simp [finiteWordLegal]
  | succ n =>
    have h := P.staircase n
    show finiteWordLegal (n + 2) (P.gates.take (n + 1)) = true
    exact finiteWordLegal_succ h

/-- The nine phases of the gate-program generator, from scanning through emission and rewinding
to termination. -/
inductive GenState where

  | scan

  | mark

  | term

  | afterTerm

  | emitWrite

  | emitAdvance

  | rewind

  | back

  | done
  deriving DecidableEq, Repr

instance genStateInhabited : Inhabited GenState := ⟨.scan⟩

/-- Encodes the nine generator phases as labels in `Fin 9`. -/
def GenState.idx : GenState → Fin 9
  | .scan => ⟨0, by omega⟩
  | .mark => ⟨1, by omega⟩
  | .term => ⟨2, by omega⟩
  | .afterTerm => ⟨3, by omega⟩
  | .emitWrite => ⟨4, by omega⟩
  | .emitAdvance => ⟨5, by omega⟩
  | .rewind => ⟨6, by omega⟩
  | .back => ⟨7, by omega⟩
  | .done => ⟨8, by omega⟩

/-- Decodes a label in `Fin 9` to its generator phase. -/
def GenState.ofIdx (i : Fin 9) : GenState :=
  match i.val with
  | 0 => .scan
  | 1 => .mark
  | 2 => .term
  | 3 => .afterTerm
  | 4 => .emitWrite
  | 5 => .emitAdvance
  | 6 => .rewind
  | 7 => .back
  | _ => .done

/-- Encoding a decoded generator-phase label returns the original label. -/
theorem GenState.idx_ofIdx : ∀ i : Fin 9, GenState.idx (GenState.ofIdx i) = i := by
  decide

/-- Decoding an encoded generator phase returns the original phase. -/
theorem GenState.ofIdx_idx (s : GenState) : GenState.ofIdx (GenState.idx s) = s := by
  cases s <;> rfl

/-- Generator control data consisting of a phase, a counter bounded by `L`, and an index bounded
by `S`. -/
structure GenControl (L S : ℕ) where

  state : GenState

  counter : Fin (L + 1)

  index : Fin (S + 1)

/-- The control-data type for `P`, with counter bound `P.gateCount` and index bound `P.bitCount
+ 2`. -/
abbrev PControl (P : GateProgram) : Type :=
  GenControl P.gateCount (P.bitCount + 2)

instance genControlInhabited (L S : ℕ) : Inhabited (GenControl L S) :=
  ⟨⟨.scan, ⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩

/-- The number `(L + 1) * (S + 1)` of counter-index pairs. -/
def genInnerSize (L S : ℕ) : ℕ := (L + 1) * (S + 1)

/-- Encodes a counter-index pair by `c.val * (S + 1) + i.val`. -/
def genInner (L S : ℕ) (c : Fin (L + 1)) (i : Fin (S + 1)) : Fin (genInnerSize L S) :=
  ⟨c.val * (S + 1) + i.val, by
    have hc : c.val * (S + 1) ≤ L * (S + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_pred_of_lt c.isLt)
    have hi : i.val < S + 1 := i.isLt
    have hlt : L * (S + 1) + (S + 1) = (L + 1) * (S + 1) := by
      have h1 := Nat.succ_mul L (S + 1)
      simpa [Nat.succ_eq_add_one] using h1.symm
    simp only [genInnerSize]
    omega⟩

/-- Recovers the counter component of an inner label by division by `S + 1`. -/
def genInnerCounter (L S : ℕ) (x : Fin (genInnerSize L S)) : Fin (L + 1) :=
  ⟨x.val / (S + 1), by
    have hlt : x.val < (L + 1) * (S + 1) := by
      simpa only [genInnerSize] using x.isLt
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < S + 1)]
    exact hlt⟩

/-- Recovers the index component of an inner label by reduction modulo `S + 1`. -/
def genInnerIndex (L S : ℕ) (x : Fin (genInnerSize L S)) : Fin (S + 1) :=
  ⟨x.val % (S + 1), Nat.mod_lt _ (by omega : 0 < S + 1)⟩

/-- Division and remainder by `S + 1` recover both components of an encoded counter-index pair. -/
theorem genInner_div_mod {L S : ℕ} (c : Fin (L + 1)) (i : Fin (S + 1)) :
    (genInner L S c i).val / (S + 1) = c.val ∧
      (genInner L S c i).val % (S + 1) = i.val := by
  rw [genInner]
  constructor
  · have h := Nat.div_add_mod' (c.val * (S + 1) + i.val) (S + 1)
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt] at h
    have hdiv : (c.val * (S + 1) + i.val) / (S + 1) * (S + 1) = c.val * (S + 1) := by
      omega
    exact Nat.mul_right_cancel (by omega : 0 < S + 1) hdiv
  · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]

/-- The number `9 * genInnerSize L S` of phase-counter-index labels. -/
def genControlSize (L S : ℕ) : ℕ := 9 * genInnerSize L S

/-- Combines a phase label and an inner label using blocks of size `genInnerSize L S`. -/
def genLabel (L S : ℕ) (s : Fin 9) (x : Fin (genInnerSize L S)) :
    Fin (genControlSize L S) :=
  ⟨s.val * genInnerSize L S + x.val, by
    have hs : s.val * genInnerSize L S ≤ 8 * genInnerSize L S :=
      Nat.mul_le_mul_right _ (Nat.le_pred_of_lt s.isLt)
    have hx : x.val < genInnerSize L S := x.isLt
    have hlt : 8 * genInnerSize L S + genInnerSize L S = 9 * genInnerSize L S := by
      have h1 := Nat.succ_mul 8 (genInnerSize L S)
      simpa [Nat.succ_eq_add_one] using h1.symm
    simp only [genControlSize]
    omega⟩

/-- Extracts the phase label by division by `genInnerSize L S`. -/
def genLabelState (L S : ℕ) (l : Fin (genControlSize L S)) : Fin 9 :=
  ⟨l.val / genInnerSize L S, by
    have hlt : l.val < 9 * genInnerSize L S := by
      simpa only [genControlSize] using l.isLt
    have hpos : 0 < genInnerSize L S := by
      simp only [genInnerSize]
      exact Nat.mul_pos (by omega) (by omega)
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hlt⟩

/-- Extracts the inner label by reduction modulo `genInnerSize L S`. -/
def genLabelInner (L S : ℕ) (l : Fin (genControlSize L S)) : Fin (genInnerSize L S) :=
  ⟨l.val % genInnerSize L S, by
    have hpos : 0 < genInnerSize L S := by
      simp only [genInnerSize]
      exact Nat.mul_pos (by omega) (by omega)
    exact Nat.mod_lt _ hpos⟩

/-- Division and remainder by the inner-label block size recover both components of `genLabel`. -/
theorem genLabel_div_mod {L S : ℕ} (s : Fin 9) (x : Fin (genInnerSize L S)) :
    (genLabel L S s x).val / genInnerSize L S = s.val ∧
      (genLabel L S s x).val % genInnerSize L S = x.val := by
  rw [genLabel]
  constructor
  · have h := Nat.div_add_mod' (s.val * genInnerSize L S + x.val) (genInnerSize L S)
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt x.isLt] at h
    have hdiv : (s.val * genInnerSize L S + x.val) / genInnerSize L S * genInnerSize L S
        = s.val * genInnerSize L S := by omega
    have hpos : 0 < genInnerSize L S := by
      simp only [genInnerSize]
      exact Nat.mul_pos (by omega) (by omega)
    exact Nat.mul_right_cancel hpos hdiv
  · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt x.isLt]

/-- Encodes a structured generator control record as one finite label. -/
def genEncode (L S : ℕ) (c : GenControl L S) : Fin (genControlSize L S) :=
  genLabel L S c.state.idx (genInner L S c.counter c.index)

/-- Decodes a finite control label into its phase, counter, and index. -/
def genDecode (L S : ℕ) (l : Fin (genControlSize L S)) : GenControl L S where
  state := GenState.ofIdx (genLabelState L S l)
  counter := genInnerCounter L S (genLabelInner L S l)
  index := genInnerIndex L S (genLabelInner L S l)

/-- Decoding an encoded generator control record returns the original record. -/
theorem genDecode_encode {L S : ℕ} (c : GenControl L S) :
    genDecode L S (genEncode L S c) = c := by
  have hlabel := genLabel_div_mod c.state.idx (genInner L S c.counter c.index)
  have hinner := genInner_div_mod c.counter c.index
  have hstate : genLabelState L S (genEncode L S c) = c.state.idx := by
    apply Fin.ext
    exact hlabel.1
  have hinner' : genLabelInner L S (genEncode L S c) = genInner L S c.counter c.index := by
    apply Fin.ext
    exact hlabel.2
  have hcounter : genInnerCounter L S (genInner L S c.counter c.index) = c.counter := by
    apply Fin.ext
    exact hinner.1
  have hindex : genInnerIndex L S (genInner L S c.counter c.index) = c.index := by
    apply Fin.ext
    exact hinner.2
  have hdec : genDecode L S (genEncode L S c)
      = ⟨GenState.ofIdx (genLabelState L S (genEncode L S c)),
        genInnerCounter L S (genLabelInner L S (genEncode L S c)),
        genInnerIndex L S (genLabelInner L S (genEncode L S c))⟩ := rfl
  rw [hdec, hstate, hinner', hcounter, hindex, GenState.ofIdx_idx]

/-- Increments the control counter, saturating at its upper bound `L`. -/
def GenControl.cappedSucc {L S : ℕ} (c : GenControl L S) : Fin (L + 1) :=
  ⟨min (c.counter.val + 1) L, by
    have h := Nat.min_le_right (c.counter.val + 1) L
    omega⟩

/-- The gate-program transition function on structured control data and the current tape symbol,
returning the next control and instruction or halting. -/
def genStepCore (P : GateProgram) (c : PControl P) (a : Option Bool) :
    Option (PControl P × Turing.TM0.Stmt (Option Bool)) :=
  let r := c.counter
  let j := c.index
  match c.state with
  | .scan =>
      if a = some true then
        some (⟨⟨.scan, GenControl.cappedSucc c, j⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩)
      else if a = none then
        some (⟨⟨.mark, r, j⟩, Turing.TM0.Stmt.write (some true)⟩)
      else none
  | .mark =>
      some (⟨⟨.term, r, j⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩)
  | .term =>
      some (⟨⟨.afterTerm, r, j⟩, Turing.TM0.Stmt.write (some false)⟩)
  | .afterTerm =>
      if P.prefixBitCount r.val = 0 then
        some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.write (some false)⟩)
      else
        some (⟨⟨.emitWrite, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩)
  | .emitWrite =>
      if h : j.val < P.prefixBitCount r.val then
        some (⟨⟨.emitAdvance, r, j⟩,
          Turing.TM0.Stmt.write (some ((P.prefixBits r.val).getD j.val false))⟩)
      else
        some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩,
          Turing.TM0.Stmt.write (some ((P.prefixBits r.val).getD j.val false))⟩)
  | .emitAdvance =>
      if h : j.val + 1 < P.prefixBitCount r.val then
        some (⟨⟨.emitWrite, r, ⟨j.val + 1, by
            have hle := P.prefixBitCount_le r.val
            omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩)
      else
        some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩,
          Turing.TM0.Stmt.write (some ((P.prefixBits r.val).getD j.val false))⟩)
  | .rewind =>
      if a = none then
        some (⟨⟨.back, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.write none⟩)
      else
        some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.left⟩)
  | .back =>
      some (⟨⟨.done, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩)
  | .done => none

/-- The Turing machine whose structured-control transitions are given by `genStepCore P`. -/
def genCoreMachine (P : GateProgram) : Turing.TM0.Machine (Option Bool) (PControl P) :=
  fun c a => genStepCore P c a

/-- Transports `genStepCore P` to finite control labels, with one additional label that halts. -/
def genMachine (P : GateProgram) :
    Turing.TM0.Machine (Option Bool) (Fin (genControlSize P.gateCount (P.bitCount + 2) + 1)) :=
  fun v a =>
    if h : v.val < genControlSize P.gateCount (P.bitCount + 2) then
      (genStepCore P (genDecode P.gateCount (P.bitCount + 2) ⟨v.val, h⟩) a).map fun p =>
        (Fin.castSucc (genEncode P.gateCount (P.bitCount + 2) p.1), p.2)
    else none

/-- The width-`n + 1` circuit word formed by the first `n` gates of `P`. -/
def gateProgramWord (P : GateProgram) (n : ℕ) : ℕ × List FiniteGateCode :=
  (n + 1, P.gates.take n)

/-- The coefficient `11 + 3 * P.bitCount` used in the generator time bound. -/
def gateProgramTimeCoefficient (P : GateProgram) : ℕ :=
  2 + 9 + 3 * P.bitCount

/-- Packages the finite-label gate-program machine with linear time and space parameters and a
constant gate-count parameter. -/
def gateProgramGenerator (P : GateProgram) : UniformBqpGenerator where
  controlBound := genControlSize P.gateCount (P.bitCount + 2)
  machine := genMachine P
  timeCoefficient := gateProgramTimeCoefficient P
  timeDegree := 1
  wordCoefficient := P.gateCount
  wordDegree := 0
  spaceCoefficient := 1
  spaceDegree := 1

end UniformBqpMachine

/-- The Boolean marker that returns `true` for every constructor of `FiniteGateCode`. -/
def FiniteGateCode.isExactFiniteDigit : FiniteGateCode → Bool
  | .h _ => true
  | .x _ => true
  | .t _ => true
  | .tdg _ => true
  | .cx _ _ => true

end Qatlib.Papers.QComplexity97.MachineDefs
