/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
set_option warningAsError false
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

def echoGenerator : UniformBqpGenerator where
  controlBound := 10
  machine := echoMachine
  timeCoefficient := 14
  timeDegree := 1
  wordCoefficient := 1
  wordDegree := 1
  spaceCoefficient := 2
  spaceDegree := 1

def echoGate : FiniteGateCode := .h 0

def echoWord (n : ℕ) : ℕ × List FiniteGateCode := (n + 1, [echoGate])

def echoEncoding (n : ℕ) : List Bool := encodeUniformBqpWord (n + 1) [echoGate]

def echoSteps (n : ℕ) : ℕ := 2 * n + 14

def hadamardDigit (s : ℤ) : FiniteDigitAmplitude := ⟨s, 0, true, 1⟩

def xDigit (s : ℤ) : FiniteDigitAmplitude := ⟨s, 0, false, 0⟩

def cnotDigit (s : ℤ) : FiniteDigitAmplitude := ⟨s, 0, false, 0⟩

def tDigit : FiniteDigitAmplitude := ⟨1, 1, true, 1⟩

def tAdjDigit : FiniteDigitAmplitude := ⟨1, -1, true, 1⟩

structure GateProgram where

  gates : List FiniteGateCode

  staircase : ∀ i : ℕ, finiteWordLegal (i + 1) (gates.take (i + 1)) = true

def GateProgram.gateCount (P : GateProgram) : ℕ := P.gates.length

def GateProgram.prefixBits (P : GateProgram) (r : ℕ) : List Bool :=
  (P.gates.take r).flatMap encodeFiniteGateCode

def GateProgram.prefixBitCount (P : GateProgram) (r : ℕ) : ℕ :=
  (P.prefixBits r).length

def GateProgram.programBits (P : GateProgram) : List Bool :=
  P.gates.flatMap encodeFiniteGateCode

def GateProgram.bitCount (P : GateProgram) : ℕ := P.programBits.length

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

theorem take_min_length {α : Type} (l : List α) (n : ℕ) :
    l.take (min n l.length) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), List.take_length, take_eq_self_of_length_le l n (by omega)]

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

theorem GateProgram.take_min_eq (P : GateProgram) (n : ℕ) :
    P.gates.take (min n P.gateCount) = P.gates.take n :=
  take_min_length P.gates n

theorem GateProgram.prefixBits_min (P : GateProgram) (n : ℕ) :
    P.prefixBits (min n P.gateCount) = (P.gates.take n).flatMap encodeFiniteGateCode := by
  rw [GateProgram.prefixBits, GateProgram.take_min_eq]

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

theorem finiteWordLegal_succ {n : ℕ} {gs : List FiniteGateCode}
    (hg : finiteWordLegal n gs = true) : finiteWordLegal (n + 1) gs = true := by
  rw [finiteWordLegal, List.all_eq_true] at hg
  rw [finiteWordLegal, List.all_eq_true]
  intro g hmem
  exact finiteCodeLegal_succ (hg g hmem)

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

theorem padWire_zero (k w : ℕ) : padWire 0 k w = w + k := by
  simp [padWire]

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

theorem GateProgram.staircase_legal (P : GateProgram) (n : ℕ) :
    finiteWordLegal (n + 1) (P.gates.take n) = true := by
  cases n with
  | zero => simp [finiteWordLegal]
  | succ n =>
    have h := P.staircase n
    show finiteWordLegal (n + 2) (P.gates.take (n + 1)) = true
    exact finiteWordLegal_succ h

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

theorem GenState.idx_ofIdx : ∀ i : Fin 9, GenState.idx (GenState.ofIdx i) = i := by
  decide

theorem GenState.ofIdx_idx (s : GenState) : GenState.ofIdx (GenState.idx s) = s := by
  cases s <;> rfl

structure GenControl (L S : ℕ) where

  state : GenState

  counter : Fin (L + 1)

  index : Fin (S + 1)

abbrev PControl (P : GateProgram) : Type :=
  GenControl P.gateCount (P.bitCount + 2)

instance genControlInhabited (L S : ℕ) : Inhabited (GenControl L S) :=
  ⟨⟨.scan, ⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩

def genInnerSize (L S : ℕ) : ℕ := (L + 1) * (S + 1)

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

def genInnerCounter (L S : ℕ) (x : Fin (genInnerSize L S)) : Fin (L + 1) :=
  ⟨x.val / (S + 1), by
    have hlt : x.val < (L + 1) * (S + 1) := by
      simpa only [genInnerSize] using x.isLt
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < S + 1)]
    exact hlt⟩

def genInnerIndex (L S : ℕ) (x : Fin (genInnerSize L S)) : Fin (S + 1) :=
  ⟨x.val % (S + 1), Nat.mod_lt _ (by omega : 0 < S + 1)⟩

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

def genControlSize (L S : ℕ) : ℕ := 9 * genInnerSize L S

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

def genLabelState (L S : ℕ) (l : Fin (genControlSize L S)) : Fin 9 :=
  ⟨l.val / genInnerSize L S, by
    have hlt : l.val < 9 * genInnerSize L S := by
      simpa only [genControlSize] using l.isLt
    have hpos : 0 < genInnerSize L S := by
      simp only [genInnerSize]
      exact Nat.mul_pos (by omega) (by omega)
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hlt⟩

def genLabelInner (L S : ℕ) (l : Fin (genControlSize L S)) : Fin (genInnerSize L S) :=
  ⟨l.val % genInnerSize L S, by
    have hpos : 0 < genInnerSize L S := by
      simp only [genInnerSize]
      exact Nat.mul_pos (by omega) (by omega)
    exact Nat.mod_lt _ hpos⟩

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

def genEncode (L S : ℕ) (c : GenControl L S) : Fin (genControlSize L S) :=
  genLabel L S c.state.idx (genInner L S c.counter c.index)

def genDecode (L S : ℕ) (l : Fin (genControlSize L S)) : GenControl L S where
  state := GenState.ofIdx (genLabelState L S l)
  counter := genInnerCounter L S (genLabelInner L S l)
  index := genInnerIndex L S (genLabelInner L S l)

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

def GenControl.cappedSucc {L S : ℕ} (c : GenControl L S) : Fin (L + 1) :=
  ⟨min (c.counter.val + 1) L, by
    have h := Nat.min_le_right (c.counter.val + 1) L
    omega⟩

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

def genCoreMachine (P : GateProgram) : Turing.TM0.Machine (Option Bool) (PControl P) :=
  fun c a => genStepCore P c a

def genMachine (P : GateProgram) :
    Turing.TM0.Machine (Option Bool) (Fin (genControlSize P.gateCount (P.bitCount + 2) + 1)) :=
  fun v a =>
    if h : v.val < genControlSize P.gateCount (P.bitCount + 2) then
      (genStepCore P (genDecode P.gateCount (P.bitCount + 2) ⟨v.val, h⟩) a).map fun p =>
        (Fin.castSucc (genEncode P.gateCount (P.bitCount + 2) p.1), p.2)
    else none

def gateProgramWord (P : GateProgram) (n : ℕ) : ℕ × List FiniteGateCode :=
  (n + 1, P.gates.take n)

def gateProgramTimeCoefficient (P : GateProgram) : ℕ :=
  2 + 9 + 3 * P.bitCount

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

def FiniteGateCode.isExactFiniteDigit : FiniteGateCode → Bool
  | .h _ => true
  | .x _ => true
  | .t _ => true
  | .tdg _ => true
  | .cx _ _ => true

end Qatlib.Papers.QComplexity97.MachineDefs
