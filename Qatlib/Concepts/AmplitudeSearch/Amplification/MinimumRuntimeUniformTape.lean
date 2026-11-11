/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Analysis.SpecificLimits.Normed
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumRuntimeDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder
import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Mathlib.Data.List.GetD
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumRuntimeNativeAttempt

/-!
# Native tape uniform sampling

This module verifies `UniformTape.program`, a fixed-alphabet tape program that samples uniformly
below a positive bound `m ≤ 2^b` by rejection sampling. The scan and restart lemmas connect
concrete tape runs to the unit-weight `weightedSampler`, giving exact capped probabilities, zero
nontermination mass on valid inputs, and a uniform output law for `nativeTerminalLaw`.

The resource statements track native CPU steps and consumed fair bits separately, compute their
terminal expectations, and bound all visited and initially occupied cells by `b+2`. The example
with `b = 2` and `m = 3` shows that finite expected CPU cost can coexist with unbounded CPU
costs in the terminal support. The surrounding minimum-finding context is described in
[DurrHoyer1996].

## Main statements

- `nativeLaw_cycle_all` identifies CPU budgets at cycle boundaries with the capped sampler law.
* `nativeTerminalLaw_output_uniform` gives the uniform law on the integers below `m` for valid
  inputs.
* `nativeTerminalLaw_cpu_mean` and `nativeTerminalLaw_reads_mean` compute the exact expected CPU
  steps and fair-bit reads.
* `nativeTerminalLaw_no_worst_cpu_bound` exhibits a valid input with unbounded supported CPU
  costs.
* `run_workspace_cells_le`, `peakWorkspaceCells_le`, and `nativeTerminalLaw_workspace` give the
  `b+2` workspace bound.

## References

- [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CappedFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

open Qatlib
open scoped ENNReal

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount Matrix
open Classical
open scoped ComplexOrder
open NativeTape
open scoped ENNReal
set_option warningAsError false

/-- In a read state, `program` uses the corresponding comparison command `readCommand` for the
current symbol. -/
theorem read_rule (c : Fin 3) (a : Symbol) : program (readState c) a = readCommand c a := by
  fin_cases c <;> rfl

/-- In a move state, `program` deterministically moves one cell to the right and returns to the
corresponding read state. -/
theorem move_rule (c : Fin 3) (a : Symbol) :
    program (moveState c) a = .det (readState c) (.move .right) := by
  fin_cases c <;> rfl

/-- The head of a tape whose right list begins with `a` contains `a`. -/
theorem head_cons (L : List Symbol) (a : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ L (a::R)).head = a := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.ListBlank.head_mk]

/-- The head of a tape with an empty right list is blank. -/
theorem head_nil (L : List Symbol) : (Turing.Tape.mk₂ L []).head = none := by
  rfl

/-- Writing `b` at the head replaces the first symbol of the right list and preserves the
remaining tape lists. -/
theorem tape_write (L : List Symbol) (a b : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ L (a::R)).write b = Turing.Tape.mk₂ L (b::R) := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]

/-- Moving right transfers the current head symbol to the front of the left list. -/
theorem tape_right (L : List Symbol) (a : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ L (a::R)).move .right = Turing.Tape.mk₂ (a::L) R := by
  simp [Turing.Tape.mk₂, Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]

/-- Moving left transfers the first symbol of the left list to the front of the right list. -/
theorem tape_left (L : List Symbol) (a : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ (a::L) R).move .left = Turing.Tape.mk₂ L (a::R) := by
  simp [Turing.Tape.mk₂, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]

/-- Scanning a register with an equally long random word takes exactly two steps per cell,
replaces each first field by its random bit, and accumulates the comparison state. The run
consumes exactly that word and leaves the suffix `raw` unread. -/
theorem scan (ys : List (Bool × Bool)) (ω raw : List Bool) (c : Fin 3) (L : List Symbol)
    (hlen : ω.length = ys.length) :
    let out := List.zipWith (fun b p => (b,p.2)) ω ys
    let r :=
        Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length)
        (ω++raw) ⟨readState c, Turing.Tape.mk₂ L (ys.map data)⟩
    r.cfg = ⟨readState (out.foldl compareUpdate c),
      Turing.Tape.mk₂ (out.reverse.map data ++ L) []⟩ ∧
    r.unread = raw ∧ r.bits = ω ∧ r.steps = 2*ys.length := by
  induction ys generalizing ω c L with
  | nil =>
    have hω : ω = [] := List.eq_nil_of_length_eq_zero hlen
    subst ω
    (try dsimp only)
    simp only [List.zipWith_nil_left, List.foldl_nil, List.reverse_nil, List.map_nil,
      List.nil_append, List.length_nil, mul_zero, Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, read_rule, head_nil, readCommand]
    split <;> simp [Result.bits, Result.steps]
  | cons p ys ih =>
    cases ω with
    | nil => simp at hlen
    | cons b ω =>
      have hlen' : ω.length = ys.length := by simpa using! hlen
      have hi := ih ω (compareUpdate c (b,p.2)) (cell b p.2 :: L) hlen'
      (try dsimp only at hi ⊢)
      rw [show 2*(p::ys).length = (2*ys.length+1)+1 by simp; omega]
      simp only [List.cons_append, List.map_cons, Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, read_rule, head_cons, data,
        readCommand, cell, advance, TM0StmtApply, tape_write]
      rw [move_rule]
      simp only [tape_right]
      simpa [Result.prepend, Result.bits, Result.steps, List.zipWith_cons_cons,
        List.reverse_cons, List.map_append, List.append_assoc, Nat.add_comm] using! hi

/-- Starting in control state `6`, rewinding past `xs` and the marker returns to read state `0`
in `xs.length+2` steps, with data word `xs.reverse ++ ys`. The run consumes no random bits
and preserves the entire unread input. -/
theorem rewind (xs ys : List (Bool × Bool)) (raw : List Bool) :
    let r := Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (xs.length+2) raw
      ⟨6, Turing.Tape.mk₂ (xs.map data ++ [marker]) (ys.map data)⟩
    r.cfg = ⟨readState 0, Turing.Tape.mk₂ [marker] ((xs.reverse++ys).map data)⟩ ∧
      r.unread = raw ∧ r.bits = [] ∧ r.steps = xs.length+2 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, program, head_nil, head_cons, marker, tape_left, advance,
        TM0StmtApply, tape_right, readCommand, Result.prepend, Result.bits, Result.steps, readState]
    | cons p ys => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, program, head_cons, marker, data, cell, tape_left, advance,
        TM0StmtApply, tape_right, readCommand, Result.prepend, Result.bits, Result.steps, readState]
  | cons p xs ih =>
    have hi := ih (p::ys)
    have hc : (Turing.Tape.mk₂ (data p :: (xs.map data ++ [marker])) (ys.map data)).head ≠ marker := by
      cases ys <;> simp [head_nil, head_cons, data, cell, marker]
    (try dsimp only at hi ⊢)
    rw [show (p::xs).length+2 = (xs.length+2)+1 by simp]
    rw [List.map_cons, List.cons_append, Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run]
    dsimp only [program]
    simp only [if_neg hc, advance, TM0StmtApply, tape_left]
    simpa [tape_left, Result.prepend, Result.bits, Result.steps, List.reverse_cons, List.map_append,
      List.append_assoc, Nat.add_comm] using! hi

/-- The width-`b` encoding of any natural number contains exactly `b` bits. -/
theorem encode_length (b v : ℕ) : (encode b v).length = b := by
  induction b generalizing v with
  | zero => rfl
  | succ b ih => simp [encode, ih]

/-- For `v < 2^b`, decoding the width-`b` encoding of `v` recovers `v`. -/
theorem encode_value (b v : ℕ) (hv : v < 2^b) : binaryValue (encode b v) = v := by
  induction b generalizing v with
  | zero =>
    have hzero : v = 0 := by simpa using! hv
    subst v
    rfl
  | succ b ih =>
    rw [encode, binaryValue, encode_length, ih _ (Nat.mod_lt _ (Nat.two_pow_pos b))]
    by_cases h : 2^b ≤ v
    · simp only [h, decide_true, ↓reduceIte]
      have ht : v < 2^b+2^b := by simpa [Nat.pow_succ, Nat.mul_two] using! hv
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : v-2^b < 2^b)]
      omega
    · simp [h, Nat.mod_eq_of_lt (by omega : v < 2^b)]

/-- Testing whether the comparison fold ends in state `2` gives the same Boolean result as
lexicographic comparison after swapping the two fields of each pair. -/
theorem compareFold_greater (xs : List (Bool × Bool)) :
    (xs.foldl compareUpdate 0 == 2) = lexLess (xs.map Prod.swap) := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    cases a <;> cases b <;> simp [List.foldl_cons, compareUpdate, lexLess, compareFold_stable, ih]

/-- The comparison fold avoids state `2` exactly when the binary value of the first fields is at
most that of the second fields. -/
theorem compareFold_le (xs : List (Bool × Bool)) :
    xs.foldl compareUpdate 0 ≠ 2 ↔ binaryValue (xs.map Prod.fst) ≤ binaryValue (xs.map Prod.snd) := by
  have h := compareFold_greater xs
  have hl := lexLess_numeric (xs.map Prod.swap)
  simp only [List.map_map, Function.comp_def] at hl
  change lexLess (xs.map Prod.swap) = true ↔
      binaryValue (xs.map Prod.snd) < binaryValue (xs.map Prod.fst) at hl
  simpa using!
      (not_congr ((show xs.foldl compareUpdate 0 = 2 ↔ lexLess (xs.map Prod.swap) = true by simpa using! congrArg (fun b => b = true) h).trans hl))

/-- Appending one bit doubles the binary value and adds one precisely when the appended bit is
true. -/
theorem binaryValue_concat (xs : List Bool) (b : Bool) :
    binaryValue (xs ++ [b]) = 2*binaryValue xs + (if b then 1 else 0) := by
  induction xs with
  | nil => cases b <;> rfl
  | cons a xs ih =>
    cases a <;> simp [binaryValue, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_comm, Nat.add_assoc]

/-- The binary value of a register's list of bits equals the natural-number value given by
`bitVecEquiv`. -/
theorem binaryValue_reg (b : ℕ) (ω : Reg b) : binaryValue (List.ofFn ω) = (bitVecEquiv b ω).val := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [List.ofFn_succ', List.concat_eq_append, binaryValue_concat, ih]
    have h : (bitVecEquiv (b+1) ω).val = (boolEquivFin2 (ω (Fin.last b))).val +
        2*(bitVecEquiv b (fun i => ω i.castSucc)).val := rfl
    rw [h]
    cases hb : ω (Fin.last b) <;> simp [boolEquivFin2, Nat.add_comm]

/-- Reading as many digits to the left as there are data cells recovers their first fields in
left-list order, independently of the remaining tape lists. -/
theorem leftDigits_word (xs : List (Bool × Bool)) (L R : List Symbol) :
    leftDigits xs.length (Turing.Tape.mk₂ (xs.map data ++ L) R) = xs.map Prod.fst := by
  induction xs generalizing R with
  | nil => rfl
  | cons p xs ih =>
    rw [List.map_cons, List.cons_append, List.length_cons, leftDigits]
    (try dsimp only)
    rw [tape_left, head_cons, ih (data p :: R)]
    rfl

/-- Overwriting with an equally long word replaces the first fields by that word and preserves
all second fields. -/
theorem overwrite_fields (ys : List (Bool × Bool)) (ω : List Bool) (h : ω.length = ys.length) :
    let out := List.zipWith (fun b p => (b,p.2)) ω ys
    out.map Prod.fst = ω ∧ out.map Prod.snd = ys.map Prod.snd := by
  induction ys generalizing ω with
  | nil => have hω : ω = [] := List.eq_nil_of_length_eq_zero h; subst ω; simp
  | cons p ys ih => cases ω with
    | nil => simp at h
    | cons b ω => simpa using! ih ω (by simpa using! h)

/-- A valid width-`b` trial returns its sampled register value exactly when that value is below
`bound`. Its observation records exactly `2*b` CPU steps and `b` random-bit reads. -/
theorem trial_observation (b bound : ℕ) (hp : 0 < bound) (hb : bound ≤ 2^b) (ω : Reg b) :
    trialObservation b (trial b bound ω) =
      (if (bitVecEquiv b ω).val < bound then some (bitVecEquiv b ω).val else none, 2*b, b) := by
  let ys := (encode b (bound-1)).map (fun t => (false,t))
  let w := List.ofFn ω
  let out := List.zipWith (fun b p => (b,p.2)) w ys
  have hlen : w.length = ys.length := by simp [ys, w, encode_length]
  have hin : input b bound = ⟨readState 0, Turing.Tape.mk₂ [marker] (ys.map data)⟩ := by
    simp [input, start, hp, hb, ys, data, readState, Function.comp_def]
  have hi := scan ys w [] 0 [marker] hlen
  have hrun : trial b bound ω = Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (w++[])
      ⟨readState 0, Turing.Tape.mk₂ [marker] (ys.map data)⟩ := by
    simp [trial, hin, ys, encode_length, w]
  rw [← hrun] at hi
  change (trial b bound ω).cfg = ⟨readState (out.foldl compareUpdate 0),
    Turing.Tape.mk₂ (out.reverse.map data ++ [marker]) []⟩ ∧ _ at hi
  obtain ⟨hc, hu, hbits, hsteps⟩ := hi
  obtain ⟨hfst, hsnd⟩ := overwrite_fields ys w hlen
  change out.map Prod.fst = w at hfst
  change out.map Prod.snd = ys.map Prod.snd at hsnd
  have hol : out.length = b := by simpa [w] using! congrArg List.length hfst
  have hout : Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b (trial b bound ω).cfg.Tape = (bitVecEquiv b ω).val := by
    rw [hc]
    dsimp only [Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output]
    have hl := leftDigits_word out.reverse [marker] []
    rw [show out.reverse.length = b by simpa using! hol] at hl
    rw [hl]
    simpa [List.map_reverse, hfst, w] using! binaryValue_reg b ω
  have hhalt := run_halt_iff program (2*b) (List.ofFn ω) (input b bound)
  change (trial b bound ω).stop = .halted ↔
      program (trial b bound ω).cfg.q (trial b bound ω).cfg.Tape.head = .halt at hhalt
  rw [hc] at hhalt
  simp only [read_rule, head_nil, readCommand] at hhalt
  have hcmp : out.foldl compareUpdate 0 ≠ 2 ↔ (bitVecEquiv b ω).val < bound := by
    rw [compareFold_le, hfst, hsnd]
    simp only [ys, List.map_map, Function.comp_def, List.map_id', w]
    rw [encode_value b (bound-1) (by omega), binaryValue_reg]
    omega
  have hh : (trial b bound ω).stop = .halted ↔ (bitVecEquiv b ω).val < bound := by
    have hh' : (trial b bound ω).stop = .halted ↔ out.foldl compareUpdate 0 ≠ 2 := by
      by_cases h : out.foldl compareUpdate 0 = 2 <;> simpa [h] using! hhalt
    exact hh'.trans hcmp
  simp only [trialObservation, hout, hbits, hsteps, hh]
  simp [ys, encode_length, w]

/-- For a valid bound, a trial is the image of the uniform law on `Fin (2^b)`, accepting
precisely the values below the bound. Every outcome records `2*b` CPU steps and `b`
random-bit reads. -/
theorem trial_law_uniform (b bound : ℕ) (hp : 0 < bound) (hb : bound ≤ 2^b) :
    trialLaw b bound = (PMF.uniformOfFintype' (Fin (2^b))).map
      (fun v => (if v.val < bound then some v.val else none, 2*b, b)) := by
  classical
  rw [trialLaw, CoinCode.block_law_uniform, PMF.map_comp]
  ext z
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype'_apply,
    Function.comp_apply, trial_observation b bound hp hb, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  exact (bitVecEquiv b).sum_comp (fun v : Fin (2^b) =>
    if z = (if v.val < bound then some v.val else none, 2*b, b) then ((2^b : ℕ) : ℝ≥0∞)⁻¹ else 0)

/-- From rejection state `2` at the right blank, the machine returns to read state `0` in
`xs.length+2` steps, restoring `xs.reverse` to the right of the marker. It consumes no
random bits and preserves `raw`. -/
theorem restart (xs : List (Bool × Bool)) (raw : List Bool) :
    let r := Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (xs.length+2) raw
      ⟨readState 2, Turing.Tape.mk₂ (xs.map data ++ [marker]) []⟩
    r.cfg = ⟨readState 0, Turing.Tape.mk₂ [marker] (xs.reverse.map data)⟩ ∧
      r.unread = raw ∧ r.bits = [] ∧ r.steps = xs.length+2 := by
  have h := rewind xs [] raw
  (try dsimp only at h ⊢)
  simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, program, readState, head_nil, readCommand, marker,
    Result.prepend, Result.bits, Result.steps] using! h

/-- A run from control state `7` exhausts exactly its allotted fuel while consuming no random
bits and leaving `raw` unread. -/
theorem invalid_run (n : ℕ) (raw : List Bool) (T : Turing.Tape Symbol) :
    let r := Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw ⟨7,T⟩
    r.stop = .fuel ∧ r.steps = n ∧ r.bits = [] ∧ r.unread = raw := by
  induction n generalizing T with
  | zero => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, program, Result.steps, Result.bits]
  | succ n ih => simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run, program, Result.prepend, Result.steps, Result.bits, advance, TM0StmtApply] using! ih (T.write T.head)

/-- For a valid bound and `v < bound`, the accepting trial outcome `(some v, 2*b, b)` has mass
`(2^b)⁻¹`. -/
theorem trial_law_accept (b bound v : ℕ) (hp : 0 < bound) (hb : bound ≤ 2^b) (hv : v < bound) :
    trialLaw b bound (some v, 2*b, b) = (2^b : ℝ≥0∞)⁻¹ := by
  classical
  rw [trial_law_uniform b bound hp hb, PMF.map_apply, tsum_fintype]
  have hvb : v < 2^b := lt_of_lt_of_le hv hb
  have he (a : Fin (2^b)) :
      ((some v, 2*b, b) = (if a.val < bound then some a.val else none, 2*b, b)) ↔ a = ⟨v,hvb⟩ := by
    by_cases ha : a.val < bound <;> simp [ha, Fin.ext_iff] <;> omega
  simp [he, PMF.uniformOfFintype'_apply]

/-- A loaded register of positive length does not start with a halting program command. -/
theorem loaded_not_halt (ys : List (Bool × Bool)) (hp : 0 < ys.length) :
    program (loaded ys).q (loaded ys).Tape.head ≠ .halt := by
  cases ys with
  | nil => simp at hp
  | cons p ys => simp [loaded, read_rule, head_cons, readCommand, cell]

/-- A word whose value exceeds the stored threshold completes one rejection cycle in `cycleSteps
ys.length` steps. The run ends fuel-exhausted in the overwritten loaded configuration,
having consumed exactly that word and preserved `raw`. -/
theorem rejected_cycle (ys : List (Bool × Bool)) (ω raw : List Bool)
    (hp : 0 < ys.length) (hlen : ω.length = ys.length)
    (hbad : binaryValue (ys.map Prod.snd) < binaryValue ω) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps ys.length) (ω++raw) (loaded ys)).observe =
      (loaded (overwrite ω ys), .fuel, raw, ω, cycleSteps ys.length) := by
  let out := overwrite ω ys
  have h0 := scan ys ω raw 0 [marker] hlen
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).cfg =
    ⟨readState (out.foldl compareUpdate 0), Turing.Tape.mk₂ (out.reverse.map data ++ [marker]) []⟩ ∧ _ at h0
  obtain ⟨hc,hu,hbits,hs⟩ := h0
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).unread = raw at hu
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).bits = ω at hbits
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).steps = 2*ys.length at hs
  obtain ⟨hfst,hsnd⟩ := overwrite_fields ys ω hlen
  change out.map Prod.fst = ω at hfst
  change out.map Prod.snd = ys.map Prod.snd at hsnd
  have hol : out.length = ys.length := by
    have h := congrArg List.length hfst
    simpa [hlen] using! h
  have hcmp : out.foldl compareUpdate 0 = 2 := by
    by_contra hne
    have he := (compareFold_le out).mp hne
    rw [hfst,hsnd] at he
    omega
  have hf : (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).stop = .fuel := by
    apply (run_fuel_iff _ _ _ _).mpr
    refine ⟨hs, ?_⟩
    rw [hc,hcmp]
    simp [read_rule,head_nil,readCommand]
  have hr := restart out.reverse raw
  (try dsimp only at hr)
  simp only [List.length_reverse,hol,List.reverse_reverse] at hr
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (ys.length+2) raw
    ⟨readState 2,Turing.Tape.mk₂ (out.reverse.map data ++ [marker]) []⟩).cfg = loaded out ∧ _ at hr
  obtain ⟨hrc,hru,hrb,hrs⟩ := hr
  have hrf : (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (ys.length+2) raw
      ⟨readState 2,Turing.Tape.mk₂ (out.reverse.map data ++ [marker]) []⟩).stop = .fuel := by
    apply (run_fuel_iff _ _ _ _).mpr
    refine ⟨hrs,?_⟩
    rw [hrc]
    exact loaded_not_halt out (by omega)
  have he := run_fuel_add_observe program (2*ys.length) (ys.length+2) (ω++raw) (loaded ys) hf
  (try dsimp only at he)
  rw [hu,hc,hcmp,hbits,hs,hrc,hrf,hru,hrb,hrs] at he
  simpa only [List.append_nil,cycleSteps,show 2*ys.length+(ys.length+2) = 3*ys.length+2 by omega] using! he
/-- The configuration at the end of a scan, with the folded comparison state and the reversed
data cells to the left of the blank head. -/
def endConfig (out : List (Bool × Bool)) : Turing.TM0.Cfg Symbol Control :=
  ⟨readState (out.foldl compareUpdate 0), Turing.Tape.mk₂ (out.reverse.map data ++ [marker]) []⟩

/-- A word at most the stored threshold halts after exactly two steps per cell, even when
additional fuel is supplied. The final configuration is `endConfig` of the overwritten
register, and only the accepted word is consumed. -/
theorem accepted_scan (ys : List (Bool × Bool)) (ω raw : List Bool) (extra : ℕ)
    (hlen : ω.length = ys.length) (hgood : binaryValue ω ≤ binaryValue (ys.map Prod.snd)) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length+extra) (ω++raw) (loaded ys)).observe =
      (endConfig (overwrite ω ys), .halted, raw, ω, 2*ys.length) := by
  have h0 := scan ys ω raw 0 [marker] hlen
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).observe.1 = endConfig (overwrite ω ys) ∧ _ at h0
  obtain ⟨hc,hu,hbits,hs⟩ := h0
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).cfg = endConfig (overwrite ω ys) at hc
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).unread = raw at hu
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).bits = ω at hbits
  change (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).steps = 2*ys.length at hs
  have hcmp : (overwrite ω ys).foldl compareUpdate 0 ≠ 2 := by
    rw [compareFold_le]
    obtain ⟨hf,ht⟩ := overwrite_fields ys ω hlen
    simpa only [overwrite,hf,ht] using! hgood
  have hh : (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (2*ys.length) (ω++raw) (loaded ys)).stop = .halted := by
    apply (run_halt_iff _ _ _ _).mpr
    rw [hc]
    simp [endConfig,read_rule,head_nil,readCommand,hcmp]
  rw [run_halted_add _ _ _ _ _ hh]
  simp only [Result.observe,hc,hh,hu,hbits,hs]

/-- Overwriting is equivalent to pairing the new word with the old register's second fields
using `List.zip`. -/
theorem overwrite_zip (ω : List Bool) (ys : List (Bool × Bool)) :
    overwrite ω ys = ω.zip (ys.map Prod.snd) := by
  induction ω generalizing ys with
  | nil => rfl
  | cons b ω ih => cases ys with
    | nil => rfl
    | cons p ys => simpa [overwrite] using! congrArg (List.cons (b,p.2)) (ih ys)
/-- Apply `overwrite` successively to each word in `words`, starting from the register `ys`. -/
def afterWords (ys : List (Bool × Bool)) (words : List (List Bool)) : List (Bool × Bool) :=
  words.foldl (fun xs w => overwrite w xs) ys

/-- Successively overwriting with words of the original register length preserves the complete
list of threshold bits. -/
theorem afterWords_threshold (ys : List (Bool × Bool)) (words : List (List Bool))
    (hlen : ∀ w ∈ words, w.length = ys.length) :
    (afterWords ys words).map Prod.snd = ys.map Prod.snd := by
  induction words generalizing ys with
  | nil => rfl
  | cons w ws ih =>
    have hw : w.length = ys.length := hlen w (by simp)
    have hs := (overwrite_fields ys w hw).2
    change (overwrite w ys).map Prod.snd = ys.map Prod.snd at hs
    have hol : (overwrite w ys).length = ys.length := by
      simpa using! congrArg List.length hs
    change (afterWords (overwrite w ys) ws).map Prod.snd = _
    rw [ih (overwrite w ys) (fun v hv => by rw [hol]; exact hlen v (by simp [hv])),hs]

/-- A sequence of fixed-width words exceeding the threshold consumes exactly one full rejection
cycle per word and ends fuel-exhausted in `loaded (afterWords ys words)`. It consumes their
concatenation and leaves `raw` unread. -/
theorem all_rejected (ys : List (Bool × Bool)) (words : List (List Bool)) (raw : List Bool)
    (hp : 0 < ys.length) (hlen : ∀ w ∈ words, w.length = ys.length)
    (hbad : ∀ w ∈ words, binaryValue (ys.map Prod.snd) < binaryValue w) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps ys.length * words.length) (words.flatten++raw) (loaded ys)).observe =
      (loaded (afterWords ys words), .fuel, raw, words.flatten, cycleSteps ys.length * words.length) := by
  induction words generalizing ys with
  | nil =>
    have hn := loaded_not_halt ys hp
    simp only [List.length_nil,Nat.mul_zero,List.flatten_nil,List.nil_append,afterWords,List.foldl_nil]
    cases hc : program (loaded ys).q (loaded ys).Tape.head with
    | halt => exact False.elim (hn hc)
    | det q s => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run,hc,Result.observe,Result.bits,Result.steps]
    | coin k => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run,hc,Result.observe,Result.bits,Result.steps]
  | cons w ws ih =>
    have hw : w.length = ys.length := hlen w (by simp)
    have ht := (overwrite_fields ys w hw).2
    change (overwrite w ys).map Prod.snd = ys.map Prod.snd at ht
    have hol : (overwrite w ys).length = ys.length := by simpa using! congrArg List.length ht
    have hi := ih (overwrite w ys) (by omega)
      (fun v hv => by rw [hol]; exact hlen v (by simp [hv]))
      (fun v hv => by rw [ht]; exact hbad v (by simp [hv]))
    rw [hol] at hi
    obtain ⟨hci,hsi,hui,hbi,hti⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp hi
    have h0 := rejected_cycle ys w (ws.flatten++raw) hp hw (hbad w (by simp))
    obtain ⟨hc,hf,hu,hb,hs⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp h0
    have he := run_fuel_add_observe program (cycleSteps ys.length) (cycleSteps ys.length*ws.length)
      (w++(ws.flatten++raw)) (loaded ys) hf
    (try dsimp only at he)
    rw [hu,hc,hb,hs,hci,hsi,hui,hbi,hti] at he
    simpa only [List.flatten_cons,List.append_assoc,List.length_cons,afterWords,List.foldl_cons,
      show cycleSteps ys.length*(ws.length+1) = cycleSteps ys.length + cycleSteps ys.length*ws.length by ring] using! he

/-- After a prefix of rejected words, the first word at most the threshold halts after one full
cycle per rejection and two steps per accepted bit. The final configuration depends on the
accepted word and original threshold, and any suffix `raw` remains unread. -/
theorem first_accept (ys : List (Bool × Bool)) (bad : List (List Bool)) (good raw : List Bool) (extra : ℕ)
    (hp : 0 < ys.length) (hlen : ∀ w ∈ bad, w.length = ys.length)
    (hbad : ∀ w ∈ bad, binaryValue (ys.map Prod.snd) < binaryValue w)
    (hgoodLen : good.length = ys.length) (hgood : binaryValue good ≤ binaryValue (ys.map Prod.snd)) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps ys.length*bad.length+2*ys.length+extra)
      (bad.flatten++good++raw) (loaded ys)).observe =
    (endConfig (overwrite good ys), .halted, raw, bad.flatten++good,
      cycleSteps ys.length*bad.length+2*ys.length) := by
  have ht := afterWords_threshold ys bad hlen
  have hol : (afterWords ys bad).length = ys.length := by simpa using! congrArg List.length ht
  have hr := all_rejected ys bad (good++raw) hp hlen hbad
  obtain ⟨hc,hf,hu,hb,hs⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp hr
  have ha := accepted_scan (afterWords ys bad) good raw extra
    (by rw [hol]; exact hgoodLen) (by rw [ht]; exact hgood)
  rw [hol] at ha
  have ho : overwrite good (afterWords ys bad) = overwrite good ys := by
    simp only [overwrite_zip,ht]
  rw [ho] at ha
  obtain ⟨hca,hha,hua,hba,hsa⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp ha
  have he := run_fuel_add_observe program (cycleSteps ys.length*bad.length) (2*ys.length+extra)
    (bad.flatten++(good++raw)) (loaded ys) hf
  (try dsimp only at he)
  rw [hu,hc,hb,hs,hca,hha,hua,hba,hsa] at he
  simpa only [List.append_assoc,Nat.add_assoc] using! he

/-- Reading the output from an end-of-scan configuration gives the binary value of its data
cells' first fields. -/
theorem endConfig_output (xs : List (Bool × Bool)) :
    Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output xs.length (endConfig xs).Tape = binaryValue (xs.map Prod.fst) := by
  have hl := leftDigits_word xs.reverse [marker] []
  simp only [List.length_reverse] at hl
  dsimp only [Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output,endConfig]
  rw [hl]
  simp only [List.map_reverse,List.reverse_reverse]

/-- The concatenation of words all of length `b` has length `b` times the number of words. -/
theorem uniform_words_length (b : ℕ) (words : List (List Bool))
    (hlen : ∀ w ∈ words, w.length = b) : words.flatten.length = b*words.length := by
  induction words with
  | nil => simp
  | cons w ws ih =>
    rw [List.flatten_cons,List.length_append,hlen w (by simp),ih (fun v hv => hlen v (by simp [hv]))]
    simp [Nat.mul_succ,Nat.add_comm]

/-- The first accepted word determines the returned binary value, while each preceding rejection
contributes a full cycle to CPU time. The number of random-bit reads is the register width
times the number of attempted words. -/
theorem first_accept_observation (ys : List (Bool × Bool)) (bad : List (List Bool))
    (good raw : List Bool) (extra : ℕ) (hp : 0 < ys.length)
    (hlen : ∀ w ∈ bad, w.length = ys.length)
    (hbad : ∀ w ∈ bad, binaryValue (ys.map Prod.snd) < binaryValue w)
    (hgoodLen : good.length = ys.length) (hgood : binaryValue good ≤ binaryValue (ys.map Prod.snd)) :
    trialObservation ys.length (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps ys.length*bad.length+2*ys.length+extra)
      (bad.flatten++good++raw) (loaded ys)) =
    (some (binaryValue good), cycleSteps ys.length*bad.length+2*ys.length, ys.length*(bad.length+1)) := by
  have hr := first_accept ys bad good raw extra hp hlen hbad hgoodLen hgood
  obtain ⟨hc,hh,hu,hb,hs⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp hr
  have hf := (overwrite_fields ys good hgoodLen).1
  change (overwrite good ys).map Prod.fst = good at hf
  have hol : (overwrite good ys).length = ys.length := by
    have hl := congrArg List.length hf
    simpa [hgoodLen] using! hl
  have ho : Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output ys.length (endConfig (overwrite good ys)).Tape = binaryValue good := by
    have h := endConfig_output (overwrite good ys)
    rw [hol,hf] at h
    exact h
  simp only [trialObservation,hh,↓reduceIte,hc,ho,hb,hs,List.length_append,
    uniform_words_length ys.length bad hlen,hgoodLen]
  simp [Nat.mul_succ,Nat.add_comm]

/-- For a positive representable bound, the input configuration is the loaded register with zero
first fields and the encoding of `bound-1` as its threshold fields. -/
theorem input_loaded (b bound : ℕ) (hp : 0 < bound) (hb : bound ≤ 2^b) :
    input b bound = loaded ((encode b (bound-1)).map (fun t => (false,t))) := by
  simp [input,loaded,start,hp,hb,Function.comp_def,readState]

/-- For positive width and a valid bound, a rejected prefix followed by an accepted word
produces its binary value with the stated exact CPU and random-bit counts. The run consumes
exactly those words and leaves the suffix `raw` unread. -/
theorem first_accept_input (b bound : ℕ) (bad : List (List Bool)) (good raw : List Bool) (extra : ℕ)
    (hbpos : 0 < b) (hp : 0 < bound) (hb : bound ≤ 2^b)
    (hlen : ∀ w ∈ bad, w.length = b) (hbad : ∀ w ∈ bad, bound ≤ binaryValue w)
    (hgoodLen : good.length = b) (hgood : binaryValue good < bound) :
    let r :=
        Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program
        (cycleSteps b*bad.length+2*b+extra) (bad.flatten++good++raw) (input b bound)
    trialObservation b r = (some (binaryValue good), cycleSteps b*bad.length+2*b, b*(bad.length+1)) ∧
      r.unread = raw ∧ r.bits = bad.flatten++good := by
  let ys := (encode b (bound-1)).map (fun t => (false,t))
  have hylen : ys.length = b := by simp [ys,encode_length]
  have ht : binaryValue (ys.map Prod.snd) = bound-1 := by
    simp only [ys,List.map_map,Function.comp_def,List.map_id']
    exact encode_value b (bound-1) (by omega)
  have hlen' : ∀ w ∈ bad, w.length = ys.length := fun w hw => by rw [hylen]; exact hlen w hw
  have hbad' : ∀ w ∈ bad, binaryValue (ys.map Prod.snd) < binaryValue w := by
    intro w hw
    rw [ht]
    have h := hbad w hw
    omega
  have hglen : good.length = ys.length := hgoodLen.trans hylen.symm
  have hgood' : binaryValue good ≤ binaryValue (ys.map Prod.snd) := by rw [ht]; omega
  have hpos : 0 < ys.length := by omega
  have hs := first_accept ys bad good raw extra hpos hlen' hbad' hglen hgood'
  have ho := first_accept_observation ys bad good raw extra hpos hlen' hbad' hglen hgood'
  rw [hylen] at hs ho
  have hi : loaded ys = input b bound := (input_loaded b bound hp hb).symm
  rw [hi] at hs ho
  obtain ⟨_,_,hu,hr,_⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp hs
  exact ⟨ho,hu,hr⟩

/-- The exact first halting time is one full cycle per rejected word plus two steps per accepted
bit. Every smaller CPU budget ends with fuel exhaustion. -/
theorem first_accept_time (ys : List (Bool × Bool)) (bad : List (List Bool)) (good raw : List Bool)
    (hp : 0 < ys.length) (hlen : ∀ w ∈ bad, w.length = ys.length)
    (hbad : ∀ w ∈ bad, binaryValue (ys.map Prod.snd) < binaryValue w)
    (hgoodLen : good.length = ys.length) (hgood : binaryValue good ≤ binaryValue (ys.map Prod.snd)) :
    let T := cycleSteps ys.length*bad.length+2*ys.length
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program T (bad.flatten++good++raw) (loaded ys)).stop = .halted ∧
      ∀ n < T, (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n (bad.flatten++good++raw) (loaded ys)).stop = .fuel := by
  have hr := first_accept ys bad good raw 0 hp hlen hbad hgoodLen hgood
  simp only [Nat.add_zero] at hr
  obtain ⟨_,hh,_,_,hs⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp hr
  exact ⟨hh, fun n hn => fuel_before _ _ n _ _ hs hn⟩

/-- For unit weights, the cumulative weight before an index is its natural-number value. -/
theorem unit_prefix {m : ℕ} (j : Fin m) : weightPrefix (fun _ : Fin m => 1) j = j.val := by
  simp only [weightPrefix,Finset.sum_const,smul_eq_mul,mul_one]
  rw [Fin.card_filter_val_lt,Nat.min_eq_right (Nat.le_of_lt j.isLt)]

/-- The unit-weight decoder returns an index `j` exactly when the decoded natural number equals
`j.val`. -/
theorem unit_decode_some {m : ℕ} (u : ℕ) (j : Fin m) :
    (weightDecodeCounted (fun _ : Fin m => 1) u).1 = some j ↔ u = j.val := by
  rw [weightDecodeCounted_some_iff,unit_prefix]
  omega

/-- The unit-weight decoder rejects a natural number exactly when it is at least `m`. -/
theorem unit_decode_none (m u : ℕ) :
    (weightDecodeCounted (fun _ : Fin m => 1) u).1 = none ↔ m ≤ u := by
  rw [weightDecodeCounted_none_iff]
  simp [weightTotal]
/-- Relates a counted sampler record to fixed-width rejected words followed, on success, by one
word encoding its returned index. Pending records consist of exactly `cap` rejected words,
while a successful record counts its rejected prefix and final word within the cap. -/
def describesWords (m b cap : ℕ) (z : SamplerRecord m) (raw : List Bool) : Prop :=
  ∃ bad : List (List Bool),
    (∀ w ∈ bad, w.length = b) ∧ (∀ w ∈ bad, m ≤ binaryValue w) ∧
    match z.1 with
    | .inl out => ∃ good, good.length = b ∧ binaryValue good = out.1.val ∧
        raw = bad.flatten++good ∧ z.2 = bad.length+1 ∧ z.2 ≤ cap
    | .inr _ => raw = bad.flatten ∧ bad.length = cap ∧ z.2 = cap

/-- A counted loop started from an already returned output immediately returns that output with
zero additional trials, for every cap. -/
theorem countedLoop_halted {m : ℕ} (b cap : ℕ) (out : Fin m × ℕ × ℕ) :
    countedLoop (fun _ : Fin m => 1) b cap (.inl out) = .ret (.inl out,0) := by
  cases cap <;> rfl

/-- Every path of a unit-weight counted loop started from a pending state satisfies
`describesWords`, including its word lengths, rejected values, and trial count. -/
theorem countedLoop_words (m b cap : ℕ) (BD : ℕ × ℕ) (z : SamplerRecord m) (raw : List Bool)
    (hz : (z,raw) ∈ (countedLoop (fun _ : Fin m => 1) b cap (.inr BD)).paths) :
    describesWords m b cap z raw := by
  rcases z with ⟨cfg,t⟩
  induction cap generalizing BD cfg t raw with
  | zero =>
    simp only [countedLoop,CoinCode.paths,List.mem_singleton,Prod.mk.injEq] at hz
    rcases hz with ⟨⟨rfl,rfl⟩,rfl⟩
    refine ⟨[],by simp,by simp,?_⟩
    simp
  | succ cap ih =>
    rw [countedLoop] at hz
    obtain ⟨ω,u,v,hblock,hv,hraw⟩ := (CoinCode.mem_paths_bind _ _ _ _).mp hz
    have hu := CoinCode.block_path_word b ω u hblock
    subst u
    rw [CoinCode.paths_bind_ret] at hv
    obtain ⟨⟨⟨cfg',t'⟩,v'⟩,hrest,he⟩ := List.mem_map.mp hv
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨⟨rfl,rfl⟩,rfl⟩
    subst raw
    cases hd : (weightDecodeCounted (fun _ : Fin m => 1) (bitVecEquiv b ω).val).1 with
    | none =>
      simp only [countedTrialResult,hd] at hrest
      have hi := ih (BD := _) (cfg := cfg') (t := t') (raw := v') hrest
      obtain ⟨bad,hlen,hbad,hshape⟩ := hi
      have hwbad : m ≤ binaryValue (List.ofFn ω) := by
        rw [binaryValue_reg]
        exact (unit_decode_none m _).mp hd
      refine ⟨List.ofFn ω :: bad, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · simp
        · exact hlen w hw
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hwbad
        · exact hbad w hw
      · cases cfg' with
        | inl out =>
          obtain ⟨good,hgl,hgv,hword,ht,hcap⟩ := hshape
          refine ⟨good,hgl,hgv,?_,?_,by omega⟩
          · simpa only [List.flatten_cons,List.append_assoc] using!
              congrArg (List.append (List.ofFn ω)) hword
          · simp only [List.length_cons]
            omega
        | inr state =>
          obtain ⟨hword,hbl,ht⟩ := hshape
          refine ⟨?_,?_,by omega⟩
          · simpa only [List.flatten_cons] using! congrArg (List.append (List.ofFn ω)) hword
          · simpa using! congrArg Nat.succ hbl
    | some j =>
      have hj := (unit_decode_some _ j).mp hd
      simp only [countedTrialResult,hd] at hrest
      rw [countedLoop_halted] at hrest
      simp only [CoinCode.paths,List.mem_singleton,Prod.mk.injEq] at hrest
      rcases hrest with ⟨⟨rfl,rfl⟩,rfl⟩
      refine ⟨[],by simp,by simp,List.ofFn ω,by simp,?_,by simp,by simp,by omega⟩
      simpa only [binaryValue_reg] using! hj

/-- Subtracting the final `b+2` rewind steps from `k+1` full cycles leaves `k` full rejection
cycles followed by a `2*b`-step accepted scan. -/
theorem cycleSteps_rebate (b k : ℕ) :
    cycleSteps b*(k+1)-(b+2) = cycleSteps b*k+2*b := by
  rw [Nat.mul_succ]
  unfold cycleSteps
  omega

/-- For positive width and a valid bound, words satisfying `describesWords` reproduce their
counted observation in a native run with the corresponding capped cycle budget. The run
consumes all supplied bits and halts precisely for a returned record. -/
theorem describesWords_native (m b cap : ℕ) (z : SamplerRecord m) (raw : List Bool)
    (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) (h : describesWords m b cap z raw) :
    let r :=
        Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) raw
        (input b m)
    trialObservation b r = countedObservation b z ∧ r.unread = [] ∧ r.bits = raw ∧
      r.stop = (match z.1 with | .inl _ => .halted | .inr _ => .fuel) := by
  rcases z with ⟨cfg,t⟩
  obtain ⟨bad,hlen,hbad,hshape⟩ := h
  (try dsimp only)
  cases cfg with
  | inl out =>
    obtain ⟨good,hgl,hgv,hword,ht,hcap⟩ := hshape
    subst raw
    change t = bad.length+1 at ht
    change t ≤ cap at hcap
    subst t
    let T := cycleSteps b*bad.length+2*b
    have hc : 2*b ≤ cycleSteps b := by unfold cycleSteps; omega
    have hmul := Nat.mul_le_mul_left (cycleSteps b) hcap
    rw [Nat.mul_succ] at hmul
    have hT : T ≤ cycleSteps b*cap := by dsimp only [T]; omega
    have hsum : T+(cycleSteps b*cap-T) = cycleSteps b*cap := by omega
    have hh := first_accept_input b m bad good [] (cycleSteps b*cap-T)
      hbpos hm hb hlen hbad hgl (by rw [hgv]; exact out.1.isLt)
    simp only [List.append_nil] at hh
    change trialObservation b
        (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (T+(cycleSteps b*cap-T)) (bad.flatten++good) (input b m)) = _ ∧ _ at hh
    rw [hsum] at hh
    refine ⟨?_,hh.2.1,hh.2.2,?_⟩
    · simpa only [countedObservation,cycleSteps_rebate,hgv] using! hh.1
    · by_contra hn
      have ho := congrArg Prod.fst hh.1
      simp [trialObservation,hn] at ho
  | inr state =>
    obtain ⟨hword,hbl,ht⟩ := hshape
    change t = cap at ht
    subst raw
    let ys := (encode b (m-1)).map (fun x => (false,x))
    have hyl : ys.length = b := by simp [ys,encode_length]
    have hyt : binaryValue (ys.map Prod.snd) = m-1 := by
      simp only [ys,List.map_map,Function.comp_def,List.map_id']
      exact encode_value b (m-1) (by omega)
    have hr := all_rejected ys bad [] (by omega)
      (fun w hw => by rw [hyl]; exact hlen w hw)
      (fun w hw => by rw [hyt]; have he := hbad w hw; omega)
    simp only [hyl,hbl,List.append_nil] at hr
    have hi : loaded ys = input b m := (input_loaded b m hm hb).symm
    rw [hi] at hr
    obtain ⟨_,hf,hu,hw,hs⟩ := (Result.observe_eq_iff _ _ _ _ _ _).mp hr
    have hread : bad.flatten.length = b*cap := by rw [uniform_words_length b bad hlen,hbl]
    refine ⟨?_,hu,hw,hf⟩
    simp [trialObservation,hf,hw,hs,countedObservation,ht,hread]

/-- Each path word of the valid positive-width unit-weight sampler realizes its counted
observation in the native tape program. All supplied bits are consumed, and the native stop
status is halted for returned records and fuel-exhausted for pending records. -/
theorem weightedSampler_native_word (b m cap : ℕ) (z : SamplerRecord m × List Bool)
    (hz : z ∈ (weightedSampler (fun _ : Fin m => 1) b cap).paths)
    (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    let r :=
        Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) z.2
        (input b m)
    trialObservation b r = countedObservation b z.1 ∧ r.unread = [] ∧ r.bits = z.2 ∧
      r.stop = (match z.1.1 with | .inl _ => .halted | .inr _ => .fuel) := by
  exact describesWords_native m b cap z.1 z.2 hbpos hm hb
    (countedLoop_words m b cap (0,0) z.1 z.2 hz)

/-- For positive width and a valid bound, running the unit-weight sampler's path law for a
capped number of cycles gives the full native execution law at that CPU budget. -/
theorem native_fullLaw_cycle (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    let p := weightedSampler (fun _ : Fin m => 1) b cap
    p.pathLaw.map (fun i => Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) (p.paths.get i).2 (input b m)) =
      NativeTape.law program (cycleSteps b*cap) (input b m) := by
  apply law_eq_pathLaw
  intro z hz
  have hh := weightedSampler_native_word b m cap z hz hbpos hm hb
  refine ⟨hh.2.1,?_⟩
  rw [hh.2.2.2]
  cases z.1.1 <;> simp

/-- For positive width and a valid bound, the native observation law at a whole-cycle CPU budget
equals `nativeCapLaw` with the corresponding cap. -/
theorem nativeLaw_cycle (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    nativeLaw b m (cycleSteps b*cap) = nativeCapLaw b m cap := by
  unfold nativeLaw nativeCapLaw
  rw [← native_fullLaw_cycle b m cap hbpos hm hb,PMF.map_comp]
  rfl

/-- For positive width and a valid bound, the capped native law is the image of the unit-weight
sampler law under `countedObservation`. -/
theorem nativeCapLaw_counted (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    nativeCapLaw b m cap = (weightedSampler (fun _ : Fin m => 1) b cap).law.map
      (fun z => countedObservation b z.1) := by
  let p := weightedSampler (fun _ : Fin m => 1) b cap
  have hf (i : Fin p.paths.length) :
      trialObservation b (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) (p.paths.get i).2 (input b m)) =
        countedObservation b (p.paths.get i).1 :=
    (weightedSampler_native_word b m cap (p.paths.get i) (List.get_mem _ _) hbpos hm hb).1
  change p.pathLaw.map _ = p.law.map _
  calc
    _ = p.pathLaw.map (fun i => countedObservation b (p.paths.get i).1) :=
      congrArg (fun f => p.pathLaw.map f) (funext hf)
    _ = (p.pathLaw.map (fun i => ((p.paths.get i).1,(p.paths.get i).2.length))).map
        (fun z => countedObservation b z.1) := by rw [PMF.map_comp]; rfl
    _ = _ := by rw [CoinCode.pathLaw_map]

/-- A counted observation has no returned value exactly when its sampler configuration has a
rejected or pending outcome. -/
theorem countedObservation_none {m : ℕ} (b : ℕ) (z : SamplerRecord m) :
    (countedObservation b z).1 = none ↔ rejectionOutcome z.1 = .inr () := by
  rcases z with ⟨cfg,t⟩
  cases cfg <;> simp [countedObservation,rejectionOutcome]

/-- A counted observation returns `j.val` exactly when its sampler configuration has returned
the index `j`. -/
theorem countedObservation_some {m : ℕ} (b : ℕ) (z : SamplerRecord m) (j : Fin m) :
    (countedObservation b z).1 = some j.val ↔ rejectionOutcome z.1 = .inl j := by
  rcases z with ⟨cfg,t⟩
  cases cfg <;> simp [countedObservation,rejectionOutcome,Fin.ext_iff]

/-- For positive width and a valid bound, the probability of no return after `cap` cycles is the
single-trial rejection mass raised to `cap`. -/
theorem nativeCapLaw_timeout (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 = none) =
      rationalRejectMass (fun _ : Fin m => 1) b ^ cap := by
  rw [nativeCapLaw_counted b m cap hbpos hm hb,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  simpa only [countedObservation_none] using! weightedSampler_timeout (fun _ : Fin m => 1) b cap
    (by simpa [weightTotal] using! hb)

/-- For positive width and a valid bound, each index below `m` has capped return probability
`1/m` times one minus the timeout probability. -/
theorem nativeCapLaw_return (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) (j : Fin m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 = some j.val) =
      (1 : ℝ≥0∞)/m * (1-rationalRejectMass (fun _ : Fin m => 1) b ^ cap) := by
  rw [nativeCapLaw_counted b m cap hbpos hm hb,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  simp only [countedObservation_some]
  simpa [weightTotal] using! weightedSampler_return (fun _ : Fin m => 1) b cap
    (by simpa [weightTotal] using! hm) (by simpa [weightTotal] using! hb) j

/-- For a valid bound, the expected number of trials used by the capped unit-weight sampler is
the finite geometric sum of rejection probabilities over `Finset.range cap`. -/
theorem source_trials_mean (b m cap : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler (fun _ : Fin m => 1) b cap).law
      (fun z => (z.1.2 : ℝ≥0∞)) =
      ∑ k ∈ Finset.range cap, rationalRejectMass (fun _ : Fin m => 1) b ^ k := by
  rw [weightedSampler_law,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  exact (rational_finite_three_resource_expectations m (fun _ : Fin m => 1) b cap
    (by simpa [weightTotal] using! hm) (by simpa [weightTotal] using! hb)).1

/-- The CPU count in any counted observation is at most the full cycle cost times its recorded
trial count. -/
theorem countedObservation_time_le {m : ℕ} (b : ℕ) (z : SamplerRecord m) :
    (countedObservation b z).2.1 ≤ cycleSteps b*z.2 := by
  rcases z with ⟨cfg,t⟩
  cases cfg with
  | inl out => exact Nat.sub_le _ _
  | inr state => exact le_rfl

/-- For positive width and a valid bound, expected capped native CPU steps are at most the cycle
cost times the finite geometric sum of rejection probabilities. -/
theorem nativeCapLaw_time_le (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞)) ≤
      (cycleSteps b : ℝ≥0∞) * ∑ k ∈ Finset.range cap, rationalRejectMass (fun _ : Fin m => 1) b ^ k := by
  rw [nativeCapLaw_counted b m cap hbpos hm hb,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler (fun _ : Fin m => 1) b cap).law
        (fun z => (cycleSteps b : ℝ≥0∞) * (z.1.2 : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro z
      apply mul_le_mul_right
      (try dsimp only)
      exact_mod_cast countedObservation_time_le b z.1
    _ = _ := by rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul,source_trials_mean b m cap hm hb]

/-- A counted observation records exactly `b` random-bit reads per recorded trial. -/
theorem countedObservation_reads {m : ℕ} (b : ℕ) (z : SamplerRecord m) :
    (countedObservation b z).2.2 = b*z.2 := by
  rcases z with ⟨cfg,t⟩
  cases cfg <;> rfl

/-- For positive width and a valid bound, expected capped random-bit reads equal `b` times the
finite geometric sum of rejection probabilities. -/
theorem nativeCapLaw_reads_mean (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.2 : ℝ≥0∞)) =
      (b : ℝ≥0∞) * ∑ k ∈ Finset.range cap, rationalRejectMass (fun _ : Fin m => 1) b ^ k := by
  rw [nativeCapLaw_counted b m cap hbpos hm hb,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp only [countedObservation_reads,Nat.cast_mul]
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul,source_trials_mean b m cap hm hb]

/-- For positive width and a valid bound, every capped expected CPU cost is bounded by
`cycleSteps b` divided by one minus the single-trial rejection mass. -/
theorem nativeCapLaw_time_uniform_bound (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞)) ≤
      (cycleSteps b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) := by
  calc
    _ ≤ (cycleSteps b : ℝ≥0∞) * ∑ k ∈ Finset.range cap,
        rationalRejectMass (fun _ : Fin m => 1) b ^ k := nativeCapLaw_time_le b m cap hbpos hm hb
    _ ≤ (cycleSteps b : ℝ≥0∞) * ∑' k : ℕ,
        rationalRejectMass (fun _ : Fin m => 1) b ^ k :=
      mul_le_mul_right (ENNReal.sum_le_tsum (Finset.range cap)) _
    _ = _ := by rw [ENNReal.tsum_geometric,div_eq_mul_inv]

/-- For positive width and a valid bound, the supremum of expected capped CPU costs over all
caps is finite. -/
theorem nativeCapLaw_time_sup_finite (b m : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨆ cap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞))) < ⊤ := by
  have hfin := (weightedSampler_expected_reads_limit (fun _ : Fin m => 1) b
    (by simpa [weightTotal] using! hm) (by simpa [weightTotal] using! hb)).2
  have hbn : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hbpos
  have hden : 1-rationalRejectMass (fun _ : Fin m => 1) b ≠ 0 := by
    intro hz
    simp [hz,ENNReal.div_zero hbn] at hfin
  exact lt_of_le_of_lt (iSup_le fun cap => nativeCapLaw_time_uniform_bound b m cap hbpos hm hb)
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) hden)

/-- For positive width and a valid bound, the capped probability of no returned value tends to
zero as the cap tends to infinity. -/
theorem nativeCapLaw_timeout_tendsto_zero (b m : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Filter.Tendsto (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 = none))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hh := weightedSampler_timeout_tendsto_zero (fun _ : Fin m => 1) b
    (by simpa [weightTotal] using! hm) (by simpa [weightTotal] using! hb)
  simp_rw [weightedSampler_timeout (fun _ : Fin m => 1) b _ (by simpa [weightTotal] using! hb)] at hh
  simp_rw [nativeCapLaw_timeout b m _ hbpos hm hb]
  exact hh

/-- With zero width and bound one, every capped native law returns zero immediately with zero
CPU steps and zero random-bit reads. -/
theorem nativeCapLaw_zero_width (cap : ℕ) : nativeCapLaw 0 1 cap = PMF.pure (some 0,0,0) := by
  have hr (raw : List Bool) :
      trialObservation 0 (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps 0*cap) raw (input 0 1)) = (some 0,0,0) := by
    have he := run_halted_add program 0 (cycleSteps 0*cap) raw (input 0 1) (by rfl)
    simp only [Nat.zero_add] at he
    rw [he]
    rfl
  simp only [nativeCapLaw,hr]
  exact PMF.map_const _ _

/-- An invalid bound gives a deterministic capped observation with no return, the full allotted
cycle budget as CPU time, and zero random-bit reads. -/
theorem nativeCapLaw_invalid (b m cap : ℕ) (hbad : ¬ (0 < m ∧ m ≤ 2^b)) :
    nativeCapLaw b m cap = PMF.pure (none,cycleSteps b*cap,0) := by
  have hr (raw : List Bool) :
      trialObservation b (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) raw (input b m)) = (none,cycleSteps b*cap,0) := by
    have hi : input b m = ⟨7,(input b m).Tape⟩ := by simp [input,start,hbad]
    have h := invalid_run (cycleSteps b*cap) raw (input b m).Tape
    rw [← hi] at h
    simp only [trialObservation,h.1,h.2.1,h.2.2.1,List.length_nil,reduceCtorEq,↓reduceIte]
  simp only [nativeCapLaw,hr]
  exact PMF.map_const _ _

/-- With zero width and bound one, every CPU-budgeted native law returns zero immediately with
no CPU steps or random-bit reads. -/
theorem nativeLaw_zero_width (budget : ℕ) : nativeLaw 0 1 budget = PMF.pure (some 0,0,0) := by
  have he := run_halted_add program 0 budget [] (input 0 1) (by rfl)
  simp only [Nat.zero_add] at he
  have hs :
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program budget [] (input 0 1)).stop ≠ .needBits := by rw [he]; decide +kernel
  rw [nativeLaw,law_eq_pure_of_run_nil program budget (input 0 1) hs,PMF.pure_map,he]
  rfl

/-- For an invalid bound, every CPU-budgeted law deterministically records no return, the entire
CPU budget, and zero random-bit reads. -/
theorem nativeLaw_invalid (b m budget : ℕ) (hbad : ¬ (0 < m ∧ m ≤ 2^b)) :
    nativeLaw b m budget = PMF.pure (none,budget,0) := by
  have hi : input b m = ⟨7,(input b m).Tape⟩ := by simp [input,start,hbad]
  have hr := invalid_run budget [] (input b m).Tape
  rw [← hi] at hr
  have hs :
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program budget [] (input b m)).stop ≠ .needBits := by simp [hr.1]
  rw [nativeLaw,law_eq_pure_of_run_nil program budget (input b m) hs,PMF.pure_map]
  simp [trialObservation,hr.1,hr.2.1,hr.2.2.1]

/-- At every whole-cycle CPU budget, the native observation law equals the corresponding capped
law, including zero-width and invalid inputs. -/
theorem nativeLaw_cycle_all (b m cap : ℕ) :
    nativeLaw b m (cycleSteps b*cap) = nativeCapLaw b m cap := by
  by_cases hv : 0 < m ∧ m ≤ 2^b
  · cases b with
    | zero =>
      have hm : m = 1 := by norm_num at hv; omega
      subst m
      rw [nativeLaw_zero_width,nativeCapLaw_zero_width]
    | succ b => exact nativeLaw_cycle (b+1) m cap (by omega) hv.1 hv.2
  · rw [nativeLaw_invalid b m _ hv,nativeCapLaw_invalid b m cap hv]

/-- For every positive representable bound, including the zero-width case, the supremum of
expected capped CPU costs is finite. -/
theorem nativeCapLaw_time_sup_finite_all (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨆ cap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞))) < ⊤ := by
  cases b with
  | zero =>
    have hm1 : m = 1 := by norm_num at hb; omega
    subst m
    simp [nativeCapLaw_zero_width]
  | succ b => exact nativeCapLaw_time_sup_finite (b+1) m (Nat.succ_pos _) hm hb

/-- With bound zero, the supremum of expected capped CPU costs is infinite. -/
theorem nativeCapLaw_zero_bound_time_sup (b : ℕ) :
    (⨆ cap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b 0 cap) (fun z => (z.2.1 : ℝ≥0∞))) = ⊤ := by
  apply eq_top_iff.mpr
  calc
    ⊤ = ⨆ cap : ℕ, (cap : ℝ≥0∞) := ENNReal.iSup_natCast.symm
    _ ≤ _ := by
      apply iSup_mono
      intro cap
      rw [nativeCapLaw_invalid b 0 cap (by omega),Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      change (cap : ℝ≥0∞) ≤ ((cycleSteps b*cap : ℕ) : ℝ≥0∞)
      have hc : 1 ≤ cycleSteps b := by unfold cycleSteps; omega
      have hn : cap ≤ cycleSteps b*cap := by simpa using! Nat.mul_le_mul_right cap hc
      exact_mod_cast hn

/-- With bound zero, the expected number of random-bit reads is zero for every width and cap. -/
theorem nativeCapLaw_zero_bound_reads (b cap : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b 0 cap) (fun z => (z.2.2 : ℝ≥0∞)) = 0 := by
  rw [nativeCapLaw_invalid b 0 cap (by omega),Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  simp

/-- For a record described by its input words, adding a rebate of `b+2` steps on success to the
observed CPU count gives the full cycle cost times its trial count. -/
theorem countedObservation_clock_identity (m b cap : ℕ) (z : SamplerRecord m) (raw : List Bool)
    (h : describesWords m b cap z raw) :
    (countedObservation b z).2.1 + (if (countedObservation b z).1 = none then 0 else b+2) =
      cycleSteps b*z.2 := by
  rcases z with ⟨cfg,t⟩
  cases cfg with
  | inr state => simp [countedObservation]
  | inl out =>
    obtain ⟨bad,_,_,good,_,_,_,ht,_⟩ := h
    change t = bad.length+1 at ht
    subst t
    simp only [countedObservation,reduceCtorEq,↓reduceIte]
    apply Nat.sub_add_cancel
    have hc : b+2 ≤ cycleSteps b := by unfold cycleSteps; omega
    have hk := Nat.mul_le_mul_left (cycleSteps b) (Nat.succ_le_succ (Nat.zero_le bad.length))
    simp only [Nat.mul_one] at hk
    exact le_trans hc hk

/-- For positive width and a valid bound, expected capped CPU time plus the expected
successful-run rebate equals the cycle cost times the finite geometric sum of rejection
probabilities. -/
theorem nativeCapLaw_clock_mean (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞)) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z =>
        ((if z.1 = none then 0 else b+2 : ℕ) : ℝ≥0∞)) =
    (cycleSteps b : ℝ≥0∞)*∑ k ∈ Finset.range cap, rationalRejectMass (fun _ : Fin m => 1) b ^ k := by
  classical
  let p := weightedSampler (fun _ : Fin m => 1) b cap
  let F : (SamplerRecord m × ℕ) → ℝ≥0∞ := fun z =>
    ((countedObservation b z.1).2.1 : ℝ≥0∞) +
      ((if (countedObservation b z.1).1 = none then 0 else b+2 : ℕ) : ℝ≥0∞)
  have hpoint (i : Fin p.paths.length) :
      F ((p.paths.get i).1,(p.paths.get i).2.length) =
        (cycleSteps b : ℝ≥0∞)*((p.paths.get i).1.2 : ℝ≥0∞) := by
    have hw :=
        countedLoop_words m b cap (0,0) (p.paths.get i).1 (p.paths.get i).2 (List.get_mem _ _)
    have hn := countedObservation_clock_identity m b cap _ _ hw
    simpa only [F,Nat.cast_add,Nat.cast_mul] using! congrArg (fun n : ℕ => (n : ℝ≥0∞)) hn
  have htrial : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.pathLaw (fun i => ((p.paths.get i).1.2 : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.law (fun z => (z.1.2 : ℝ≥0∞)) := by
    rw [← CoinCode.pathLaw_map p,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.law F := by
      rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,nativeCapLaw_counted b m cap hbpos hm hb,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.pathLaw (fun i => F ((p.paths.get i).1,(p.paths.get i).2.length)) := by
      rw [← CoinCode.pathLaw_map p,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.pathLaw
        (fun i => (cycleSteps b : ℝ≥0∞)*((p.paths.get i).1.2 : ℝ≥0∞)) := by
      apply congrArg (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.pathLaw)
      funext i
      exact hpoint i
    _ = (cycleSteps b : ℝ≥0∞)*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.law (fun z => (z.1.2 : ℝ≥0∞)) := by
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul,htrial]
    _ = _ := by rw [source_trials_mean b m cap hm hb]

/-- For positive width and a valid bound, the capped probability of returning any value is one
minus the single-trial rejection mass raised to the cap. -/
theorem nativeCapLaw_return_total (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 ≠ none) =
      1-rationalRejectMass (fun _ : Fin m => 1) b ^ cap := by
  classical
  have hsum : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 ≠ none) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 = none) = 1 := by
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
    calc
      _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun _ => 1) := by
        apply congrArg
            (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap))
        funext z
        by_cases hz : z.1 = none <;> simp [hz]
      _ = _ := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const _ _
  have hn : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 = none) ≠ ⊤ := by
    intro ht
    rw [ht] at hsum
    simp at hsum
  have hh := ENNReal.eq_sub_of_add_eq hn hsum
  rwa [nativeCapLaw_timeout b m cap hbpos hm hb] at hh

/-- For positive width and a valid bound, the expected successful-run rebate is `b+2` times the
probability of returning by the cap. -/
theorem nativeCapLaw_rebate_mean (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z =>
      ((if z.1 = none then 0 else b+2 : ℕ) : ℝ≥0∞)) =
      ((b+2 : ℕ) : ℝ≥0∞)*(1-rationalRejectMass (fun _ : Fin m => 1) b ^ cap) := by
  rw [← nativeCapLaw_return_total b m cap hbpos hm hb]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  apply congrArg
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap))
  funext z
  by_cases hz : z.1 = none <;> simp [hz]

/-- For positive width and a valid bound, expected capped CPU steps equal the cycle cost times
the finite geometric sum, minus `b+2` times the probability of returning by the cap. -/
theorem nativeCapLaw_time_exact (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞)) =
      (cycleSteps b : ℝ≥0∞)*(∑ k ∈ Finset.range cap, rationalRejectMass (fun _ : Fin m => 1) b ^ k) -
      ((b+2 : ℕ) : ℝ≥0∞)*(1-rationalRejectMass (fun _ : Fin m => 1) b ^ cap) := by
  have hh := nativeCapLaw_clock_mean b m cap hbpos hm hb
  rw [nativeCapLaw_rebate_mean b m cap hbpos hm hb] at hh
  have hle : ((b+2 : ℕ) : ℝ≥0∞)*(1-rationalRejectMass (fun _ : Fin m => 1) b ^ cap) ≤
      ((b+2 : ℕ) : ℝ≥0∞) := by
    calc
      _ ≤ ((b+2 : ℕ) : ℝ≥0∞)*1 := mul_le_mul_right tsub_le_self _
      _ = _ := mul_one _
  exact ENNReal.eq_sub_of_add_eq (ne_of_lt (lt_of_le_of_lt hle (by finiteness))) hh

/-- For `m > 0`, choosing width `Nat.clog 2 m` bounds expected capped CPU steps by `6*Nat.clog 2
m+4`, uniformly in the cap. -/
theorem nativeCapLaw_effective_time_bound (m cap : ℕ) (hm : 0 < m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw (Nat.clog 2 m) m cap) (fun z => (z.2.1 : ℝ≥0∞)) ≤
      ((6*Nat.clog 2 m+4 : ℕ) : ℝ≥0∞) := by
  by_cases hm1 : m = 1
  · subst m
    simp [nativeCapLaw_zero_width]
  · have hm2 : 1 < m := by omega
    have hbpos : 0 < Nat.clog 2 m := Nat.clog_pos (by decide) hm2
    have hcut := finite_coin_effective_cutoff m cap hm
    have hq : rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ≤ 1/2 := by
      simpa [rationalRejectMass,weightTotal] using! hcut.2.1
    have hsum : (∑ k ∈ Finset.range cap,
        rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)^k) ≤ 2 := by
      calc
        _ ≤ ∑ k ∈ Finset.range cap, (1/2 : ℝ≥0∞)^k :=
          Finset.sum_le_sum fun _ _ => ENNReal.pow_le_pow_left hq
        _ ≤ ∑' k : ℕ, (1/2 : ℝ≥0∞)^k := ENNReal.sum_le_tsum _
        _ = 2 := by norm_num [ENNReal.tsum_geometric]
    calc
      _ ≤ (cycleSteps (Nat.clog 2 m) : ℝ≥0∞) * ∑ k ∈ Finset.range cap,
          rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)^k :=
        nativeCapLaw_time_le _ _ _ hbpos hm hcut.1
      _ ≤ (cycleSteps (Nat.clog 2 m) : ℝ≥0∞)*2 := mul_le_mul_right hsum _
      _ = _ := by
        norm_num [cycleSteps,Nat.cast_add,Nat.cast_mul]
        ring

/-- Expected CPU steps are monotone in the CPU budget for every width and bound. -/
theorem nativeLaw_time_mono (b m : ℕ) : Monotone (fun n =>
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞))) := by
  intro n N hN
  simpa only [nativeLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,trialObservation] using!
    law_steps_mean_mono program (input b m) hN

/-- Expected random-bit reads are monotone in the CPU budget for every width and bound. -/
theorem nativeLaw_reads_mono (b m : ℕ) : Monotone (fun n =>
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.2 : ℝ≥0∞))) := by
  intro n N hN
  simpa only [nativeLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,trialObservation] using!
    law_reads_mean_mono program (input b m) hN

/-- The probability of observing no return equals the probability that the underlying native
execution stops by fuel exhaustion. -/
theorem nativeLaw_timeout_eq_fuel (b m n : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = none) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (NativeTape.law program n (input b m)) (fun r => r.stop = .fuel) := by
  classical
  rw [nativeLaw,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  apply expectation_congr_support
  intro r hr
  have hn := (law_support_run program n (input b m) r hr).2.2
  cases hs : r.stop <;> simp_all [trialObservation]

/-- The probability of observing no return is antitone in the CPU budget. -/
theorem nativeLaw_timeout_antitone (b m : ℕ) :
    Antitone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = none)) := by
  intro n N hN
  simpa only [nativeLaw_timeout_eq_fuel] using! law_fuel_antitone program (input b m) hN

/-- The supremum of expected CPU steps over all CPU budgets equals the supremum over capped
whole-cycle budgets. -/
theorem nativeLaw_time_sup_cofinal (b m : ℕ) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞))) =
      ⨆ cap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞)) := by
  rw [iSup_mul_budget _ (nativeLaw_time_mono b m) (cycleSteps b) (by simp [cycleSteps])]
  simp only [nativeLaw_cycle_all]

/-- The supremum of expected random-bit reads over all CPU budgets equals the supremum over
capped whole-cycle budgets. -/
theorem nativeLaw_reads_sup_cofinal (b m : ℕ) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.2 : ℝ≥0∞))) =
      ⨆ cap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.2 : ℝ≥0∞)) := by
  rw [iSup_mul_budget _ (nativeLaw_reads_mono b m) (cycleSteps b) (by simp [cycleSteps])]
  simp only [nativeLaw_cycle_all]

/-- For a positive representable bound, the supremum of expected CPU steps over all CPU budgets
is finite. -/
theorem nativeLaw_time_sup_finite (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞))) < ⊤ := by
  rw [nativeLaw_time_sup_cofinal]
  exact nativeCapLaw_time_sup_finite_all b m hm hb

/-- For `m > 0`, width `Nat.clog 2 m` bounds expected native CPU steps by `6*Nat.clog 2 m+4` for
every CPU budget. -/
theorem nativeLaw_effective_time_bound (m budget : ℕ) (hm : 0 < m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw (Nat.clog 2 m) m budget) (fun z => (z.2.1 : ℝ≥0∞)) ≤
      6*(Nat.clog 2 m : ℝ≥0∞)+4 := by
  have hn : budget ≤ cycleSteps (Nat.clog 2 m)*budget := by
    simpa using!
        Nat.mul_le_mul_right budget (show 1 ≤ cycleSteps (Nat.clog 2 m) by simp [cycleSteps])
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw (Nat.clog 2 m) m (cycleSteps (Nat.clog 2 m)*budget))
        (fun z => (z.2.1 : ℝ≥0∞)) := nativeLaw_time_mono _ _ hn
    _ = _ := by rw [nativeLaw_cycle_all]
    _ ≤ _ := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using!
          nativeCapLaw_effective_time_bound m budget hm

/-- For a positive representable bound, the infimum over CPU budgets of the probability of no
return is zero. -/
theorem nativeLaw_timeout_inf_zero (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨅ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = none)) = 0 := by
  rw [iInf_mul_budget _ (nativeLaw_timeout_antitone b m) (cycleSteps b) (by simp [cycleSteps])]
  simp only [nativeLaw_cycle_all]
  apply iInf_eq_of_tendsto
  · intro n N hN
    have hn := nativeLaw_timeout_antitone b m (Nat.mul_le_mul_left (cycleSteps b) hN)
    simpa only [nativeLaw_cycle_all] using! hn
  · cases b with
    | zero =>
      have hm1 : m = 1 := by norm_num at hb; omega
      subst m
      simp [nativeCapLaw_zero_width,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
    | succ b => exact nativeCapLaw_timeout_tendsto_zero (b+1) m (by omega) hm hb

/-- For a positive representable bound, the probability of no return tends to zero as the CPU
budget tends to infinity. -/
theorem nativeLaw_timeout_tendsto_zero (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Filter.Tendsto (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = none))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hh := tendsto_atTop_iInf (nativeLaw_timeout_antitone b m)
  rwa [nativeLaw_timeout_inf_zero b m hm hb] at hh

/-- For `0 < m ≤ 2^b`, the supremum of expected random-bit reads over CPU budgets is `b / (1 -
rationalRejectMass (fun _ : Fin m => 1) b)`. -/
theorem nativeLaw_reads_sup (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.2 : ℝ≥0∞))) =
      (b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) := by
  cases b with
  | zero =>
    have hm1 : m = 1 := by norm_num at hb; omega
    subst m
    simp [nativeLaw_zero_width]
  | succ b =>
    rw [nativeLaw_reads_sup_cofinal]
    apply iSup_eq_of_tendsto
    · intro n N hN
      have hh := nativeLaw_reads_mono (b+1) m (Nat.mul_le_mul_left (cycleSteps (b+1)) hN)
      simpa only [nativeLaw_cycle_all] using! hh
    · have hw : 0 < weightTotal (fun _ : Fin m => 1) := by simpa [weightTotal] using! hm
      have hcap : weightTotal (fun _ : Fin m => 1) ≤ 2^(b+1) := by simpa [weightTotal] using! hb
      have heq : (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw (b+1) m cap) (fun z => (z.2.2 : ℝ≥0∞))) =
          (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler (fun _ : Fin m => 1) (b+1) cap).law) := by
        funext cap
        rw [nativeCapLaw_reads_mean (b+1) m cap (by omega) hm hb,
          (weightedSampler_expectations (fun _ : Fin m => 1) (b+1) cap hw hcap).1]
      rw [heq]
      exact (weightedSampler_expected_reads_limit (fun _ : Fin m => 1) (b+1) hw hcap).1

/-- For a positive representable bound, expected random-bit reads converge to `b / (1 -
rationalRejectMass (fun _ : Fin m => 1) b)` as the CPU budget grows. -/
theorem nativeLaw_reads_tendsto (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Filter.Tendsto (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.2 : ℝ≥0∞)))
      Filter.atTop (nhds ((b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b))) := by
  have hh := tendsto_atTop_iSup (nativeLaw_reads_mono b m)
  rwa [nativeLaw_reads_sup b m hm hb] at hh

/-- For a positive representable bound, the supremum of expected random-bit reads over all CPU
budgets is finite. -/
theorem nativeLaw_reads_sup_finite (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.2 : ℝ≥0∞))) < ⊤ := by
  rw [nativeLaw_reads_sup b m hm hb]
  exact (weightedSampler_expected_reads_limit (fun _ : Fin m => 1) b
    (by simpa [weightTotal] using! hm) (by simpa [weightTotal] using! hb)).2

/-- For positive width and a valid bound, expected capped CPU steps converge to `cycleSteps b /
(1 - rationalRejectMass (fun _ : Fin m => 1) b) - (b+2)`. -/
theorem nativeCapLaw_time_tendsto (b m : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Filter.Tendsto (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞)))
      Filter.atTop (nhds ((cycleSteps b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) - (b+2 : ℝ≥0∞))) := by
  let q := rationalRejectMass (fun _ : Fin m => 1) b
  have hseries : Filter.Tendsto (fun cap => ∑ k ∈ Finset.range cap, q^k)
      Filter.atTop (nhds ((1-q)⁻¹)) := by
    simpa only [ENNReal.tsum_geometric] using! ENNReal.tendsto_nat_tsum (fun k : ℕ => q^k)
  have hpow : Filter.Tendsto (fun cap => q^cap) Filter.atTop (nhds 0) := by
    have hh := nativeCapLaw_timeout_tendsto_zero b m hbpos hm hb
    simpa only [nativeCapLaw_timeout b m _ hbpos hm hb] using! hh
  have hleft := ENNReal.Tendsto.const_mul (a := (cycleSteps b : ℝ≥0∞)) hseries
    (Or.inr (ENNReal.natCast_ne_top _))
  have hrebate : Filter.Tendsto (fun cap => (b+2 : ℝ≥0∞)*(1-q^cap))
      Filter.atTop (nhds (b+2 : ℝ≥0∞)) := by
    have hh := ENNReal.Tendsto.const_mul (a := (b+2 : ℝ≥0∞))
      (ENNReal.Tendsto.sub (ma := fun _ : ℕ => (1 : ℝ≥0∞)) tendsto_const_nhds hpow
        (Or.inl ENNReal.one_ne_top)) (Or.inr (by finiteness))
    simpa using! hh
  have hh := ENNReal.Tendsto.sub hleft hrebate (Or.inr (by finiteness))
  have heq : (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.1 : ℝ≥0∞))) =
      (fun cap => (cycleSteps b : ℝ≥0∞) * ∑ k ∈ Finset.range cap, q^k - (b+2 : ℝ≥0∞)*(1-q^cap)) := by
    funext cap
    simpa only [Nat.cast_add,Nat.cast_ofNat] using! nativeCapLaw_time_exact b m cap hbpos hm hb
  rw [heq]
  simpa only [div_eq_mul_inv] using! hh

/-- For a positive representable bound, the supremum of expected CPU steps over all budgets is
`cycleSteps b / (1 - rationalRejectMass (fun _ : Fin m => 1) b) - (b+2)`. -/
theorem nativeLaw_time_sup (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞))) =
      (cycleSteps b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) - (b+2 : ℝ≥0∞) := by
  cases b with
  | zero =>
    have hm1 : m = 1 := by norm_num at hb; omega
    subst m
    norm_num [nativeLaw_zero_width,cycleSteps,rationalRejectMass,coinRejectMass,weightTotal]
  | succ b =>
    rw [nativeLaw_time_sup_cofinal]
    apply iSup_eq_of_tendsto
    · intro n N hN
      have hh := nativeLaw_time_mono (b+1) m (Nat.mul_le_mul_left (cycleSteps (b+1)) hN)
      simpa only [nativeLaw_cycle_all] using! hh
    · exact nativeCapLaw_time_tendsto (b+1) m (by omega) hm hb

/-- For a positive representable bound, expected CPU steps converge to `cycleSteps b / (1 -
rationalRejectMass (fun _ : Fin m => 1) b) - (b+2)` as the CPU budget grows. -/
theorem nativeLaw_time_tendsto (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Filter.Tendsto (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞)))
      Filter.atTop (nhds ((cycleSteps b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) - (b+2 : ℝ≥0∞))) := by
  have hh := tendsto_atTop_iSup (nativeLaw_time_mono b m)
  rwa [nativeLaw_time_sup b m hm hb] at hh

/-- For an invalid bound, the supremum of expected CPU steps over all CPU budgets is infinite. -/
theorem nativeLaw_invalid_time_sup (b m : ℕ) (hbad : ¬ (0 < m ∧ m ≤ 2^b)) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞))) = ⊤ := by
  simp only [nativeLaw_invalid b m _ hbad,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  exact ENNReal.iSup_natCast

/-- For an invalid bound, the probability of no return is one for every CPU budget. -/
theorem nativeLaw_invalid_timeout (b m budget : ℕ) (hbad : ¬ (0 < m ∧ m ≤ 2^b)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m budget) (fun z => z.1 = none) = 1 := by
  simp [nativeLaw_invalid b m budget hbad,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]

/-- The terminal law of the tape sampler, recording a returned value, CPU steps, and consumed
random bits in `some`, and nontermination in `none`. -/
noncomputable def nativeTerminalLaw (b m : ℕ) : PMF (Option (ℕ × ℕ × ℕ)) :=
  (terminalLaw program (input b m)).map fun z => z.map (fun r => (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length))

/-- For a positive representable bound, the native tape sampler has zero nontermination mass. -/
theorem native_never_zero (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    NativeTape.neverMass program (input b m) = 0 := by
  rw [neverMass_eq_iInf_fuel]
  simp only [← nativeLaw_timeout_eq_fuel]
  exact nativeLaw_timeout_inf_zero b m hm hb

/-- The mass assigned to `none` by the terminal observation law equals the underlying program's
nontermination mass. -/
theorem nativeTerminalLaw_none (b m : ℕ) :
    nativeTerminalLaw b m none = NativeTape.neverMass program (input b m) := by
  classical
  rw [nativeTerminalLaw,PMF.map_apply,tsum_eq_single none]
  · simp
  · intro z hz
    cases z with
    | none => exact False.elim (hz rfl)
    | some r => simp

/-- For a positive representable bound, the terminal observation law assigns zero mass to
`none`. -/
theorem nativeTerminalLaw_none_zero (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    nativeTerminalLaw b m none = 0 := by rw [nativeTerminalLaw_none,native_never_zero b m hm hb]

/-- The probability of returning `j` within a CPU budget equals the probability that the
underlying run has halted with tape output `j`. -/
theorem nativeLaw_return_eq_halted (b m n j : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = some j) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (NativeTape.law program n (input b m))
        (fun r => r.stop = .halted ∧ Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape = j) := by
  classical
  rw [nativeLaw,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro r
  cases hs : r.stop <;> simp [trialObservation,hs]

/-- For each fixed value, its probability of being returned is monotone in the CPU budget. -/
theorem nativeLaw_return_mono (b m j : ℕ) :
    Monotone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = some j)) := by
  intro n N hN
  simpa only [nativeLaw_return_eq_halted] using! law_halted_event_mono program (input b m)
    (fun cfg => Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b cfg.Tape = j) hN

/-- For a positive representable bound, the supremum over CPU budgets of the probability of
returning any fixed `j : Fin m` is `1/m`. -/
theorem nativeLaw_return_sup (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) (j : Fin m) :
    (⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeLaw b m n) (fun z => z.1 = some j.val)) = 1/(m : ℝ≥0∞) := by
  cases b with
  | zero =>
    have hm1 : m = 1 := by norm_num at hb; omega
    subst m
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [nativeLaw_zero_width,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  | succ b =>
    rw [iSup_mul_budget _ (nativeLaw_return_mono (b+1) m j.val) (cycleSteps (b+1)) (by simp [cycleSteps])]
    simp only [nativeLaw_cycle_all]
    apply iSup_eq_of_tendsto
    · intro n N hN
      have hh := nativeLaw_return_mono (b+1) m j.val (Nat.mul_le_mul_left (cycleSteps (b+1)) hN)
      simpa only [nativeLaw_cycle_all] using! hh
    · have hpow := nativeCapLaw_timeout_tendsto_zero (b+1) m (by omega) hm hb
      simp only [nativeCapLaw_timeout (b+1) m _ (by omega) hm hb] at hpow
      simp only [nativeCapLaw_return (b+1) m _ (by omega) hm hb j]
      have hh := ENNReal.Tendsto.const_mul (a := (1/(m : ℝ≥0∞)))
        (ENNReal.Tendsto.sub (ma := fun _ : ℕ => (1 : ℝ≥0∞)) tendsto_const_nhds hpow
          (Or.inl ENNReal.one_ne_top)) (Or.inr (ENNReal.div_lt_top ENNReal.one_ne_top (by exact_mod_cast hm.ne')).ne)
      simpa using! hh

/-- For a positive representable bound, each index below `m` has terminal return probability
`1/m`. -/
theorem nativeTerminalLaw_return (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) (j : Fin m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeTerminalLaw b m) (fun z => z.map Prod.fst = some j.val) = 1/(m : ℝ≥0∞) := by
  classical
  rw [nativeTerminalLaw,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  calc
    _ = ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (NativeTape.law program n (input b m))
        (fun r => r.stop = .halted ∧ Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape = j.val) := by
      have hh :=
          terminalLaw_event_some program (input b m)
          (fun r => Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape = j.val)
      convert! hh using 1
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
      intro z
      cases z <;> simp
    _ = _ := by simp only [← nativeLaw_return_eq_halted]; exact nativeLaw_return_sup b m hm hb j

/-- For nonzero `m ≤ 2^b`, projecting the terminal law to its optional output gives the uniform
law on the natural-number values of `Fin m`, each wrapped in `some`. -/
theorem nativeTerminalLaw_output_uniform (b m : ℕ) [NeZero m] (hb : m ≤ 2^b) :
    (nativeTerminalLaw b m).map (Option.map Prod.fst) =
      (PMF.uniformOfFintype' (Fin m)).map (fun j => some j.val) := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne _)
  symm
  apply map_eq_of_mass_le
  · intro i j he
    exact Fin.ext (Option.some.inj he)
  · intro j
    have he : ((nativeTerminalLaw b m).map (Option.map Prod.fst)) (some j.val) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeTerminalLaw b m) (fun z => z.map Prod.fst = some j.val) := by
      rw [PMF.map_apply,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
      unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      apply tsum_congr
      intro z
      (try dsimp only)
      by_cases hz : z.map Prod.fst = some j.val
      · rw [if_pos hz.symm,if_pos hz,mul_one]
      · rw [if_neg (fun he => hz he.symm),if_neg hz,mul_zero]
    rw [he,nativeTerminalLaw_return b m hm hb j]
    simp only [PMF.uniformOfFintype'_apply,Fintype.card_fin,one_div,le_refl]

/-- For an invalid bound, the terminal observation law is concentrated on nontermination. -/
theorem nativeTerminalLaw_invalid (b m : ℕ) (hbad : ¬ (0 < m ∧ m ≤ 2^b)) :
    nativeTerminalLaw b m = PMF.pure none := by
  apply pmf_eq_pure_of_one
  rw [nativeTerminalLaw_none,neverMass_eq_iInf_fuel]
  simp only [← nativeLaw_timeout_eq_fuel,nativeLaw_invalid_timeout b m _ hbad,iInf_const]
  exact le_rfl

/-- With zero width and bound one, the terminal law is concentrated on returning zero with zero
CPU steps and zero random-bit reads. -/
theorem nativeTerminalLaw_zero_width : nativeTerminalLaw 0 1 = PMF.pure (some (0,0,0)) := by
  have hc := law_complete_terminal program 0 (input 0 1) (fun r hr => by
    rw [law_eq_pure_of_run_nil program 0 (input 0 1) (by decide +kernel),PMF.mem_support_pure_iff] at hr
    subst r
    decide +kernel)
  rw [nativeTerminalLaw,← hc,PMF.map_comp,law_eq_pure_of_run_nil program 0 (input 0 1) (by decide +kernel),PMF.pure_map]
  rfl

/-- Every supported returned terminal observation is realized by a halted native run using
exactly its consumed bits and recorded step count. Its trace is a valid path, no input
remains unread, and every smaller CPU budget ends in fuel exhaustion. -/
theorem nativeTerminalLaw_first_stop (b m : ℕ) (z : ℕ × ℕ × ℕ)
    (hz : some z ∈ (nativeTerminalLaw b m).support) :
    ∃ r : Result Symbol Control, (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length) = z ∧
      Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program r.steps r.bits (input b m) = r ∧ r.unread = [] ∧ r.stop = .halted ∧
      Path program (input b m) r.trace r.cfg ∧
        ∀ k < r.steps, (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program k r.bits (input b m)).stop = .fuel := by
  obtain ⟨s,hs,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  cases s with
  | none => simp at he
  | some r =>
    refine ⟨r,Option.some.inj he,?_⟩
    exact terminalLaw_first_stop program (input b m) r hs

/-- For a positive representable bound, terminal expected CPU cost, assigning infinite cost to
nontermination, is bounded by the supremum of expected CPU steps over finite CPU budgets. -/
theorem nativeTerminalLaw_cpu_le_sup (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m)
      (fun z => match z with | none => ⊤ | some out => (out.2.1 : ℝ≥0∞)) ≤
        ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞)) := by
  classical
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m)
        (fun z => match z with | none => 0 | some out => (out.2.1 : ℝ≥0∞)) := by
      apply expectation_congr_support
      intro z hz
      cases z with
      | none => exact False.elim (((PMF.mem_support_iff _ _).mp hz) (nativeTerminalLaw_none_zero b m hm hb))
      | some out => rfl
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (terminalLaw program (input b m))
        (fun z => match z with | none => 0 | some r => (r.steps : ℝ≥0∞)) := by
      rw [nativeTerminalLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      cases z <;> rfl
    _ = ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law program n (input b m))
        (fun r => if r.stop = .halted then (r.steps : ℝ≥0∞) else 0) :=
      by
        convert! terminalLaw_halted_expectation program (input b m) (fun r => (r.steps : ℝ≥0∞)) using 1
        congr 1
        funext x
        cases x <;> rfl
    _ ≤ ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law program n (input b m)) (fun r => (r.steps : ℝ≥0∞)) := by
      apply iSup_mono
      intro n
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall
      intro r
      split_ifs <;> simp
    _ = _ := by simp only [nativeLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,trialObservation]

/-- For a positive representable bound, terminal expected CPU cost is finite even when
nontermination is assigned infinite cost. -/
theorem nativeTerminalLaw_cpu_finite (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m)
      (fun z => match z with | none => ⊤ | some out => (out.2.1 : ℝ≥0∞)) < ⊤ :=
  lt_of_le_of_lt (nativeTerminalLaw_cpu_le_sup b m hm hb) (nativeLaw_time_sup_finite b m hm hb)

/-- For `m > 0`, choosing width `Nat.clog 2 m` bounds terminal expected CPU cost by `6*Nat.clog
2 m+4`, with infinite cost assigned to nontermination. -/
theorem nativeTerminalLaw_effective_cpu_bound (m : ℕ) (hm : 0 < m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw (Nat.clog 2 m) m)
      (fun z => match z with | none => ⊤ | some out => (out.2.1 : ℝ≥0∞)) ≤
        6*(Nat.clog 2 m : ℝ≥0∞)+4 := by
  have hb : m ≤ 2^(Nat.clog 2 m) := (finite_coin_effective_cutoff m 1 hm).1
  exact (nativeTerminalLaw_cpu_le_sup _ _ hm hb).trans
    (iSup_le (fun n => nativeLaw_effective_time_bound m n hm))

/-- Evaluating `haltedPayoff F` under the native observation law is equivalent to evaluating `F`
on halted runs and assigning zero to all other runs. -/
theorem nativeLaw_haltedPayoff_eq (b m n : ℕ) (F : ℕ × ℕ × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (haltedPayoff F) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law program n (input b m))
        (fun r => if r.stop = .halted then F (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length) else 0) := by
  rw [nativeLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro r
  cases hs : r.stop <;> simp [haltedPayoff,trialObservation,hs]

/-- For every nonnegative extended-real payoff on completed observations, its expected halted
payoff is monotone in the CPU budget. -/
theorem nativeLaw_haltedPayoff_mono (b m : ℕ) (F : ℕ × ℕ × ℕ → ℝ≥0∞) :
    Monotone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (haltedPayoff F)) := by
  intro n N hN
  simpa only [nativeLaw_haltedPayoff_eq] using! law_halted_expectation_mono program (input b m)
    (fun r => F (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length)) hN

/-- A terminal payoff with value zero on nontermination has expectation equal to the supremum of
its expected halted payoff over all cycle caps. -/
theorem nativeTerminalLaw_moment_capSup (b m : ℕ) (F : ℕ × ℕ × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim 0 F) =
      ⨆ cap, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (haltedPayoff F) := by
  have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim 0 F) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (terminalLaw program (input b m))
        (fun z => match z with | none => 0 | some r => F (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length)) := by
    rw [nativeTerminalLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro z
    cases z <;> rfl
  rw [he]
  have hh := terminalLaw_halted_expectation program (input b m)
    (fun r => F (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length))
  trans ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law program n (input b m))
    (fun r => if r.stop = .halted then F (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length) else 0)
  · convert! hh using 1
    congr 1
    funext z
    cases z <;> rfl
  · simp only [← nativeLaw_haltedPayoff_eq]
    rw [iSup_mul_budget _ (nativeLaw_haltedPayoff_mono b m F) (cycleSteps b) (by simp [cycleSteps])]
    simp only [nativeLaw_cycle_all]

/-- A pending counted observation arising from a unit-weight sampler path records exactly `cap`
full cycles and `b*cap` random-bit reads. -/
theorem countedObservation_pending_path (b m cap : ℕ) (z : SamplerRecord m) (raw : List Bool)
    (hz : (z,raw) ∈ (weightedSampler (fun _ : Fin m => 1) b cap).paths)
    (h : (countedObservation b z).1 = none) :
    countedObservation b z = (none,cycleSteps b*cap,b*cap) := by
  obtain ⟨bad,_,_,hd⟩ := countedLoop_words m b cap (0,0) z raw hz
  rcases z with ⟨cfg,t⟩
  cases cfg with
  | inl out => simp [countedObservation] at h
  | inr pending =>
    change raw = bad.flatten ∧ bad.length = cap ∧ t = cap at hd
    rw [hd.2.2]
    rfl

/-- For positive width and a valid bound, every supported capped observation with no return is
exactly `(none, cycleSteps b*cap, b*cap)`. -/
theorem nativeCapLaw_pending_support (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b)
    (z : Option ℕ × ℕ × ℕ) (hz : z ∈ (nativeCapLaw b m cap).support) (h : z.1 = none) :
    z = (none,cycleSteps b*cap,b*cap) := by
  let p := weightedSampler (fun _ : Fin m => 1) b cap
  obtain ⟨i,_,rfl⟩ := (PMF.mem_support_map_iff _ p.pathLaw z).mp hz
  have he := (weightedSampler_native_word b m cap (p.paths.get i) (List.get_mem _ _) hbpos hm hb).1
  change (trialObservation b (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) (p.paths.get i).2 (input b m))).1 = none at h
  change trialObservation b
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (cycleSteps b*cap) (p.paths.get i).2 (input b m)) = _
  rw [he] at h ⊢
  exact countedObservation_pending_path b m cap _ _ (List.get_mem _ _) h

/-- For positive width and a valid bound, any capped payoff expectation splits into its
contribution from returned outcomes and its value at the unique pending observation times
the timeout probability. -/
theorem nativeCapLaw_payoff_decomposition (b m cap : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b)
    (F : Option ℕ × ℕ × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) F =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap)
        (fun z => match z.1 with | none => 0 | some _ => F z) +
        F (none,cycleSteps b*cap,b*cap) * rationalRejectMass (fun _ : Fin m => 1) b ^ cap := by
  classical
  have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap)
      (fun z => if z.1 = none then F (none,cycleSteps b*cap,b*cap) else 0) =
        F (none,cycleSteps b*cap,b*cap) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nativeCapLaw b m cap) (fun z => z.1 = none) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro z
    split_ifs <;> simp
  rw [← nativeCapLaw_timeout b m cap hbpos hm hb,← he,← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  apply expectation_congr_support
  intro z hz
  cases ht : z.1 with
  | none =>
    have hp := nativeCapLaw_pending_support b m cap hbpos hm hb z hz ht
    simp [hp]
  | some j => simp

/-- For an extended nonnegative real `q < 1`, the product `(c*cap) * q^cap` tends to zero for
every natural coefficient `c`. -/
theorem pending_geometric_cost_tendsto (q : ℝ≥0∞) (hq : q < 1) (c : ℕ) :
    Filter.Tendsto (fun cap => ((c*cap : ℕ) : ℝ≥0∞)*q^cap) Filter.atTop (nhds 0) := by
  have hqfin : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq.le
  have hqr : q.toReal < 1 := by
    have hh := (ENNReal.toReal_lt_toReal hqfin ENNReal.one_ne_top).mpr hq
    simpa using! hh
  have hr := tendsto_self_mul_const_pow_of_lt_one ENNReal.toReal_nonneg hqr
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have hn : Filter.Tendsto (fun cap : ℕ => (cap : ℝ≥0∞)*q^cap) Filter.atTop (nhds 0) := by
    convert! he using 1
    · funext cap
      change (cap : ℝ≥0∞)*q^cap = ENNReal.ofReal ((cap : ℝ)*q.toReal^cap)
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cap),ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hqfin]
    · simp
  have hc := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) hn (Or.inr (ENNReal.natCast_ne_top _))
  simpa only [Nat.cast_mul,mul_assoc,mul_zero] using! hc

/-- For every positive number `m` of unit weights, the width-`b` rejection mass is strictly less
than one. -/
theorem unit_reject_lt_one (b m : ℕ) (hm : 0 < m) :
    rationalRejectMass (fun _ : Fin m => 1) b < 1 := by
  simp only [rationalRejectMass,coinRejectMass,weightTotal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,mul_one]
  have hden : ((2^b : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_ne_zero b (by decide : (2 : ℕ) ≠ 0))
  rw [ENNReal.div_lt_iff (Or.inl hden) (Or.inl (ENNReal.natCast_ne_top _)),one_mul]
  exact_mod_cast Nat.sub_lt (by positivity : 0 < (2 : ℕ)^b) hm

/-- For positive width and a valid bound, a payoff whose value on the pending observation is
`k*cap` has the same expectation limit after its pending contribution is set to zero. -/
theorem nativeCapLaw_completed_cost_tendsto (b m k : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b)
    (G : Option ℕ × ℕ × ℕ → ℝ≥0∞) (hk : ∀ cap, G (none,cycleSteps b*cap,b*cap) = ((k*cap : ℕ) : ℝ≥0∞))
    (L : ℝ≥0∞) (hG : Filter.Tendsto (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) G)
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap)
      (fun z => match z.1 with | none => 0 | some _ => G z)) Filter.atTop (nhds L) := by
  have hq := unit_reject_lt_one b m hm
  have hqfin := ne_top_of_le_ne_top ENNReal.one_ne_top hq.le
  have hpending := pending_geometric_cost_tendsto _ hq k
  have heq (cap : ℕ) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap)
      (fun z => match z.1 with | none => 0 | some _ => G z) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) G -
          ((k*cap : ℕ) : ℝ≥0∞)*rationalRejectMass (fun _ : Fin m => 1) b^cap := by
    have he := nativeCapLaw_payoff_decomposition b m cap hbpos hm hb G
    rw [hk] at he
    exact ENNReal.eq_sub_of_add_eq
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top hqfin)) he.symm
  simp_rw [heq]
  simpa only [tsub_zero] using! ENNReal.Tendsto.sub hG hpending (Or.inr ENNReal.zero_ne_top)

/-- For every nonnegative extended-real payoff on completed observations, its expected halted
payoff is monotone in the cycle cap. -/
theorem nativeCapLaw_haltedPayoff_mono (b m : ℕ) (F : ℕ × ℕ × ℕ → ℝ≥0∞) :
    Monotone (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (haltedPayoff F)) := by
  intro n N hN
  have hh := nativeLaw_haltedPayoff_mono b m F (Nat.mul_le_mul_left (cycleSteps b) hN)
  simpa only [nativeLaw_cycle_all] using! hh

/-- For a positive representable bound, replacing any assigned payoff on nontermination by zero
leaves the terminal expectation unchanged. -/
theorem nativeTerminalLaw_expectation_zero_never (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b)
    (F : ℕ × ℕ × ℕ → ℝ≥0∞) (a : ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim a F) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim 0 F) := by
  apply expectation_congr_support
  intro z hz
  cases z with
  | none => exact False.elim (((PMF.mem_support_iff _ _).mp hz) (nativeTerminalLaw_none_zero b m hm hb))
  | some out => rfl

/-- For a positive representable bound, terminal expected CPU cost is `cycleSteps b / (1 -
rationalRejectMass (fun _ : Fin m => 1) b) - (b+2)`, with infinite cost assigned to
nontermination. -/
theorem nativeTerminalLaw_cpu_mean (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim ⊤ (fun out => (out.2.1 : ℝ≥0∞))) =
      (cycleSteps b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) - (b+2 : ℝ≥0∞) := by
  rw [nativeTerminalLaw_expectation_zero_never b m hm hb,nativeTerminalLaw_moment_capSup]
  cases b with
  | zero =>
    have hm1 : m = 1 := by norm_num at hb; omega
    subst m
    norm_num [nativeCapLaw_zero_width,haltedPayoff,cycleSteps,rationalRejectMass,coinRejectMass,weightTotal]
  | succ b =>
    apply iSup_eq_of_tendsto (nativeCapLaw_haltedPayoff_mono (b+1) m _)
    simpa only [haltedPayoff] using! nativeCapLaw_completed_cost_tendsto (b+1) m (cycleSteps (b+1))
      (by omega) hm hb (fun z => (z.2.1 : ℝ≥0∞)) (fun _ => rfl) _
      (nativeCapLaw_time_tendsto (b+1) m (by omega) hm hb)

/-- For positive width and a valid bound, expected capped random-bit reads converge to `b / (1 -
rationalRejectMass (fun _ : Fin m => 1) b)` as the cap grows. -/
theorem nativeCapLaw_reads_tendsto (b m : ℕ) (hbpos : 0 < b) (hm : 0 < m) (hb : m ≤ 2^b) :
    Filter.Tendsto (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.2 : ℝ≥0∞)))
      Filter.atTop (nhds ((b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b))) := by
  have hw : 0 < weightTotal (fun _ : Fin m => 1) := by simpa [weightTotal] using! hm
  have hcap : weightTotal (fun _ : Fin m => 1) ≤ 2^b := by simpa [weightTotal] using! hb
  have heq : (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeCapLaw b m cap) (fun z => (z.2.2 : ℝ≥0∞))) =
      (fun cap => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler (fun _ : Fin m => 1) b cap).law) := by
    funext cap
    rw [nativeCapLaw_reads_mean b m cap hbpos hm hb,(weightedSampler_expectations (fun _ : Fin m => 1) b cap hw hcap).1]
  rw [heq]
  exact (weightedSampler_expected_reads_limit (fun _ : Fin m => 1) b hw hcap).1

/-- For a positive representable bound, terminal expected random-bit reads are `b / (1 -
rationalRejectMass (fun _ : Fin m => 1) b)`, assigning zero reads to nontermination. -/
theorem nativeTerminalLaw_reads_mean (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim 0 (fun out => (out.2.2 : ℝ≥0∞))) =
      (b : ℝ≥0∞)/(1-rationalRejectMass (fun _ : Fin m => 1) b) := by
  rw [nativeTerminalLaw_moment_capSup]
  cases b with
  | zero =>
    have hm1 : m = 1 := by norm_num at hb; omega
    subst m
    simp [nativeCapLaw_zero_width,haltedPayoff]
  | succ b =>
    apply iSup_eq_of_tendsto (nativeCapLaw_haltedPayoff_mono (b+1) m _)
    simpa only [haltedPayoff] using! nativeCapLaw_completed_cost_tendsto (b+1) m (b+1)
      (by omega) hm hb (fun z => (z.2.2 : ℝ≥0∞)) (fun _ => rfl) _
      (nativeCapLaw_reads_tendsto (b+1) m (by omega) hm hb)

/-- Any halted run that consumes its entire supplied random word contributes its output, CPU
steps, and random-bit count to the support of the terminal observation law. -/
theorem nativeTerminalLaw_support_halted_run (b m n : ℕ) (raw : List Bool)
    (hs : (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).stop = .halted)
    (hu : (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).unread = []) :
    some (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).cfg.Tape,
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).steps,(Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).bits.length) ∈
        (nativeTerminalLaw b m).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨some (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)),?_,rfl⟩
  rw [terminalLaw_support_some]
  refine ⟨hs,n,?_⟩
  rw [PMF.mem_support_iff]
  have hl := law_run_lower program n raw (input b m) (by simp [hs]) hu
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 1/2) _) hl)

/-- For width two and bound three, the terminal law supports returning zero after `8*k+4` CPU
steps and `2*(k+1)` random-bit reads for every `k`. -/
theorem nativeTerminalLaw_repeated_reject_support (k : ℕ) :
    some (0,8*k+4,2*(k+1)) ∈ (nativeTerminalLaw 2 3).support := by
  let bad := List.replicate k [true,true]
  have hlen : ∀ w ∈ bad, w.length = 2 := by
    intro w hw
    have he := List.eq_of_mem_replicate hw
    subst w
    rfl
  have hbad : ∀ w ∈ bad, 3 ≤ binaryValue w := by
    intro w hw
    have he := List.eq_of_mem_replicate hw
    subst w
    decide +kernel
  have hh := first_accept_input 2 3 bad [false,false] [] 0
    (by decide) (by decide) (by decide) hlen hbad (by decide) (by decide)
  have hbLen : bad.length = k := by simp [bad]
  simp only [List.append_nil,Nat.add_zero,hbLen,cycleSteps] at hh
  change trialObservation 2 (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (8*k+4) (bad.flatten++[false,false]) (input 2 3)) =
    (some 0,8*k+4,2*(k+1)) ∧ _ at hh
  let r :=
      Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program (8*k+4)
      (bad.flatten++[false,false]) (input 2 3)
  change trialObservation 2 r = (some 0,8*k+4,2*(k+1)) ∧ r.unread = [] ∧
      r.bits = bad.flatten++[false,false] at hh
  have hs : r.stop = .halted := by
    by_contra hn
    have he := congrArg Prod.fst hh.1
    change (if r.stop = .halted then some (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output 2 r.cfg.Tape) else none) = some 0 at he
    simp [hn] at he
  have hv : (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output 2 r.cfg.Tape,r.steps,r.bits.length) = (0,8*k+4,2*(k+1)) := by
    have he := hh.1
    simpa only [trialObservation,hs,↓reduceIte,Prod.mk.injEq,Option.some.injEq] using! he
  have hp := nativeTerminalLaw_support_halted_run 2 3 (8*k+4) (bad.flatten++[false,false]) hs hh.2.1
  change some (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output 2 r.cfg.Tape,r.steps,r.bits.length) ∈ (nativeTerminalLaw 2 3).support at hp
  rwa [hv] at hp

/-- For width two and bound three, no natural bound controls the CPU steps of every returned
observation in the terminal support. -/
theorem nativeTerminalLaw_no_worst_cpu_bound :
    ¬ ∃ B : ℕ, ∀ z : ℕ × ℕ × ℕ, some z ∈ (nativeTerminalLaw 2 3).support → z.2.1 ≤ B := by
  rintro ⟨B,hB⟩
  have hb := hB (0,8*B+4,2*(B+1)) (nativeTerminalLaw_repeated_reject_support B)
  (try dsimp only at hb)
  omega

/-- For a positive representable bound, terminal expected CPU cost, assigning infinite cost to
nontermination, equals the supremum of expected CPU steps over finite CPU budgets. -/
theorem nativeTerminalLaw_cpu_eq_truncated_sup (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim ⊤ (fun out => (out.2.1 : ℝ≥0∞))) =
      ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.1 : ℝ≥0∞)) := by
  rw [nativeTerminalLaw_cpu_mean b m hm hb,nativeLaw_time_sup b m hm hb]

/-- For a positive representable bound, terminal expected random-bit reads, assigning zero to
nontermination, equal the supremum of expected reads over finite CPU budgets. -/
theorem nativeTerminalLaw_reads_eq_truncated_sup (b m : ℕ) (hm : 0 < m) (hb : m ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeTerminalLaw b m) (fun z => z.elim 0 (fun out => (out.2.2 : ℝ≥0∞))) =
      ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nativeLaw b m n) (fun z => (z.2.2 : ℝ≥0∞)) := by
  rw [nativeTerminalLaw_reads_mean b m hm hb,nativeLaw_reads_sup b m hm hb]

/-- A tape window at position `p` places the cursor between absolute positions zero and `b+1`,
inclusive. -/
theorem window_bounds {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol} (h : Window b p T) :
    0 ≤ p ∧ p ≤ (b : ℤ)+1 := by
  cases h <;> constructor <;> omega

/-- Moving right from a data cell preserves the width-`b` tape window and increases the absolute
cursor position by one. -/
theorem window_right_data {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol}
    (h : Window b p T) (hd : ∃ v : Bool × Bool, T.head = data v) :
    Window b (p+1) (T.move .right) := by
  obtain ⟨v,hv⟩ := hd
  cases h with
  | atMarker ys hlen => simp [head_cons,marker,data,cell] at hv
  | span xs ys hlen =>
    cases ys with
    | nil => simp [head_nil,data,cell] at hv
    | cons y ys =>
      simp only [List.map_cons,tape_right]
      have hh := Window.span (b := b) (y::xs) ys (by simp only [List.length_cons] at hlen ⊢; omega)
      simpa [List.map_cons,List.cons_append] using! hh

/-- Moving left from a head other than the marker preserves the width-`b` tape window and
decreases the absolute cursor position by one. -/
theorem window_left {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol}
    (h : Window b p T) (hm : T.head ≠ marker) : Window b (p-1) (T.move .left) := by
  cases h with
  | atMarker ys hlen => exact False.elim (hm (head_cons [] marker (ys.map data)))
  | span xs ys hlen =>
    cases xs with
    | nil =>
      simp only [List.map_nil,List.nil_append,tape_left,List.length_nil,Nat.cast_zero,zero_add,sub_self]
      exact Window.atMarker ys (by simpa using! hlen)
    | cons x xs =>
      simp only [List.map_cons,List.cons_append,tape_left]
      have hh := Window.span (b := b) xs (x::ys) (by simp only [List.length_cons] at hlen ⊢; omega)
      convert! hh using 1; simp

/-- Moving right from the marker preserves the width-`b` tape window and increases the absolute
cursor position by one. -/
theorem window_right_marker {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol}
    (h : Window b p T) (hm : T.head = marker) : Window b (p+1) (T.move .right) := by
  cases h with
  | atMarker ys hlen =>
    simp only [tape_right,zero_add]
    simpa using! Window.span [] ys (by simpa using! hlen)
  | span xs ys hlen =>
    cases ys with
    | nil => simp [head_nil,marker] at hm
    | cons y ys => simp [List.map_cons,head_cons,data,cell,marker] at hm

/-- Replacing the head data pair by another data pair preserves the tape window at the same
absolute cursor position. -/
theorem window_write_data {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol}
    (h : Window b p T) (hd : ∃ v : Bool × Bool, T.head = data v) (w : Bool × Bool) :
    Window b p (T.write (data w)) := by
  obtain ⟨v,hv⟩ := hd
  cases h with
  | atMarker ys hlen => simp [head_cons,marker,data,cell] at hv
  | span xs ys hlen =>
    cases ys with
    | nil => simp [head_nil,data,cell] at hv
    | cons y ys =>
      simp only [List.map_cons,tape_write]
      exact Window.span xs (w::ys) (by simpa using! hlen)

/-- A tape window supplies the workspace invariant whenever the control state is outside the
move-state range from `3` through `5`. -/
theorem workspace_of_window {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol} (q : Control)
    (hw : Window b p T) (hq : ¬ (3 ≤ q.val ∧ q.val ≤ 5)) : Workspace b p ⟨q,T⟩ :=
  ⟨hw,fun h => False.elim (hq h)⟩

/-- A transition from a read state preserves the workspace invariant at the position adjusted by
the executed statement's displacement. -/
theorem workspace_read_step (b : ℕ) (p : ℤ) (T : Turing.Tape Symbol) (c : Fin 3)
    (hw : Window b p T) (bit : Bool) (next : Control × Turing.TM0.Stmt Symbol)
    (hp : table program bit (readState c) T.head = some next) :
    Workspace b (p+statementDisplacement next.2) (advance ⟨readState c,T⟩ next) := by
  simp only [table,read_rule] at hp
  cases hh : T.head with
  | none =>
    by_cases hc : c = 2
    · simp only [hh,readCommand,if_pos hc,Option.some.injEq] at hp
      subst next
      change Workspace b (p-1) ⟨6,T.move .left⟩
      apply workspace_of_window
      · exact window_left hw (by simp [hh,marker])
      · decide
    · simp [hh,readCommand,hc] at hp
  | some a =>
    cases a with
    | inl u => cases u; simp [hh,readCommand] at hp
    | inr v =>
      rcases v with ⟨x,t⟩
      simp only [hh,readCommand,Option.some.injEq] at hp
      subst next
      change Workspace b (p+0) ⟨moveState (compareUpdate c (bit,t)),T.write (cell bit t)⟩
      rw [add_zero]
      constructor
      · exact window_write_data hw ⟨(x,t),hh⟩ (bit,t)
      · intro _
        exact ⟨(bit,t),rfl⟩

/-- Every defined program-table transition preserves the workspace invariant at the position
adjusted by its statement displacement. -/
theorem workspace_table_step (b : ℕ) (p : ℤ) (cfg : Turing.TM0.Cfg Symbol Control)
    (hw : Workspace b p cfg) (bit : Bool) (next : Control × Turing.TM0.Stmt Symbol)
    (hp : table program bit cfg.q cfg.Tape.head = some next) :
    Workspace b (p+statementDisplacement next.2) (advance cfg next) := by
  rcases cfg with ⟨q,T⟩
  fin_cases q
  · exact workspace_read_step b p T 0 hw.1 bit next hp
  · exact workspace_read_step b p T 1 hw.1 bit next hp
  · exact workspace_read_step b p T 2 hw.1 bit next hp
  · simp only [table,program,Option.some.injEq] at hp
    subst next
    change Workspace b (p+1) ⟨0,T.move .right⟩
    exact workspace_of_window 0 (window_right_data hw.1 (hw.2 (by norm_num))) (by decide)
  · simp only [table,program,Option.some.injEq] at hp
    subst next
    change Workspace b (p+1) ⟨1,T.move .right⟩
    exact workspace_of_window 1 (window_right_data hw.1 (hw.2 (by norm_num))) (by decide)
  · simp only [table,program,Option.some.injEq] at hp
    subst next
    change Workspace b (p+1) ⟨2,T.move .right⟩
    exact workspace_of_window 2 (window_right_data hw.1 (hw.2 (by norm_num))) (by decide)
  · by_cases hm : T.head = marker
    · simp only [table,program,if_pos hm,Option.some.injEq] at hp
      subst next
      change Workspace b (p+1) ⟨0,T.move .right⟩
      exact workspace_of_window 0 (window_right_marker hw.1 hm) (by decide)
    · simp only [table,program,if_neg hm,Option.some.injEq] at hp
      subst next
      change Workspace b (p-1) ⟨6,T.move .left⟩
      exact workspace_of_window 6 (window_left hw.1 hm) (by decide)
  · simp only [table,program,Option.some.injEq] at hp
    subst next
    change Workspace b (p+0) ⟨7,T.write T.head⟩
    rw [add_zero,Turing.Tape.write_self]
    exact workspace_of_window 7 hw.1 (by decide)

/-- Every native execution step preserves the workspace invariant after adding its tick
displacement to the absolute cursor position. -/
theorem workspace_step (b : ℕ) (p : ℤ) {cfg next : Turing.TM0.Cfg Symbol Control} {o : Option Bool}
    (hw : Workspace b p cfg) (hs : NativeTape.Step program cfg o next) :
    Workspace b (p+tickDisplacement program (cfg,o)) next := by
  cases ht : table program (o.getD false) cfg.q cfg.Tape.head with
  | none => have hh := hs.2; simp [TM0_step_apply,ht] at hh
  | some act =>
    have he : advance cfg act = next := by
      simpa only [TM0_step_apply,ht,Option.map_some,Option.some.injEq] using! hs.2
    rw [← he]
    simpa only [tickDisplacement,ht] using! workspace_table_step b p cfg hw (o.getD false) act ht

/-- A native path preserves the final workspace invariant after summing its tick displacements,
and every cursor position remains between zero and `b+1`. Every tick's source configuration
also satisfies a workspace invariant at some position. -/
theorem workspace_path (b : ℕ) {cfg last : Turing.TM0.Cfg Symbol Control} {es : List (Tick Symbol Control)}
    (hp : Path program cfg es last) (p : ℤ) (hw : Workspace b p cfg) :
    Workspace b (p+(es.map (tickDisplacement program)).sum) last ∧
      (∀ i ∈ cursorTrace program p es, 0 ≤ i ∧ i ≤ (b : ℤ)+1) ∧
        (∀ e ∈ es, ∃ i, Workspace b i e.1) := by
  induction hp generalizing p with
  | nil cfg =>
    refine ⟨by simpa using! hw,?_,by simp⟩
    intro i hi
    have he : i = p := by simpa [cursorTrace] using! hi
    subst i
    exact window_bounds hw.1
  | @cons cfg next last o es hs hp ih =>
    have hn := workspace_step b p hw hs
    obtain ⟨hEnd,hRange,hStates⟩ := ih (p+tickDisplacement program (cfg,o)) hn
    refine ⟨?_,?_,?_⟩
    · simpa only [List.map_cons,List.sum_cons,add_assoc] using! hEnd
    · intro i hi
      simp only [cursorTrace,List.scanl_cons,List.mem_cons] at hi
      rcases hi with he | ht
      · subst i
        exact window_bounds hw.1
      · exact hRange i ht
    · intro e he
      rcases List.mem_cons.mp he with rfl | ht
      · exact ⟨p,hw⟩
      · exact hStates e ht

/-- Every sampler input configuration satisfies the width-`b` workspace invariant with initial
cursor position one. -/
theorem workspace_input (b m : ℕ) : Workspace b 1 (input b m) := by
  let ys := (encode b (m-1)).map (fun t => (false,t))
  have hT : (input b m).Tape = Turing.Tape.mk₂ [marker] (ys.map data) := by
    simp [input,start,ys,List.map_map,data,Function.comp_def]
  constructor
  · rw [hT]
    simpa using! Window.span (b := b) [] ys (by simp [ys,encode_length])
  · intro hq
    by_cases hv : 0 < m ∧ m ≤ 2^b <;> simp [input,start,hv] at hq

/-- Every finite sampler run preserves the workspace invariant and keeps all cursor positions
between zero and `b+1`. Each configuration appearing as a tick source satisfies the
invariant at some absolute position. -/
theorem run_workspace (b m n : ℕ) (raw : List Bool) :
    let r := Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)
    Workspace b (1+(r.trace.map (tickDisplacement program)).sum) r.cfg ∧
      (∀ i ∈ cursorTrace program 1 r.trace, 0 ≤ i ∧ i ≤ (b : ℤ)+1) ∧
        (∀ e ∈ r.trace, ∃ i, Workspace b i e.1) :=
  workspace_path b (run_path program n raw (input b m)) 1 (workspace_input b m)

/-- Every finite sampler run visits at most `b+2` distinct cursor positions. -/
theorem run_visited_cells_le (b m n : ℕ) (raw : List Bool) :
    (cursorTrace program 1 (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).trace).toFinset.card ≤ b+2 := by
  have hsub : (cursorTrace program 1 (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).trace).toFinset ⊆
      (Finset.range (b+2)).image (fun i : ℕ => (i : ℤ)) := by
    intro i hi
    have hb := (run_workspace b m n raw).2.1 i (List.mem_toFinset.mp hi)
    apply Finset.mem_image.mpr
    refine ⟨i.toNat,Finset.mem_range.mpr (by omega),?_⟩
    omega
  exact (Finset.card_le_card hsub).trans (by simpa using! (Finset.card_image_le
    (s := Finset.range (b+2)) (f := fun i : ℕ => (i : ℤ))))

/-- The union of initially occupied cells and visited cursor positions contains at most `b+2`
cells for every finite sampler run. -/
theorem run_workspace_cells_le (b m n : ℕ) (raw : List Bool) :
    (workspaceCells b (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).trace).card ≤ b+2 := by
  have hsub : workspaceCells b (Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)).trace ⊆
      (Finset.range (b+2)).image (fun i : ℕ => (i : ℤ)) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hin | hvisit
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hin
      exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega),rfl⟩
    · have hb := (run_workspace b m n raw).2.1 i (List.mem_toFinset.mp hvisit)
      exact Finset.mem_image.mpr ⟨i.toNat,Finset.mem_range.mpr (by omega),by omega⟩
  exact (Finset.card_le_card hsub).trans (by simpa using! (Finset.card_image_le
    (s := Finset.range (b+2)) (f := fun i : ℕ => (i : ℤ))))

/-- A tape built from lists `L` and `R` is blank at every relative position strictly below
`-L.length` or at least `R.length`. -/
theorem tape_outside_lists (L R : List Symbol) (i : ℤ)
    (hi : i < -(L.length : ℤ) ∨ (R.length : ℤ) ≤ i) : (Turing.Tape.mk₂ L R).nth i = none := by
  cases i with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at hi ⊢
    have hn : R.length ≤ n := by omega
    rw [Turing.Tape.mk₂,Turing.Tape.mk'_nth_nat,Turing.ListBlank.nth_mk,List.getI_eq_default _ hn]
    rfl
  | negSucc n =>
    have hn : L.length ≤ n := by omega
    change (Turing.ListBlank.mk L).nth n = none
    rw [Turing.ListBlank.nth_mk,List.getI_eq_default _ hn]
    rfl

/-- A tape satisfying the width-`b` window invariant is blank at every absolute position outside
the interval from zero to `b`. -/
theorem window_outside_blank {b : ℕ} {p : ℤ} {T : Turing.Tape Symbol}
    (hw : Window b p T) (j : ℤ) (hj : j < 0 ∨ (b : ℤ) < j) : T.nth (j-p) = none := by
  cases hw with
  | atMarker ys hlen =>
    apply tape_outside_lists
    simp only [List.length_nil,List.length_cons,List.length_map] at *
    omega
  | span xs ys hlen =>
    apply tape_outside_lists
    simp only [List.length_append,List.length_map,List.length_singleton] at *
    omega

/-- After any finite sampler run, every absolute tape position outside the interval from zero to
`b` remains blank, with relative indices adjusted by the final cursor position. -/
theorem run_outside_blank (b m n : ℕ) (raw : List Bool) (j : ℤ) (hj : j < 0 ∨ (b : ℤ) < j) :
    let r := Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program n raw (input b m)
    r.cfg.Tape.nth (j-(1+(r.trace.map (tickDisplacement program)).sum)) = none :=
  window_outside_blank (run_workspace b m n raw).1.1 j hj

/-- The finite numeric encoding `symbolCode` distinguishes all tape symbols. -/
theorem symbolCode_injective : Function.Injective symbolCode := by decide +kernel

/-- The three-bit encoding `symbolBits` distinguishes all tape symbols. -/
theorem symbolBits_injective : Function.Injective symbolBits :=
  (bitVecEquiv 3).symm.injective.comp symbolCode_injective

/-- The native sampler has six tape symbols and eight control states. -/
theorem native_alphabet_control_card : Fintype.card Symbol = 6 ∧ Fintype.card Control = 8 := by
    decide +kernel

/-- Every result in a finite native execution law's support uses at most `b+2` workspace cells. -/
theorem law_workspace_cells_le (b m n : ℕ) (r : Result Symbol Control)
    (hr : r ∈ (NativeTape.law program n (input b m)).support) : (workspaceCells b r.trace).card ≤ b+2 := by
  have he := (law_support_run program n (input b m) r hr).1
  have hh := run_workspace_cells_le b m n r.bits
  rwa [he] at hh

/-- Every returned result in the terminal execution law's support uses at most `b+2` workspace
cells. -/
theorem terminal_workspace_cells_le (b m : ℕ) (r : Result Symbol Control)
    (hr : some r ∈ (terminalLaw program (input b m)).support) : (workspaceCells b r.trace).card ≤ b+2 := by
  obtain ⟨_,n,hn⟩ := (terminalLaw_support_some program (input b m) r).mp hr
  exact law_workspace_cells_le b m n r hn

/-- The supremum of workspace-cell counts over all CPU budgets and random input words is at most
`b+2`. -/
theorem peakWorkspaceCells_le (b m : ℕ) : peakWorkspaceCells b m ≤ ((b+2 : ℕ) : ℝ≥0∞) := by
  apply iSup_le
  intro n
  apply iSup_le
  intro raw
  exact_mod_cast run_workspace_cells_le b m n raw

/-- The sampler's peak workspace-cell count is finite for every width and bound. -/
theorem peakWorkspaceCells_finite (b m : ℕ) : peakWorkspaceCells b m < ⊤ :=
  lt_of_le_of_lt (peakWorkspaceCells_le b m) (by finiteness)

/-- Every supported returned terminal observation has a realizing native run using exactly its
recorded steps and consumed bits. That run uses at most `b+2` workspace cells. -/
theorem nativeTerminalLaw_workspace (b m : ℕ) (z : ℕ × ℕ × ℕ)
    (hz : some z ∈ (nativeTerminalLaw b m).support) :
    ∃ r : Result Symbol Control, (Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape.output b r.cfg.Tape,r.steps,r.bits.length) = z ∧
      Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape.run program r.steps r.bits (input b m) = r ∧
        (workspaceCells b r.trace).card ≤ b+2 := by
  obtain ⟨r,hobs,he,_⟩ := nativeTerminalLaw_first_stop b m z hz
  refine ⟨r,hobs,he,?_⟩
  have hh := run_workspace_cells_le b m r.steps r.bits
  rwa [he] at hh
end Qatlib.Concepts.AmplitudeSearch.Amplification
