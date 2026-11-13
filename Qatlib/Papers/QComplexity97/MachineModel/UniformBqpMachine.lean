/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QComplexity97.MachineModel.UniformBqpMachineDefs

/-!
# Explicit machines for uniform finite gate families

This module verifies concrete bit-tape generators for the uniform finite gate-word framework
used in the development of [BernsteinVazirani1997]. The echo machine produces a single Hadamard
gate on a register of width `n + 1`; its tape configurations give the exact execution and
halting result `echo_halts_at`. For an arbitrary `GateProgram`, the analogous construction
produces the prefix `P.gates.take n`, as recorded by `gen_generated`.

The machine proofs establish legal output words, polynomial clocks, local unidirectionality, and
the declared resource bounds through `echo_valid` and `gen_valid`. Exact finite-digit
representations of the fixed gate matrices supply `legalWord_finiteDigitBackend`, while
`clause5_complete` and `clause6_complete` collect the circuit transport and generator
obligations.

## Main statements

* `echo_generated`: the echo generator returns `(n + 1, [echoGate])`.
* `echo_halts_at`: the echo machine halts at time `2 * n + 14` on unary input `n`.
* `legalWord_finiteDigitBackend`: every legal finite gate word has exact finite-digit gate
  entries.
* `gen_generated`: a program generator returns `(n + 1, P.gates.take n)`.
* `gen_valid`: every program generator satisfies its generation and resource bounds.
* `clause5_complete` and `clause6_complete`: the collected circuit transport and machine
  obligations.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.QComplexity97.MachineDefs.UniformBqpMachine
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace UniformBqpMachine

open Turing

/-- Constructs an `Option Bool` tape from the nearest-first left list `l` and the list `r`
beginning at the head. -/
def tapeOf (l r : List (Option Bool)) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk l) (ListBlank.mk r)

/-- The head of `tapeOf l r` is the default head `r.headI` of the right-hand list. -/
@[simp] theorem tapeOf_head {l r : List (Option Bool)} :
    (tapeOf l r).head = r.headI := by
  simp [tapeOf, Tape.mk', ListBlank.head_mk]

/-- The left side of `tapeOf l r` is the blank-extended list `ListBlank.mk l`. -/
@[simp] theorem tapeOf_left {l r : List (Option Bool)} :
    (tapeOf l r).left = ListBlank.mk l := by
  simp [tapeOf, Tape.mk']

/-- The cells strictly to the right of the head of `tapeOf l r` form `ListBlank.mk r.tail`. -/
@[simp] theorem tapeOf_right {l r : List (Option Bool)} :
    (tapeOf l r).right = ListBlank.mk r.tail := by
  simp [tapeOf, Tape.mk']

/-- The head-inclusive right side of `tapeOf l r` is `ListBlank.mk (r.headI :: r.tail)`. -/
@[simp] theorem tapeOf_right₀ {l r : List (Option Bool)} :
    (tapeOf l r).right₀ = ListBlank.mk (r.headI :: r.tail) := by
  simp only [tapeOf, Tape.mk', Tape.right₀, ListBlank.head_mk, ListBlank.tail_mk,
    ListBlank.cons_mk]

/-- Moving `tapeOf l r` right transfers `r.headI` to the front of `l` and leaves `r.tail`
beginning at the new head. -/
@[simp] theorem tapeOf_move_right {l r : List (Option Bool)} :
    (tapeOf l r).move Turing.Dir.right = tapeOf (r.headI :: l) r.tail := by
  simp only [tapeOf, Tape.mk', Tape.move, ListBlank.head_mk, ListBlank.tail_mk,
    ListBlank.cons_mk]

/-- Moving `tapeOf l r` left makes `l.headI` the new head, with `l.tail` to the left and the old
head followed by `r.tail` to the right. -/
@[simp] theorem tapeOf_move_left {l r : List (Option Bool)} :
    (tapeOf l r).move Turing.Dir.left = tapeOf l.tail (l.headI :: r.headI :: r.tail) := by
  simp only [tapeOf, Tape.mk', Tape.move, ListBlank.head_mk, ListBlank.tail_mk,
    ListBlank.cons_mk, List.headI_cons, List.tail_cons]

/-- Writing `a` on `tapeOf l r` replaces the head by `a` while retaining `l` and `r.tail`. -/
@[simp] theorem tapeOf_write {l r : List (Option Bool)} (a : Option Bool) :
    (tapeOf l r).write a = tapeOf l (a :: r.tail) := by
  simp only [tapeOf, Tape.mk', Tape.write, ListBlank.head_mk, ListBlank.tail_mk]
  rfl

/-- Identifies `Tape.mk₂ l r` with the list-based tape `tapeOf l r`. -/
@[simp] theorem tapeOf_mk₂ (l r : List (Option Bool)) :
    Tape.mk₂ l r = tapeOf l r := rfl

/-- The default head of a list containing `m + 1` copies of `a` is `a`. -/
@[simp] theorem replicate_headI_succ {m : ℕ} (a : Option Bool) :
    (List.replicate (m + 1) a).headI = a := by
  rw [List.replicate_succ, List.headI_cons]

/-- The default head of a list containing zero copies of an `Option Bool` value is `none`. -/
@[simp] theorem replicate_headI_zero (a : Option Bool) :
    (List.replicate 0 a).headI = none := by
  rw [List.replicate_zero, List.headI_nil]
  rfl

/-- Removing the head of `m + 1` copies of `a` leaves `m` copies. -/
@[simp] theorem replicate_tail_succ {m : ℕ} (a : Option Bool) :
    (List.replicate (m + 1) a).tail = List.replicate m a := by
  rw [List.replicate_succ]
  rfl

/-- Prepending `a` to `m` copies of `a` gives the list of `m + 1` copies. -/
theorem replicate_succ' {α : Type} {m : ℕ} (a : α) :
    a :: List.replicate m a = List.replicate (m + 1) a := by
  rw [List.replicate_succ]

/-- Records the reflexive equality of `m` one cells followed by three zero cells. -/
@[simp] theorem replicate_append_gate {m : ℕ} :
    List.replicate m (some true) ++ [some false, some false, some false]
      = List.replicate m (some true) ++ [some false, some false, some false] := rfl

/-- The default value of `Option Bool` is the blank symbol `none`. -/
@[simp] theorem default_optionBool : (default : Option Bool) = none := rfl

/-- The default head of `m` copies of `a` is `a` whenever `m` is nonzero. -/
theorem replicate_headI_of_ne_zero {m : ℕ} (a : Option Bool) (hm : m ≠ 0) :
    (List.replicate m a).headI = a := by
  cases m with
  | zero => exact absurd rfl hm
  | succ m => exact replicate_headI_succ a

/-- For nonzero `m`, the tail of `m` copies of `a` consists of `m - 1` copies. -/
theorem replicate_tail_of_ne_zero {m : ℕ} (a : Option Bool) (hm : m ≠ 0) :
    (List.replicate m a).tail = List.replicate (m - 1) a := by
  cases m with
  | zero => exact absurd rfl hm
  | succ m => exact replicate_tail_succ a

/-- Identifies the one-list tape `Tape.mk₁ l` with `tapeOf [] l`. -/
@[simp] theorem tapeOf_mk₁ (l : List (Option Bool)) :
    Tape.mk₁ l = tapeOf [] l := by
  rw [Tape.mk₁, tapeOf_mk₂]

/-- The initial configuration on unary input `n` has control `Echo.val .scan`, an empty left
side, and `n` one cells beginning at the head. -/
theorem init_eq_scan (n : ℕ) :
    Turing.TM0.init (uniformBqpUnaryInput n) =
      ⟨Echo.val .scan, tapeOf (List.replicate 0 (some true))
        (List.replicate n (some true))⟩ := by
  simp [Turing.TM0.init, tapeOf_mk₁, List.replicate_zero, Echo.val, uniformBqpUnaryInput]

/-- After `k ≤ n` steps on unary input `n`, `echoMachine` remains in the scan state with `k` one
cells to the left and `n - k` one cells beginning at the head. -/
theorem scan_run (n k : ℕ) (hk : k ≤ n) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) k =
      some ⟨Echo.val .scan,
        tapeOf (List.replicate k (some true)) (List.replicate (n - k) (some true))⟩ := by
  induction k with
  | zero =>
    rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep, init_eq_scan]
    simp [List.replicate_zero]
  | succ k ih =>
    have hkn : k < n := by omega
    have hne : n - k ≠ 0 := by omega
    have hhead : (List.replicate (n - k) (some true)).headI = some true :=
      replicate_headI_of_ne_zero (a := some true) hne
    rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ, ih (by omega)]
    simp only [Turing.TM0.step, echoMachine, Option.bind_some, Echo.val, Fin.val_zero, tapeOf_head,
      hhead, if_pos, Option.map_some]
    rw [tapeOf_move_right]
    simp only [hhead]
    have hleft : some true :: List.replicate k (some true) = List.replicate (k + 1) (some true) :=
      replicate_succ' (some true)
    have hright : (List.replicate (n - k) (some true)).tail
        = List.replicate (n - (k + 1)) (some true) := by
      rw [replicate_tail_of_ne_zero (a := some true) hne]
      congr 1
    rw [hleft, hright]

/-- Reading a blank-extended list `L` containing no blank cells succeeds whenever the reading
bound is at least `L.length`, returning the Boolean values of its cells. -/
theorem readOutput_of_list {L : List (Option Bool)} :
    ∀ (B : ℕ), L.length ≤ B → (∀ a ∈ L, a ≠ none) →
      Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelReadOutputUntilBlank B (ListBlank.mk L)
        = some (L.map fun o => o.getD false) := by
  induction L with
  | nil =>
    intro B hL hnb
    cases B with
    | zero =>
      rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelReadOutputUntilBlank_zero, ListBlank.nth_mk,
        List.getI_eq_default (l := []) (n := 0) (by simp)]
      rfl
    | succ k =>
      rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelReadOutputUntilBlank_succ]
      rw [ListBlank.nth_mk, List.getI_eq_default (l := []) (n := 0) (by simp)]
      rfl
  | cons a t ih =>
    intro B hL hnb
    have ha : a ≠ none := hnb a List.mem_cons_self
    cases B with
    | zero =>
      have hz : (a :: t).length ≤ 0 := hL
      simp at hz
    | succ k =>
      rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelReadOutputUntilBlank_succ]
      rw [ListBlank.nth_mk, List.getI_cons_zero]
      obtain ⟨b, rfl⟩ : ∃ b, a = some b := by
        cases a with
        | none => exact absurd rfl ha
        | some b => exact ⟨b, rfl⟩
      rw [ListBlank.tail_mk, List.tail_cons]
      have hlt : t.length ≤ k := by
        have hlt' : t.length + 1 ≤ k + 1 := by simpa using! hL
        omega
      rw [ih k hlt (fun x hx => hnb x (List.mem_cons_of_mem (some b) hx))]
      simp [List.map_cons, Option.getD_some]

/-- The echo scan configuration after all `n` input one cells have moved to the left of the
blank head. -/
def cfgScan (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .scan, tapeOf (List.replicate n (some true)) (List.replicate 0 (some true))⟩

/-- The echo configuration in state `Echo.val .widthBit` with `n` one cells to the left of a
blank head. -/
def cfgWidthBit (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .widthBit, tapeOf (List.replicate n (some true)) [none]⟩

/-- The echo configuration in state `Echo.val .widthStep` with a one at the head and `n` one
cells to the left. -/
def cfgWidth (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .widthStep, tapeOf (List.replicate n (some true)) [some true]⟩

/-- The echo configuration in state `Echo.val .termBit` with a blank head and `n + 1` one cells
to the left. -/
def cfgWidthStep (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .termBit, tapeOf (some true :: List.replicate n (some true))
    (List.replicate 0 (some true))⟩

/-- The echo configuration in state `Echo.val .termStep` with a zero at the head and `n + 1` one
cells to the left. -/
def cfgTerm (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .termStep, tapeOf (some true :: List.replicate n (some true)) [some false]⟩

/-- The echo configuration in state `Echo.val .gateBit0` with a blank head and, nearest first to
the left, a zero followed by `n + 1` ones. -/
def cfgTermStep (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .gateBit0, tapeOf (some false :: some true :: List.replicate n (some true))
    (List.replicate 0 (some true))⟩

/-- The echo configuration in state `Echo.val .gateStep` with a zero at the head and, nearest
first to the left, a zero followed by `n + 1` ones. -/
def cfgGate0 (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .gateStep, tapeOf (some false :: some true :: List.replicate n (some true))
    [some false]⟩

/-- The echo configuration in state `Echo.val .gateBit1` with a blank head and, nearest first to
the left, two zeros followed by `n + 1` ones. -/
def cfgGateStep (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .gateBit1, tapeOf (some false :: some false :: some true :: List.replicate n (some true))
    (List.replicate 0 (some true))⟩

/-- The echo rewind configuration with a zero at the head and, nearest first to the left, two
zeros followed by `n + 1` ones. -/
def cfgGate1 (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .rewind, tapeOf (some false :: some false :: some true :: List.replicate n (some true))
    [some false]⟩

/-- The echo rewind configuration with two zeros beginning at the head and, nearest first to the
left, a zero followed by `n + 1` ones. -/
def cfgRewind1 (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .rewind, tapeOf (some false :: some true :: List.replicate n (some true))
    [some false, some false]⟩

/-- The echo rewind configuration with three zeros beginning at the head and `n + 1` ones to the
left. -/
def cfgRewind2 (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .rewind, tapeOf (some true :: List.replicate n (some true))
    [some false, some false, some false]⟩

/-- The echo rewind configuration with `n + 3 - j` ones to the left and a one, then `j - 3`
further ones, then three zeros beginning at the head. -/
def cfgRewind (n j : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .rewind,
    tapeOf (List.replicate (n + 3 - j) (some true))
      (some true :: (List.replicate (j - 3) (some true) ++
        [some false, some false, some false]))⟩

/-- The echo configuration in the done state with a blank immediately to the left and the output
of `n + 1` ones followed by three zeros beginning at the head. -/
def cfgDone (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .done,
    tapeOf [none] (some true :: (List.replicate n (some true) ++
      [some false, some false, some false]))⟩

/-- One step of `echoMachine` takes `cfgScan n` to `cfgWidthBit n`. -/
theorem step_cfgScan (n : ℕ) :
    Turing.TM0.step echoMachine (cfgScan n) = some (cfgWidthBit n) := by
  simp [cfgScan, cfgWidthBit, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    replicate_headI_zero, tapeOf_write]

/-- One step of `echoMachine` takes `cfgWidthBit n` to `cfgWidth n`. -/
theorem step_cfgWidthBit (n : ℕ) :
    Turing.TM0.step echoMachine (cfgWidthBit n) = some (cfgWidth n) := by
  simp [cfgWidthBit, cfgWidth, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_write]

/-- One step of `echoMachine` takes `cfgWidth n` to `cfgWidthStep n`. -/
theorem step_cfgWidth (n : ℕ) :
    Turing.TM0.step echoMachine (cfgWidth n) = some (cfgWidthStep n) := by
  simp [cfgWidth, cfgWidthStep, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_right]

/-- One step of `echoMachine` takes `cfgWidthStep n` to `cfgTerm n`. -/
theorem step_cfgWidthStep (n : ℕ) :
    Turing.TM0.step echoMachine (cfgWidthStep n) = some (cfgTerm n) := by
  simp [cfgWidthStep, cfgTerm, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_write]

/-- One step of `echoMachine` takes `cfgTerm n` to `cfgTermStep n`. -/
theorem step_cfgTerm (n : ℕ) :
    Turing.TM0.step echoMachine (cfgTerm n) = some (cfgTermStep n) := by
  simp [cfgTerm, cfgTermStep, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_right]

/-- One step of `echoMachine` takes `cfgTermStep n` to `cfgGate0 n`. -/
theorem step_cfgTermStep (n : ℕ) :
    Turing.TM0.step echoMachine (cfgTermStep n) = some (cfgGate0 n) := by
  simp [cfgTermStep, cfgGate0, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_right]

/-- One step of `echoMachine` takes `cfgGate0 n` to `cfgGateStep n`. -/
theorem step_cfgGate0 (n : ℕ) :
    Turing.TM0.step echoMachine (cfgGate0 n) = some (cfgGateStep n) := by
  simp [cfgGate0, cfgGateStep, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_write]

/-- One step of `echoMachine` takes `cfgGateStep n` to `cfgGate1 n`. -/
theorem step_cfgGateStep (n : ℕ) :
    Turing.TM0.step echoMachine (cfgGateStep n) = some (cfgGate1 n) := by
  simp [cfgGateStep, cfgGate1, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_right]

/-- One step of `echoMachine` takes `cfgGate1 n` to `cfgRewind1 n`. -/
theorem step_cfgGate1 (n : ℕ) :
    Turing.TM0.step echoMachine (cfgGate1 n) = some (cfgRewind1 n) := by
  simp [cfgGate1, cfgRewind1, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_left, List.headI_cons, List.tail_cons]

/-- One step of `echoMachine` takes `cfgRewind1 n` to `cfgRewind2 n`. -/
theorem step_cfgRewind1 (n : ℕ) :
    Turing.TM0.step echoMachine (cfgRewind1 n) = some (cfgRewind2 n) := by
  simp [cfgRewind1, cfgRewind2, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_left, List.headI_cons, List.tail_cons]

/-- One step of `echoMachine` takes `cfgRewind2 n` to `cfgRewind n 3`. -/
theorem step_cfgRewind2 (n : ℕ) :
    Turing.TM0.step echoMachine (cfgRewind2 n) = some (cfgRewind n 3) := by
  simp [cfgRewind2, cfgRewind, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_left, List.headI_cons, List.tail_cons]

/-- For `3 ≤ j ≤ n + 2`, one step of `echoMachine` takes `cfgRewind n j` to `cfgRewind n (j +
1)`. -/
theorem step_cfgRewind (n j : ℕ) (hj : 3 ≤ j) (hj' : j ≤ n + 2) :
    Turing.TM0.step echoMachine (cfgRewind n j) = some (cfgRewind n (j + 1)) := by
  have hne : n + 3 - j ≠ 0 := by omega
  have hhead : (List.replicate (n + 3 - j) (some true)).headI = some true :=
    replicate_headI_of_ne_zero (a := some true) hne
  simp [cfgRewind, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head, tapeOf_move_left,
    List.headI_cons, List.tail_cons, List.tail_append]
  rw [hhead]
  congr 1
  · congr 1
    omega
  · have hj2 : j - 2 = (j - 3) + 1 := by omega
    rw [hj2, ← replicate_succ' (some true), List.cons_append]

/-- On unary input `n`, iterating `echoMachine` for `n` steps reaches `cfgScan n`. -/
theorem scan_reaches (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n
      = some (cfgScan n) := by
  rw [scan_run n n (le_refl n)]
  simp [cfgScan, Nat.sub_self]

/-- On unary input `n`, iterating `echoMachine` for `n + 1` steps reaches `cfgWidthBit n`. -/
theorem emit_step1 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ
      = some (cfgWidthBit n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      scan_reaches n, Option.bind_some, step_cfgScan n]

/-- On unary input `n`, iterating `echoMachine` for `n + 2` steps reaches `cfgWidth n`. -/
theorem emit_step2 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ
      = some (cfgWidth n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step1 n, Option.bind_some, step_cfgWidthBit n]

/-- On unary input `n`, iterating `echoMachine` for `n + 3` steps reaches `cfgWidthStep n`. -/
theorem emit_step3 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ.succ
      = some (cfgWidthStep n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step2 n, Option.bind_some, step_cfgWidth n]

/-- On unary input `n`, iterating `echoMachine` for `n + 4` steps reaches `cfgTerm n`. -/
theorem emit_step4 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ.succ.succ
      = some (cfgTerm n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step3 n, Option.bind_some, step_cfgWidthStep n]

/-- On unary input `n`, iterating `echoMachine` for `n + 5` steps reaches `cfgTermStep n`. -/
theorem emit_step5 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ.succ.succ.succ
      = some (cfgTermStep n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step4 n, Option.bind_some, step_cfgTerm n]

/-- On unary input `n`, iterating `echoMachine` for `n + 6` steps reaches `cfgGate0 n`. -/
theorem emit_step6 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ.succ.succ.succ.succ
      = some (cfgGate0 n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step5 n, Option.bind_some, step_cfgTermStep n]

/-- On unary input `n`, iterating `echoMachine` for `n + 7` steps reaches `cfgGateStep n`. -/
theorem emit_step7 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ.succ.succ.succ.succ.succ
      = some (cfgGateStep n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step6 n, Option.bind_some, step_cfgGate0 n]

/-- On unary input `n`, iterating `echoMachine` for `n + 8` steps reaches `cfgGate1 n`. -/
theorem emit_step8 (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) n.succ.succ.succ.succ.succ.succ.succ.succ
      = some (cfgGate1 n) := by
  rw [Nat.succ_eq_add_one, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ,
      emit_step7 n, Option.bind_some, step_cfgGateStep n]

/-- The echo machine reaches `cfgGate1 n` after `n + 8` steps from its initial configuration on
unary input `n`. -/
theorem emit_run (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n))
      (n.succ.succ.succ.succ.succ.succ.succ.succ) = some (cfgGate1 n) := by
  rw [emit_step8 n]

/-- If `a` iterations of `echoMachine` take `c` to `c'`, then `a + b` iterations from `c` equal
`b` iterations from `c'`. -/
theorem iterStep_append {c c' : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1))} {a b : ℕ}
    (ha : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine c a = some c') :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine c (a + b) = Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine c' b := by
  induction b generalizing c c' with
  | zero => simpa using! ha
  | succ b ih =>
    have hab : a + (b + 1) = (a + b) + 1 := by omega
    rw [hab, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ, ih ha]
    rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ]

/-- Three iterations of `echoMachine` from `cfgGate1 n` reach `cfgRewind n 3`. -/
theorem rewind_base (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgGate1 n) 3 = some (cfgRewind n 3) := by
  rw [show (3 : ℕ) = Nat.succ (Nat.succ (Nat.succ 0)) from by omega]
  rw [Nat.succ_eq_add_one]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ_of_step (step_cfgGate1 n)]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ_of_step (step_cfgRewind1 n)]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ_of_step (step_cfgRewind2 n)]
  rfl

/-- For `3 ≤ k ≤ n + 3`, iterating `echoMachine` for `k` steps from `cfgGate1 n` reaches
`cfgRewind n k`. -/
theorem rewind_run (n k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ n + 3) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgGate1 n) k = some (cfgRewind n k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hthree : k + 1 = 3
    · have hk2 : k = 2 := by omega
      subst hk2
      rw [rewind_base n]
    · have hk3 : 3 ≤ k := by omega
      have hk2 : k ≤ n + 2 := by omega
      rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ, ih hk3 (by omega), Option.bind_some,
        step_cfgRewind n k hk3 hk2]

/-- The echo rewind configuration with an empty left side and a blank head immediately before
the output of `n + 1` ones followed by three zeros. -/
def cfgBlank (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .rewind,
    tapeOf [] (none :: (some true :: (List.replicate n (some true) ++
      [some false, some false, some false])))⟩

/-- The echo configuration in state `Echo.val .back` with an empty left side and a blank head
immediately before the output of `n + 1` ones followed by three zeros. -/
def cfgBack (n : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (10 + 1)) :=
  ⟨Echo.val .back,
    tapeOf [] (none :: (some true :: (List.replicate n (some true) ++
      [some false, some false, some false])))⟩

/-- One step of `echoMachine` takes `cfgRewind n (n + 3)` to `cfgBlank n`. -/
theorem step_cfgRewindLast (n : ℕ) :
    Turing.TM0.step echoMachine (cfgRewind n (n + 3)) = some (cfgBlank n) := by
  simp [cfgRewind, cfgBlank, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_left, List.headI_cons, List.tail_cons, List.tail_append]

/-- One step of `echoMachine` takes `cfgBlank n` to `cfgBack n`. -/
theorem step_cfgBlank (n : ℕ) :
    Turing.TM0.step echoMachine (cfgBlank n) = some (cfgBack n) := by
  simp [cfgBlank, cfgBack, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_write]

/-- One step of `echoMachine` takes `cfgBack n` to `cfgDone n`. -/
theorem step_cfgBack (n : ℕ) :
    Turing.TM0.step echoMachine (cfgBack n) = some (cfgDone n) := by
  simp [cfgBack, cfgDone, Turing.TM0.step, echoMachine, Echo.val, tapeOf_head,
    tapeOf_move_right]

/-- Starting at `cfgGate1 n`, the echo machine reaches `cfgRewind n (n + 3)` after `n + 3`
iterations. -/
theorem rewind_reaches (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgGate1 n) (n + 3) = some (cfgRewind n (n + 3)) := by
  have hmain : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgGate1 n) (n + 3)
      = some (cfgRewind n (n + 3)) := by
    have hk : 3 ≤ n + 3 := by omega
    have hk' : n + 3 ≤ n + 3 := by omega
    exact rewind_run n (n + 3) hk hk'
  exact hmain

/-- Three iterations of `echoMachine` from `cfgRewind n (n + 3)` reach `cfgDone n`. -/
theorem last_steps (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgRewind n (n + 3)) 3 = some (cfgDone n) := by
  rw [show (3 : ℕ) = Nat.succ (Nat.succ (Nat.succ 0)) from by omega]
  rw [Nat.succ_eq_add_one]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ_of_step (step_cfgRewindLast n)]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ_of_step (step_cfgBlank n)]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ_of_step (step_cfgBack n)]
  rfl

/-- On unary input `n`, the echo machine reaches `cfgDone n` after `2 * n + 14` iterations. -/
theorem echo_final (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n)) (2 * n + 14)
      = some (cfgDone n) := by
  have hcount : (2 * n + 14) = (n + 8) + ((n + 3) + 3) := by omega
  rw [hcount]
  have h1 : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n))
      ((n + 8) + ((n + 3) + 3))
        = Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgGate1 n) ((n + 3) + 3) :=
    iterStep_append (emit_run n)
  have h2 : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgGate1 n) ((n + 3) + 3)
      = Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (cfgRewind n (n + 3)) 3 :=
    iterStep_append (rewind_reaches n)
  rw [h1, h2, last_steps n]

/-- The echo machine has no next step from `cfgDone n`. -/
theorem echo_halts_at_done (n : ℕ) :
    Turing.TM0.step echoMachine (cfgDone n) = none := by
  simp [cfgDone, Turing.TM0.step, echoMachine, Echo.val]

/-- Mapping the cell values of `n + 1` ones followed by three zeros yields the encoding of the
width-`n + 1` word `[echoGate]`. -/
theorem echoEncoding_eq (n : ℕ) :
    (some true :: (List.replicate n (some true) ++ [some false, some false, some false])).map
        (fun o => o.getD false)
      = encodeUniformBqpWord (n + 1) [echoGate] := by
  simp [echoEncoding, echoGate, encodeUniformBqpWord, encodeUnaryField,
    encodeFiniteGateCode]
  rw [← replicate_succ' (a := true), List.cons_append]

/-- Reading the head-inclusive right side of `cfgDone n` with bound `n + uniformBqpTimeBound
echoGenerator n + 1` returns the encoding of `(n + 1, [echoGate])`. -/
theorem echo_read (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelReadOutputUntilBlank (n + uniformBqpTimeBound echoGenerator n + 1)
      (cfgDone n).Tape.right₀ = some (encodeUniformBqpWord (n + 1) [echoGate]) := by
  have hlen : (some true :: (List.replicate n (some true) ++
      [some false, some false, some false])).length
        ≤ n + uniformBqpTimeBound echoGenerator n + 1 := by
    simp [echoGenerator, uniformBqpTimeBound, uniformBqpPolynomial]
    omega
  have hnb : ∀ a ∈ (some true :: (List.replicate n (some true) ++
      [some false, some false, some false])), a ≠ none := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [List.mem_replicate] at ha
        rw [ha.2]
        simp
      · rcases List.mem_cons.mp ha with rfl | ha
        · simp
        · rcases List.mem_cons.mp ha with rfl | ha
          · simp
          · rcases List.mem_singleton.mp ha with rfl <;> simp
  simp only [cfgDone]
  rw [tapeOf_right₀]
  simp only [List.headI_cons, List.tail_cons]
  rw [readOutput_of_list _ hlen hnb, echoEncoding_eq n]

/-- The bounded echo generator returns the circuit word `(n + 1, [echoGate])` on input length
`n`. -/
theorem echo_generated (n : ℕ) :
    uniformBqpGeneratedAt echoGenerator n = some (n + 1, [echoGate]) := by
  have ht : 2 * n + 14 ≤ uniformBqpTimeBound echoGenerator n := by
    simp [echoGenerator, uniformBqpTimeBound, uniformBqpPolynomial]
    omega
  have hcfg : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep echoMachine (Turing.TM0.init (uniformBqpUnaryInput n))
      (2 * n + 14) = some (cfgDone n) := echo_final n
  have hstop : Turing.TM0.step echoMachine (cfgDone n) = none := echo_halts_at_done n
  have hread := echo_read n
  have h := Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelGeneratedAt_of_run (g := echoGenerator) (n := n) (t := 2 * n + 14)
    (cfg := cfgDone n) ht hcfg hstop (n + 1) [echoGate] hread
  rwa [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelGeneratedAt_eq] at h

/-- The single-gate word `[echoGate]` is legal on a register of width `n + 1`. -/
theorem echo_word_legal (n : ℕ) : finiteWordLegal (n + 1) [echoGate] = true := by
  simp [echoGate, finiteWordLegal, finiteCodeLegal]

/-- Every circuit word successfully returned by `echoGenerator` is legal at its reported width. -/
theorem echo_wellformed : generatorWellformed echoGenerator := by
  intro n q gs h
  rw [echo_generated n] at h
  have h' : (n + 1, [echoGate]) = (q, gs) := by injection h
  cases h'
  exact echo_word_legal n

/-- For a bit-tape machine with control type `Fin (10 + 1)`, `BitMachineAfter` agrees with
`iterStep` applied to the initial input configuration. -/
theorem bitMachineAfter_eq_iterStep (m : Turing.TM0.Machine (Option Bool) (Fin (10 + 1)))
    (input : List (Option Bool)) (t : ℕ) :
    BitMachineAfter m input t = Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep m (Turing.TM0.init input) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [BitMachineAfter, ih, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ]

/-- The echo machine satisfies `BitMachineHaltsAt` on unary input `n` at time `2 * n + 14`. -/
theorem echo_halts_at (n : ℕ) :
    BitMachineHaltsAt echoMachine (uniformBqpUnaryInput n) (2 * n + 14) := by
  refine ⟨cfgDone n, ?_, echo_halts_at_done n⟩
  simpa only [bitMachineAfter_eq_iterStep] using! echo_final n

/-- The echo generator's machine halts after a finite number of steps on every unary input. -/
theorem echo_halts : generatorHaltsEffectively echoGenerator := by
  intro n
  exact ⟨2 * n + 14, echo_halts_at n⟩

/-- The echo generator's machine halts within a polynomial number of steps on every unary input. -/
theorem echo_clocked : generatorClocked echoGenerator := by
  refine ⟨14, 1, ?_⟩
  intro n
  refine ⟨2 * n + 14, ?_, echo_halts_at n⟩
  simp [echoGenerator, uniformBqpTimeBound, uniformBqpPolynomial]
  omega

/-- The echo generator halts on every unary input, and the encoding length of its totalized
generated word has a polynomial bound. -/
theorem echo_bitTm_backend : bitTmBackendPremise echoGenerator := by
  refine ⟨echo_halts, ?_⟩
  refine ⟨4, 1, ?_⟩
  intro n
  have h := echo_generated n
  simp [uniformBqpGeneratedTotal, h, echoEncoding, encodeUniformBqpWord, encodeUnaryField,
    encodeFiniteGateCode, echoGate, uniformBqpPolynomial]
  omega

/-- The echo generator successfully returns a legal word on every input length, with a halting
witness and the required time, gate-count, width, and encoding-length bounds. -/
theorem echo_valid : uniformBqpGeneratorValid echoGenerator := by
  intro n
  have hgen := echo_generated n
  have htime : 2 * n + 14 ≤ uniformBqpTimeBound echoGenerator n := by
    simp [echoGenerator, uniformBqpTimeBound, uniformBqpPolynomial]
    omega
  have hword : [echoGate].length ≤ uniformBqpWordBound echoGenerator n := by
    simp [echoGenerator, uniformBqpWordBound, uniformBqpPolynomial]
  have hspace : n + 1 ≤ uniformBqpSpaceBound echoGenerator n := by
    simp [echoGenerator, uniformBqpSpaceBound, uniformBqpPolynomial]
  have henc : (encodeUniformBqpWord (n + 1) [echoGate]).length
      ≤ n + uniformBqpTimeBound echoGenerator n := by
    simp [echoGenerator, uniformBqpTimeBound, uniformBqpPolynomial, echoEncoding,
      encodeUniformBqpWord, encodeUnaryField, encodeFiniteGateCode, echoGate]
    omega
  exact ⟨n + 1, [echoGate], hgen, ⟨2 * n + 14, htime, echo_halts_at n⟩, echo_word_legal n,
    hword, hspace, henc⟩

/-- Any two move transitions of `echoMachine` from the same control state have the same
direction, regardless of the scanned symbols. -/
theorem echo_unidirectional : tm0Unidirectional echoMachine := by
  intro q a b r s har hbs hmr hms
  have hq := q.isLt
  rcases q with ⟨v, hv⟩
  interval_cases v
  · simp only [echoMachine, Echo.val] at har hbs
    by_cases ha : a = some true
    · simp only [ha, if_true] at har
      cases har
      by_cases hb : b = some true
      · simp only [hb, if_true] at hbs
        cases hbs
        rfl
      · by_cases hb0 : b = none
        · simp only [hb, hb0, if_false, if_true] at hbs
          cases hbs
          simp at hms
        · simp only [hb, hb0, if_false, if_false] at hbs
          simp at hbs
    · by_cases ha0 : a = none
      · simp only [ha, ha0, if_false, if_true] at har
        cases har
        simp at hmr
      · simp only [ha, ha0, if_false, if_false] at har
        simp at har
  · simp only [echoMachine, Echo.val] at har
    cases har
    simp at hmr
  · simp only [echoMachine, Echo.val] at har hbs
    cases har
    cases hbs
    rfl
  · simp only [echoMachine, Echo.val] at har
    cases har
    simp at hmr
  · simp only [echoMachine, Echo.val] at har hbs
    cases har
    cases hbs
    rfl
  · simp only [echoMachine, Echo.val] at har
    cases har
    simp at hmr
  · simp only [echoMachine, Echo.val] at har hbs
    cases har
    cases hbs
    rfl
  · simp only [echoMachine, Echo.val] at har
    cases har
    simp at hmr
  · simp only [echoMachine, Echo.val] at har hbs
    by_cases ha : a = none
    · simp only [ha, if_true] at har
      cases har
      simp at hmr
    · simp only [ha, if_false] at har
      cases har
      by_cases hb : b = none
      · simp only [hb, if_true] at hbs
        cases hbs
        simp at hms
      · simp only [hb, if_false] at hbs
        cases hbs
        rfl
  · simp only [echoMachine, Echo.val] at har hbs
    cases har
    cases hbs
    rfl
  · simp only [echoMachine, Echo.val] at har
    simp at har

/-- The echo generator satisfies `generatorNormalForm`, the unidirectionality condition on its
underlying machine. -/
theorem echo_normal_form : generatorNormalForm echoGenerator := by
  exact echo_unidirectional

/-- Duplicating `(n + 1, [echoGate])` gives width `2 * (n + 1)` and the two-gate list
`[echoGate, .h (n + 1)]`. -/
theorem echo_duplicate (n : ℕ) :
    duplicateWord (n + 1) [echoGate] = (2 * (n + 1), [echoGate, .h (n + 1)]) := by
  simp [duplicateWord, echoGate,
      Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode, Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padWire]

/-- The doubled circuit word obtained by duplicating `(n + 1, [echoGate])` is legal. -/
theorem echo_duplicate_legal (n : ℕ) :
    finiteWordLegal (duplicateWord (n + 1) [echoGate]).1
      (duplicateWord (n + 1) [echoGate]).2 = true := by
  rw [echo_duplicate]
  have h1 : 0 < 2 * (n + 1) := by omega
  have h2 : n + 1 < 2 * (n + 1) := by omega
  simp [finiteWordLegal, finiteCodeLegal, echoGate, h1, h2]

/-- Duplicating the echo word gives width `2 * (n + 1)` and a gate list of length two. -/
theorem echo_duplicate_size (n : ℕ) :
    (duplicateWord (n + 1) [echoGate]).1 = 2 * (n + 1) ∧
      (duplicateWord (n + 1) [echoGate]).2.length = 2 := by
  rw [echo_duplicate]
  simp

/-- In the complex numbers, the inverse of `Real.sqrt 2` equals `Real.sqrt 2 / 2`. -/
theorem inv_sqrt2_half : ((Real.sqrt 2 : ℂ))⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  have h2 : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := sqrt2_sq
  have h0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)]
  field_simp
  exact h2.symm

/-- The finite-digit amplitude with real numerator `-1` when `a && b` and `1` otherwise, zero
imaginary numerator, a square-root-of-two factor, and denominator two equals `Hadamard a b`. -/
theorem hadamard_finiteDigit (a b : Bool) :
    finiteDigitVal ⟨(if a && b then -1 else 1 : ℤ), 0, true, 1⟩ = Hadamard a b := by
  by_cases ha : a = true <;> by_cases hb : b = true <;>
    simp only [Hadamard, Matrix.of_apply, ha, hb, Bool.false_and, Bool.true_and,
      ite_true, inv_sqrt2_half] <;>
    simp [finiteDigitVal] <;> ring

/-- The finite-digit amplitude with real numerator `1` when `b = !a` and `0` otherwise, zero
imaginary numerator, and no square-root or denominator factor equals `PauliX a b`. -/
theorem pauliX_finiteDigit (a b : Bool) :
    finiteDigitVal ⟨(if b = !a then 1 else 0 : ℤ), 0, false, 0⟩ = PauliX a b := by
  cases a <;> cases b <;>
    simp only [PauliX, permMatrix, Matrix.of_apply, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, Bool.true_eq, ite_true, ite_false] <;>
    simp [finiteDigitVal]

/-- The finite-digit amplitude with real numerator `1` exactly when `i = Function.update j t (j
t ^^ j c)` and `0` otherwise, zero imaginary numerator, and no square-root or denominator
factor equals the corresponding `cnotGate n c t` matrix entry. -/
theorem cnot_finiteDigit {n : ℕ} (c t : Fin n) (i j : Reg n) :
    finiteDigitVal ⟨(if i = Function.update j t (j t ^^ j c) then 1 else 0 : ℤ), 0, false, 0⟩
      = cnotGate n c t i j := by
  by_cases h : i = Function.update j t (j t ^^ j c)
  · simp [cnotGate, permMatrix, Matrix.of_apply, h, finiteDigitVal]
  · simp [cnotGate, permMatrix, Matrix.of_apply, h, finiteDigitVal]

/-- The complex exponential of `I * (pi / 4)` equals `(Real.sqrt 2 / 2) * (1 + I)`. -/
theorem exp_pi_div_four : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
    = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Real.exp_zero,
      Real.cos_pi_div_four]
    norm_num
  · rw [Complex.exp_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Real.exp_zero,
      Real.sin_pi_div_four]
    norm_num

/-- The complex exponential of `I * (-(pi / 4))` equals `(Real.sqrt 2 / 2) * (1 - I)`. -/
theorem exp_neg_pi_div_four : Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I)
    = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.zero_re,
      Complex.zero_im, Real.exp_zero, Real.cos_neg, Real.cos_pi_div_four]
    norm_num
  · rw [Complex.exp_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.zero_re,
      Complex.zero_im, Real.exp_zero, Real.sin_neg, Real.sin_pi_div_four]
    norm_num

/-- Dividing the complex embedding of `Real.sqrt 2` by the embedded natural number two equals
the complex embedding of the real quotient `Real.sqrt 2 / 2`. -/
theorem ofReal_sqrt2_div_two : (Real.sqrt 2 : ℂ) / ((2 : ℕ) : ℂ)
    = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  have h := Complex.ofReal_div (Real.sqrt 2) (2 : ℝ)
  have h2 : ((2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2, ← h]

/-- The finite-digit amplitude with numerators `1` and `1`, a square-root-of-two factor, and
denominator two has value `(Real.sqrt 2 / 2) * (1 + I)`. -/
theorem digit_t_diag : finiteDigitVal ⟨1, 1, true, 1⟩
    = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  simp only [finiteDigitVal, ite_true, mul_div_assoc, Nat.pow_one]
  rw [ofReal_sqrt2_div_two]
  ring

/-- The finite-digit amplitude with numerators `1` and `-1`, a square-root-of-two factor, and
denominator two has value `(Real.sqrt 2 / 2) * (1 - I)`. -/
theorem digit_tadj_diag : finiteDigitVal ⟨1, -1, true, 1⟩
    = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
  simp only [finiteDigitVal, ite_true, mul_div_assoc, Nat.pow_one]
  rw [ofReal_sqrt2_div_two]
  ring

/-- Every matrix entry of `tGate` has an exact `FiniteDigitAmplitude` representation. -/
theorem tGate_finiteDigit (a b : Bool) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = tGate a b := by
  cases a <;> cases b <;>
    simp only [tGate, Rz, Matrix.diagonal_apply, Bool.false_eq_true, Bool.true_eq,
      ite_true, ite_false]
  · exact ⟨⟨1, 0, false, 0⟩, by simp [finiteDigitVal]⟩
  · exact ⟨⟨0, 0, false, 0⟩, by simp [finiteDigitVal]⟩
  · exact ⟨⟨0, 0, false, 0⟩, by simp [finiteDigitVal]⟩
  · refine ⟨⟨1, 1, true, 1⟩, ?_⟩
    rw [exp_pi_div_four, digit_t_diag]

/-- Every matrix entry of `tGateAdj` has an exact `FiniteDigitAmplitude` representation. -/
theorem tGateAdj_finiteDigit (a b : Bool) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = tGateAdj a b := by
  cases a <;> cases b <;>
    simp only [tGateAdj, Rz, Matrix.diagonal_apply, Bool.false_eq_true, Bool.true_eq,
      ite_true, ite_false]
  · exact ⟨⟨1, 0, false, 0⟩, by simp [finiteDigitVal]⟩
  · exact ⟨⟨0, 0, false, 0⟩, by simp [finiteDigitVal]⟩
  · exact ⟨⟨0, 0, false, 0⟩, by simp [finiteDigitVal]⟩
  · refine ⟨⟨1, -1, true, 1⟩, ?_⟩
    rw [exp_neg_pi_div_four, digit_tadj_diag]

/-- Every matrix entry of a finite gate code legal at width `n` has an exact
`FiniteDigitAmplitude` representation. -/
theorem fixedGate_finiteDigit {n : ℕ} (g : FiniteGateCode)
    (hg : finiteCodeLegal n g = true) (i j : Reg n) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = finiteCodeMatrix n g i j := by
  cases g with
  | h w =>
    have hw : w < n := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    by_cases hsame : ∀ k : Fin n, k ≠ (⟨w, hw⟩ : Fin n) → i k = j k
    case pos =>
      simp only [if_pos hsame]
      refine ⟨⟨(if i ⟨w, hw⟩ && j ⟨w, hw⟩ then -1 else 1 : ℤ), 0, true, 1⟩, ?_⟩
      rw [hadamard_finiteDigit]
    case neg =>
      exact ⟨⟨0, 0, false, 0⟩, by simp [if_neg hsame, finiteDigitVal]⟩
  | x w =>
    have hw : w < n := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    by_cases hsame : ∀ k : Fin n, k ≠ (⟨w, hw⟩ : Fin n) → i k = j k
    case pos =>
      simp only [if_pos hsame]
      refine ⟨⟨(if j ⟨w, hw⟩ = !i ⟨w, hw⟩ then 1 else 0 : ℤ), 0, false, 0⟩, ?_⟩
      rw [pauliX_finiteDigit]
    case neg =>
      exact ⟨⟨0, 0, false, 0⟩, by simp [if_neg hsame, finiteDigitVal]⟩
  | t w =>
    have hw : w < n := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    by_cases hsame : ∀ k : Fin n, k ≠ (⟨w, hw⟩ : Fin n) → i k = j k
    case pos =>
      simp only [if_pos hsame]
      exact ⟨(tGate_finiteDigit (i ⟨w, hw⟩) (j ⟨w, hw⟩)).choose,
        (tGate_finiteDigit (i ⟨w, hw⟩) (j ⟨w,hw⟩)).choose_spec⟩
    case neg =>
      exact ⟨⟨0, 0, false, 0⟩, by simp [if_neg hsame, finiteDigitVal]⟩
  | tdg w =>
    have hw : w < n := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    by_cases hsame : ∀ k : Fin n, k ≠ (⟨w, hw⟩ : Fin n) → i k = j k
    case pos =>
      simp only [if_pos hsame]
      exact ⟨(tGateAdj_finiteDigit (i ⟨w, hw⟩) (j ⟨w, hw⟩)).choose,
        (tGateAdj_finiteDigit (i ⟨w, hw⟩) (j ⟨w,hw⟩)).choose_spec⟩
    case neg =>
      exact ⟨⟨0, 0, false, 0⟩, by simp [if_neg hsame, finiteDigitVal]⟩
  | cx c t =>
    have hct : c < n ∧ t < n ∧ c ≠ t := by simpa [finiteCodeLegal] using! hg
    obtain ⟨hc, ht, hne⟩ := hct
    have hct' : c < n ∧ t < n ∧ c ≠ t := ⟨hc, ht, hne⟩
    simp only [finiteCodeMatrix, dif_pos hct']
    refine ⟨⟨(if i = Function.update j ⟨t, ht⟩ (j ⟨t, ht⟩ ^^ j ⟨c, hc⟩) then 1 else 0 : ℤ),
      0, false, 0⟩, ?_⟩
    rw [cnot_finiteDigit]

/-- A legal finite gate word satisfies `finiteDigitBackendPremise`: every entry of each gate
matrix has an exact finite-digit representation. -/
theorem legalWord_finiteDigitBackend {n : ℕ} (gs : List FiniteGateCode)
    (hleg : finiteWordLegal n gs = true) :
    finiteDigitBackendPremise (n, gs) := by
  refine ⟨hleg, ?_⟩
  intro g hg i j
  have hgl : finiteCodeLegal n g = true := by
    rw [← List.all_eq_true.mp hleg]
    exact hg
  exact fixedGate_finiteDigit g hgl i j

/-- The width-`n + 1` echo word `[echoGate]` is legal and every entry of its gate matrix has an
exact finite-digit representation. -/
theorem echo_finiteDigitBackend (n : ℕ) :
    finiteDigitBackendPremise (n + 1, [echoGate]) := by
  refine ⟨echo_word_legal n, ?_⟩
  intro g hg i j
  have hg' : g = echoGate := by
    simpa only [List.mem_singleton] using! hg
  subst hg'
  have hleg : finiteCodeLegal (n + 1) echoGate = true := by
    simp [finiteCodeLegal, echoGate]
  exact fixedGate_finiteDigit echoGate hleg i j

/-- The echo family's running time, gate count, and register width satisfy the respective time,
word, and space bounds of `echoGenerator`. Its encoded output length is at most `n +
uniformBqpTimeBound echoGenerator n`. -/
theorem echo_machine_time_space_bounds (n : ℕ) :
    echoSteps n ≤ uniformBqpTimeBound echoGenerator n ∧
      (echoWord n).2.length ≤ uniformBqpWordBound echoGenerator n ∧
      (echoWord n).1 ≤ uniformBqpSpaceBound echoGenerator n ∧
      (encodeUniformBqpWord (echoWord n).1 (echoWord n).2).length
        ≤ n + uniformBqpTimeBound echoGenerator n := by
  have h1 : echoSteps n = 2 * n + 14 := rfl
  have h2 : uniformBqpTimeBound echoGenerator n = 14 * (n + 1) := by
    simp [uniformBqpTimeBound, uniformBqpPolynomial, echoGenerator]
  have h3 : uniformBqpWordBound echoGenerator n = n + 1 := by
    simp [uniformBqpWordBound, uniformBqpPolynomial, echoGenerator]
  have h4 : uniformBqpSpaceBound echoGenerator n = 2 * (n + 1) := by
    simp [uniformBqpSpaceBound, uniformBqpPolynomial, echoGenerator]
  have h5 : (echoWord n).2.length = 1 := rfl
  have h6 : (echoWord n).1 = n + 1 := rfl
  have h6' : (echoWord n).2 = [echoGate] := rfl
  have h7 : (encodeUniformBqpWord (n + 1) [echoGate]).length = n + 4 := by
    simp [encodeUniformBqpWord, encodeUnaryField, echoGate, encodeFiniteGateCode,
      List.length_append, List.length_replicate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, h2]
    omega
  · rw [h3, h5]
    omega
  · rw [h4, h6]
    omega
  · rw [h6, h6', h7, h2]
    omega

/-- For a legal gate word, `finiteWordRun` on the basis state `Ket x` succeeds and returns
`uniformBqpRun q gs x`. -/
theorem finiteWordRun_eq_uniformBqpRun {q : ℕ} {gs : List FiniteGateCode} (x : Reg q)
    (h : finiteWordLegal q gs = true) :
    finiteWordRun q gs (Ket x) = some (uniformBqpRun q gs x) := by
  simp [finiteWordRun, h, uniformBqpRun]

/-- Decoding `echoEncoding n` returns `echoWord n`. -/
theorem echo_bitEncoding_transport (n : ℕ) :
    decodeUniformBqpWord (echoEncoding n) = some (echoWord n) := by
  rw [echoEncoding, echoWord, decode_encodeUniformBqpWord]

/-- Decoding `echoEncoding n` returns the legal word `echoWord n`, whose gate list has length
one and whose register width is `n + 1`. -/
theorem echo_native_output_transport (n : ℕ) :
    decodeUniformBqpWord (echoEncoding n) = some (echoWord n) ∧
      (echoWord n).2.length = 1 ∧
      (echoWord n).1 = n + 1 ∧
      finiteWordLegal (echoWord n).1 (echoWord n).2 = true :=
  ⟨echo_bitEncoding_transport n, rfl, rfl, echo_word_legal n⟩

/-- Collects the exact finite-digit backend, equality of `uniformBqpAcceptProb` with the
identity-oracle circuit's output-event probability, and the echo family's resource bounds.
For every `n` and basis input `x`, it also gives agreement of `finiteWordRun` with
`uniformBqpRun` and decoding of `echoEncoding n`. -/
theorem clause5_complete :
    ∀ (n : ℕ) (x : Reg (n + 1)),
      finiteDigitBackendPremise (n + 1, [echoGate]) ∧
      uniformBqpAcceptProb (n + 1) [echoGate] x
        = MeasureProb (Run (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
            (finiteCodeCircuit (n + 1) [echoGate]) (Ket x))
          (uniformBqpOutputEvent (n + 1)) ∧
      echoSteps n ≤ uniformBqpTimeBound echoGenerator n ∧
      (echoWord n).2.length ≤ uniformBqpWordBound echoGenerator n ∧
      (echoWord n).1 ≤ uniformBqpSpaceBound echoGenerator n ∧
      (encodeUniformBqpWord (echoWord n).1 (echoWord n).2).length
        ≤ n + uniformBqpTimeBound echoGenerator n ∧
      finiteWordRun (echoWord n).1 (echoWord n).2 (Ket x)
        = some (uniformBqpRun (echoWord n).1 (echoWord n).2 x) ∧
      decodeUniformBqpWord (echoEncoding n) = some (echoWord n) := by
  intro n x
  have hbounds := echo_machine_time_space_bounds n
  have hleg : finiteWordLegal (echoWord n).1 (echoWord n).2 = true := echo_word_legal n
  have hrun : finiteWordRun (echoWord n).1 (echoWord n).2 (Ket x)
      = some (uniformBqpRun (echoWord n).1 (echoWord n).2 x) :=
    finiteWordRun_eq_uniformBqpRun x hleg
  refine ⟨echo_finiteDigitBackend n, rfl, hbounds.1, hbounds.2.1, hbounds.2.2.1,
    hbounds.2.2.2, hrun, echo_bitEncoding_transport n⟩

/-- Encodes a program control state as a finite machine state using `genEncode`, with the result
embedded by `Fin.castSucc` into the larger control type. -/
def genVal (P : GateProgram) (c : PControl P) :
    Fin (genControlSize P.gateCount (P.bitCount + 2) + 1) :=
  Fin.castSucc (genEncode P.gateCount (P.bitCount + 2) c)

/-- Iterates the program's core Turing machine from `cfg`, returning `some cfg` at time zero and
propagating termination through `Option.bind`. -/
def genCoreIter (P : GateProgram) (cfg : Turing.TM0.Cfg (Option Bool) (PControl P)) : ℕ →
    Option (Turing.TM0.Cfg (Option Bool) (PControl P))
  | 0 => some cfg
  | t + 1 => (genCoreIter P cfg t).bind (Turing.TM0.step (genCoreMachine P))

/-- Iterating the core generator for zero steps returns the starting configuration. -/
@[simp] theorem genCoreIter_zero (P : GateProgram)
    (cfg : Turing.TM0.Cfg (Option Bool) (PControl P)) :
    genCoreIter P cfg 0 = some cfg := rfl

/-- Iteration for `t + 1` steps performs one core-machine step after the optional result of `t`
steps. -/
theorem genCoreIter_succ (P : GateProgram)
    (cfg : Turing.TM0.Cfg (Option Bool) (PControl P)) (t : ℕ) :
    genCoreIter P cfg (t + 1) =
      (genCoreIter P cfg t).bind (Turing.TM0.step (genCoreMachine P)) := rfl

/-- If the core machine steps from `cfg0` to `next`, iteration from `cfg0` for `t + 1` steps
equals iteration from `next` for `t` steps. -/
theorem genCoreIter_succ_of_step (P : GateProgram)
    {cfg0 next : Turing.TM0.Cfg (Option Bool) (PControl P)} {t : ℕ}
    (hstep : Turing.TM0.step (genCoreMachine P) cfg0 = some next) :
    genCoreIter P cfg0 (t + 1) = genCoreIter P next t := by
  induction t with
  | zero =>
    show (genCoreIter P cfg0 0).bind (Turing.TM0.step (genCoreMachine P))
      = genCoreIter P next 0
    simp [genCoreIter, hstep]
  | succ t ih =>
    show (genCoreIter P cfg0 (t + 1)).bind (Turing.TM0.step (genCoreMachine P))
      = genCoreIter P next (t + 1)
    rw [ih, genCoreIter_succ]

/-- Computes a step of the encoded generator from a control of the form `genVal P c` by applying
the instruction returned by `genStepCore` to the tape and encoding the resulting control. -/
theorem genStep (P : GateProgram) (c : PControl P) (tape : Tape (Option Bool)) :
    Turing.TM0.step (genMachine P) ⟨genVal P c, tape⟩
      = (genStepCore P c tape.head).map (fun p :
          PControl P × Turing.TM0.Stmt (Option Bool) =>
          (⟨genVal P p.1, match p.2 with
            | Turing.TM0.Stmt.move d => tape.move d
            | Turing.TM0.Stmt.write b => tape.write b⟩ :
            Turing.TM0.Cfg (Option Bool)
              (Fin (genControlSize P.gateCount (P.bitCount + 2) + 1)))) := by
  have hlt : (genVal P c).val < genControlSize P.gateCount (P.bitCount + 2) := by
    have h := (genEncode P.gateCount (P.bitCount + 2) c).isLt
    simpa [genVal] using! h
  have hdec : genDecode P.gateCount (P.bitCount + 2) ⟨(genVal P c).val, hlt⟩ = c := by
    have hval : (genVal P c).val = (genEncode P.gateCount (P.bitCount + 2) c).val := by
      simp [genVal]
    have hfin : ⟨(genVal P c).val, hlt⟩
        = (genEncode P.gateCount (P.bitCount + 2) c) := by
      apply Fin.ext
      exact hval
    rw [hfin, genDecode_encode]
  unfold Turing.TM0.step
  simp only [genMachine, dif_pos hlt]
  rw [hdec]
  cases hstep : genStepCore P c tape.head with
  | none => simp [hstep]
  | some p =>
    simp only [hstep, Option.map_some, genVal]
    first
    | rfl
    | (cases p.2 <;> rfl)
    | (congr 1 <;> rfl)
    | simp

/-- Encoding a core configuration commutes with one generator step, leaving the tape unchanged
by the encoding map. -/
theorem genStep_transport (P : GateProgram)
    (c : Turing.TM0.Cfg (Option Bool) (PControl P)) :
    Turing.TM0.step (genMachine P) ⟨genVal P c.q, c.Tape⟩
      = (Turing.TM0.step (genCoreMachine P) c).map (fun d => ⟨genVal P d.q, d.Tape⟩) := by
  have h1 : Turing.TM0.step (genMachine P) ⟨genVal P c.q, c.Tape⟩
      = (genStepCore P c.q c.Tape.head).map (fun p :
          PControl P × Turing.TM0.Stmt (Option Bool) =>
          (⟨genVal P p.1, match p.2 with
            | Turing.TM0.Stmt.move d => c.Tape.move d
            | Turing.TM0.Stmt.write b => c.Tape.write b⟩ :
            Turing.TM0.Cfg (Option Bool)
              (Fin (genControlSize P.gateCount (P.bitCount + 2) + 1)))) := by
    exact genStep P c.q c.Tape
  have h2 : (Turing.TM0.step (genCoreMachine P) c).map
        (fun d : Turing.TM0.Cfg (Option Bool) (PControl P) =>
          (⟨genVal P d.q, d.Tape⟩ : Turing.TM0.Cfg (Option Bool)
            (Fin (genControlSize P.gateCount (P.bitCount + 2) + 1))))
      = (genStepCore P c.q c.Tape.head).map (fun p :
          PControl P × Turing.TM0.Stmt (Option Bool) =>
          (⟨genVal P p.1, match p.2 with
            | Turing.TM0.Stmt.move d => c.Tape.move d
            | Turing.TM0.Stmt.write b => c.Tape.write b⟩ :
            Turing.TM0.Cfg (Option Bool)
              (Fin (genControlSize P.gateCount (P.bitCount + 2) + 1)))) := by
    unfold Turing.TM0.step
    simp only [genCoreMachine]
    rw [Option.map_map]
    congr 1
    funext p
    simp only [Function.comp_apply]
    first
    | rfl
    | (cases p.2 <;> rfl)
    | (congr 1 <;> rfl)
    | simp
  rw [h1, h2]

/-- Mapping the result of an optional computation commutes with binding its input option. -/
theorem option_bind_map' {α β γ : Type} (x : Option α) (y : α → Option β) (f : β → γ) :
    x.bind (fun a => (y a).map f) = (x.bind y).map f := by
  cases x with
  | none => rfl
  | some a => cases y a <;> rfl

/-- Iteration of the encoded generator agrees with core iteration followed by encoding the
resulting control state. -/
theorem genCoreIter_transfer (P : GateProgram)
    (cfg : Turing.TM0.Cfg (Option Bool) (PControl P)) (t : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (genMachine P) ⟨genVal P cfg.q, cfg.Tape⟩ t
      = (genCoreIter P cfg t).map (fun c => ⟨genVal P c.q, c.Tape⟩) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ, ih, genCoreIter_succ]
    rw [Option.bind_map]
    have hfun :
        (Turing.TM0.step (genMachine P) ∘
            (fun c : Turing.TM0.Cfg (Option Bool) (PControl P) => ⟨genVal P c.q, c.Tape⟩))
        = (fun c : Turing.TM0.Cfg (Option Bool) (PControl P) =>
            (Turing.TM0.step (genCoreMachine P) c).map (fun d => ⟨genVal P d.q, d.Tape⟩)) := by
      funext c
      exact genStep_transport P c
    rw [hfun]
    rw [option_bind_map']

/-- The scan control with counter `min k P.gateCount` and bit index zero. The parameter `n` does
not affect this control. -/
def genCtrlScan (P : GateProgram) (n k : ℕ) : PControl P :=
  ⟨.scan, ⟨min k P.gateCount, by omega⟩, ⟨0, by omega⟩⟩

/-- The initial core-generator configuration, with scan counter zero and a tape containing `n`
true cells starting at the head. -/
def genCfgInit (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨genCtrlScan P n 0, tapeOf [] (List.replicate n (some true))⟩

/-- The scan configuration with `k` true cells to the left and `n - k` true cells starting at
the head, using the capped scan counter. -/
def genCfgScan (P : GateProgram) (n k : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨genCtrlScan P n k,
    tapeOf (List.replicate k (some true)) (List.replicate (n - k) (some true))⟩

/-- The mark configuration with `n` true cells to the left and a true cell under the head, after
extending the unary width field. -/
def genCfgMark (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.mark, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf (List.replicate n (some true)) [some true]⟩

/-- The term configuration with `n + 1` true cells to the left and the head on a blank cell
where the delimiter will be written. -/
def genCfgTerm (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.term, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf (some true :: List.replicate n (some true)) []⟩

/-- The configuration in phase `afterTerm`, with `n + 1` true cells to the left and the false
delimiter under the head. -/
def genCfgAfterTerm (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.afterTerm, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf (some true :: List.replicate n (some true)) [some false]⟩

/-- The number of encoded bits in the program prefix of length `min n P.gateCount`. -/
def genBitCount (P : GateProgram) (n : ℕ) : ℕ := P.prefixBitCount (min n P.gateCount)

/-- The encoded bits of the program prefix of length `min n P.gateCount`. -/
def genBits (P : GateProgram) (n : ℕ) : List Bool := P.prefixBits (min n P.gateCount)

/-- The output tape cells consisting of `n + 1` true cells, a false delimiter, and the encoded
program-prefix bits, all represented as nonblank symbols. -/
def genWordCells (P : GateProgram) (n : ℕ) : List (Option Bool) :=
  List.replicate (n + 1) (some true) ++ (some false :: (genBits P n).map (fun b => some b))

/-- The length of the output cell list `genWordCells P n`. -/
def genWordLength (P : GateProgram) (n : ℕ) : ℕ := (genWordCells P n).length

/-- The output cell count is `n + 1` plus the number of encoded prefix bits and one delimiter
cell. -/
theorem genWordCells_length (P : GateProgram) (n : ℕ) :
    (genWordCells P n).length = (n + 1) + ((genBits P n).length + 1) := by
  have h1 : (List.replicate (n + 1) (some true)).length = n + 1 := by simp
  have h2 : (some false :: (genBits P n).map (fun b => some b)).length
      = (genBits P n).length + 1 := by simp
  rw [genWordCells, List.length_append, h1, h2]

/-- The generator's output cell list is nonempty for every program and input length. -/
theorem genWordCells_ne_nil (P : GateProgram) (n : ℕ) : genWordCells P n ≠ [] := by
  intro h
  have h0 : (genWordCells P n).length = 0 := by rw [h]; rfl
  rw [genWordCells_length] at h0
  omega

/-- The cells to the left during bit emission: the first `j` encoded bits in reverse order,
followed by the false delimiter and `n + 1` true cells. -/
def genEmitLeft (P : GateProgram) (n j : ℕ) : List (Option Bool) :=
  ((genBits P n).take j).reverse.map (fun b => some b) ++
    (some false :: some true :: List.replicate n (some true))

/-- The configuration in phase `emitWrite` at bit index `j`, with `genEmitLeft P n j` to the
left and a blank cell under the head. The index may equal the total encoded bit count. -/
def genCfgWrite (P : GateProgram) (n j : ℕ) (hj : j ≤ genBitCount P n) :
    Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.emitWrite, ⟨min n P.gateCount, by omega⟩, ⟨j, by
      have hle : genBitCount P n ≤ P.bitCount := by
        simp [genBitCount]
        exact P.prefixBitCount_le (min n P.gateCount)
      omega⟩⟩,
    tapeOf (genEmitLeft P n j) []⟩

/-- The initial bit-emission configuration, given by `genCfgWrite` at bit index zero. -/
def genCfgEmit (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  genCfgWrite P n 0 (by omega)

/-- The configuration in phase `emitAdvance` at a valid bit index `j`, with the emitted bit
under the head and the preceding output cells to the left. -/
def genCfgAdv (P : GateProgram) (n j : ℕ) (hj : j < genBitCount P n) :
    Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.emitAdvance, ⟨min n P.gateCount, by omega⟩, ⟨j, by
      have hle : genBitCount P n ≤ P.bitCount := by
        simp [genBitCount]
        exact P.prefixBitCount_le (min n P.gateCount)
      omega⟩⟩,
    tapeOf (genEmitLeft P n j) ((genBits P n).getD j false :: [])⟩

/-- The rewind configuration with capped program-prefix counter, bit index zero, and tape
represented by the supplied left and right lists. -/
def genCfgRewind (P : GateProgram) (n : ℕ) (l : List (Option Bool))
    (r : List (Option Bool)) :
    Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.rewind, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩, tapeOf l r⟩

/-- The rewind configuration with the encoded bit at index `j` under the head and `genEmitLeft P
n j` to the left. -/
def genCfgRewindStart (P : GateProgram) (n : ℕ) (j : ℕ) (hj : j < genBitCount P n) :
    Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.rewind, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf (genEmitLeft P n j) ((genBits P n).getD j false :: [])⟩

/-- The rewind configuration used for an empty bit encoding, with the head on the false
delimiter and `n + 1` true cells to the left. -/
def genCfgRewindEmpty (P : GateProgram) (n : ℕ) :
    Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.rewind, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf (some true :: List.replicate n (some true)) [some false]⟩

/-- The rewind configuration with no listed left cells and the head on the blank immediately
before the complete output word. -/
def genCfgRewindEnd (P : GateProgram) (n : ℕ) :
    Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.rewind, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf [] (none :: genWordCells P n)⟩

/-- The done configuration with the head at the start of `genWordCells P n` and a blank cell
listed to the left. -/
def genCfgDone (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.done, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf [none] (genWordCells P n)⟩

/-- The configuration in phase `back`, with the head on the blank immediately before the
complete output word. -/
def genCfgBack (P : GateProgram) (n : ℕ) : Turing.TM0.Cfg (Option Bool) (PControl P) :=
  ⟨⟨.back, ⟨min n P.gateCount, by omega⟩, ⟨0, by omega⟩⟩,
    tapeOf [] (none :: genWordCells P n)⟩

/-- The encoded generator's transition function at `genVal P c` is the core transition with its
next control encoded by `genVal`. -/
theorem genStepRaw (P : GateProgram) (c : PControl P) (a : Option Bool) :
    genMachine P (genVal P c) a
      = (genStepCore P c a).map (fun p => (genVal P p.1, p.2)) := by
  have hlt : (genVal P c).val < genControlSize P.gateCount (P.bitCount + 2) := by
    have h := (genEncode P.gateCount (P.bitCount + 2) c).isLt
    simpa [genVal] using! h
  have hdec : genDecode P.gateCount (P.bitCount + 2) ⟨(genVal P c).val, hlt⟩ = c := by
    have hval : (genVal P c).val = (genEncode P.gateCount (P.bitCount + 2) c).val := by
      simp [genVal]
    have hfin : ⟨(genVal P c).val, hlt⟩
        = (genEncode P.gateCount (P.bitCount + 2) c) := by
      apply Fin.ext
      exact hval
    rw [hfin, genDecode_encode]
  unfold genMachine
  simp only [dif_pos hlt]
  rw [hdec]
  first
  | rfl
  | (cases _ <;> rfl)
  | simp

/-- Any two successful core transitions from the same control that both issue moves have equal
move instructions, regardless of the scanned symbols. -/
theorem gen_core_unidirectional (P : GateProgram) :
    ∀ (c : PControl P) (a b : Option Bool)
      (pa pb : PControl P × Turing.TM0.Stmt (Option Bool)),
      genStepCore P c a = some pa → genStepCore P c b = some pb →
      (∃ d, pa.2 = Turing.TM0.Stmt.move d) → (∃ d, pb.2 = Turing.TM0.Stmt.move d) →
      pa.2 = pb.2 := by
  intro c
  cases c with
  | mk st cnt idx =>
   cases st with
  | scan =>
      intro a b pa pb ha1 hb1 hpa hpb
      by_cases ha : a = some true
      · simp only [genStepCore, ha, if_true] at ha1
        cases ha1
        by_cases hb : b = some true
        · simp only [genStepCore, hb, if_true] at hb1
          cases hb1
          rfl
        · by_cases hb0 : b = none
          · simp only [genStepCore, hb, hb0, if_false, if_true] at hb1
            cases hb1
            simp at hpb
          · simp only [genStepCore, hb, hb0, if_false, if_false] at hb1
            simp at hb1
      · by_cases ha0 : a = none
        · simp only [genStepCore, ha, ha0, if_false, if_true] at ha1
          cases ha1
          simp at hpa
        · simp only [genStepCore, ha, ha0, if_false, if_false] at ha1
          simp at ha1
  | mark =>
      intro a b pa pb ha1 hb1 hpa hpb
      simp only [genStepCore] at ha1 hb1
      cases ha1
      cases hb1
      rfl
  | term =>
      intro a b pa pb ha1 hb1 hpa hpb
      simp only [genStepCore] at ha1 hb1
      cases ha1
      simp at hpa
  | afterTerm =>
      intro a b pa pb ha1 hb1 hpa hpb
      by_cases hk : P.prefixBitCount cnt.val = 0
      · simp only [genStepCore, hk, if_true, if_false] at ha1 hb1
        cases ha1
        simp at hpa
      · simp only [genStepCore, hk, if_false] at ha1 hb1
        cases ha1
        cases hb1
        rfl
  | emitWrite =>
      intro a b pa pb ha1 hb1 hpa hpb
      by_cases hk : idx.val < P.prefixBitCount cnt.val
      · simp only [genStepCore, hk, if_true, if_false] at ha1 hb1
        cases ha1
        simp at hpa
      · simp only [genStepCore, hk, if_false] at ha1 hb1
        cases ha1
        simp at hpa
  | emitAdvance =>
      intro a b pa pb ha1 hb1 hpa hpb
      by_cases hk : idx.val + 1 < P.prefixBitCount cnt.val
      · simp only [genStepCore, hk, if_true, if_false] at ha1 hb1
        cases ha1
        cases hb1
        rfl
      · simp only [genStepCore, hk, if_false] at ha1 hb1
        cases ha1
        simp at hpa
  | rewind =>
      intro a b pa pb ha1 hb1 hpa hpb
      by_cases ha : a = none
      · simp only [genStepCore, ha, if_true] at ha1
        cases ha1
        simp at hpa
      · simp only [genStepCore, ha, if_false] at ha1
        by_cases hb : b = none
        · simp only [genStepCore, hb, if_true] at hb1
          cases hb1
          simp at hpb
        · simp only [genStepCore, hb, if_false] at hb1
          cases ha1
          cases hb1
          rfl
  | back =>
      intro a b pa pb ha1 hb1 hpa hpb
      simp only [genStepCore] at ha1 hb1
      cases ha1
      cases hb1
      rfl
  | done =>
      intro a b pa pb ha1 hb1 hpa hpb
      simp only [genStepCore] at ha1
      simp at ha1

/-- At a control index below `genControlSize`, the encoded transition decodes the control,
applies `genStepCore`, and re-encodes the next control using `Fin.castSucc`. -/
theorem genStepDecoded (P : GateProgram)
    (q : Fin (genControlSize P.gateCount (P.bitCount + 2) + 1))
    (hlt : q.val < genControlSize P.gateCount (P.bitCount + 2)) (a : Option Bool) :
    genMachine P q a
      = (genStepCore P (genDecode P.gateCount (P.bitCount + 2) ⟨q.val, hlt⟩) a).map
        (fun p => (Fin.castSucc (genEncode P.gateCount (P.bitCount + 2) p.1), p.2)) := by
  unfold genMachine
  simp only [dif_pos hlt]

/-- The encoded generator is unidirectional: move transitions from a fixed control state have
the same direction for all scanned symbols. -/
theorem gen_unidirectional (P : GateProgram) : tm0Unidirectional (genMachine P) := by
  intro q a b r s har hbs hmr hms
  by_cases hlt : q.val < genControlSize P.gateCount (P.bitCount + 2)
  · set c := genDecode P.gateCount (P.bitCount + 2) ⟨q.val, hlt⟩ with hc
    have har' : (genStepCore P c a).map
        (fun p => (Fin.castSucc (genEncode P.gateCount (P.bitCount + 2) p.1), p.2)) = some r := by
      rw [← genStepDecoded P q hlt a]
      exact har
    have hbs' : (genStepCore P c b).map
        (fun p => (Fin.castSucc (genEncode P.gateCount (P.bitCount + 2) p.1), p.2)) = some s := by
      rw [← genStepDecoded P q hlt b]
      exact hbs
    obtain ⟨pa, hpa⟩ : ∃ pa, genStepCore P c a = some pa := by
      cases hh : genStepCore P c a with
      | none => simp [hh] at har'
      | some pa => exact ⟨pa, rfl⟩
    obtain ⟨pb, hpb⟩ : ∃ pb, genStepCore P c b = some pb := by
      cases hh : genStepCore P c b with
      | none => simp [hh] at hbs'
      | some pb => exact ⟨pb, rfl⟩
    have hr : (genVal P pa.1, pa.2) = r := by
      rw [hpa] at har'
      simp only [Option.map_some] at har'
      exact Option.some.inj har'
    have hs : (genVal P pb.1, pb.2) = s := by
      rw [hpb] at hbs'
      simp only [Option.map_some] at hbs'
      exact Option.some.inj hbs'
    obtain ⟨d₁, hd₁⟩ := hmr
    obtain ⟨d₂, hd₂⟩ := hms
    rw [← hr] at hd₁
    rw [← hs] at hd₂
    rw [← hr, ← hs]
    exact gen_core_unidirectional P c a b pa pb hpa hpb ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩
  · simp [genMachine, hlt] at har

/-- Every gate-program generator satisfies the unidirectional generator normal-form condition.
This supplies the local normal-form property in the machine setting of
[BernsteinVazirani1997]. -/
theorem gen_normal_form (P : GateProgram) :
    generatorNormalForm (gateProgramGenerator P) := by
  exact gen_unidirectional P

/-- Computes a full core-machine step by applying the move or write instruction returned by
`genStepCore` to the current tape. -/
theorem genStepCore_step (P : GateProgram) (c : PControl P) (tape : Tape (Option Bool)) :
    Turing.TM0.step (genCoreMachine P) ⟨c, tape⟩
      = (genStepCore P c tape.head).map (fun p : PControl P × Turing.TM0.Stmt (Option Bool) =>
          ⟨p.1, match p.2 with
            | Turing.TM0.Stmt.move d => tape.move d
            | Turing.TM0.Stmt.write b => tape.write b⟩) := by
  unfold Turing.TM0.step
  simp only [genCoreMachine]
  cases h : genStepCore P c tape.head with
  | none => simp [h]
  | some p =>
    simp only [h, Option.map_some]
    cases p.2 <;> rfl

/-- If core iteration reaches `c'` after `a` steps, iteration for `a + b` steps equals iteration
from `c'` for `b` steps. -/
theorem genCoreIter_append {P : GateProgram} {cfg c' : Turing.TM0.Cfg (Option Bool) (PControl P)}
    {a b : ℕ} (ha : genCoreIter P cfg a = some c') :
    genCoreIter P cfg (a + b) = genCoreIter P c' b := by
  induction b generalizing cfg c' with
  | zero => simpa using! ha
  | succ b ih =>
    have hab : a + (b + 1) = (a + b) + 1 := by omega
    rw [hab, genCoreIter_succ, ih ha]
    rw [genCoreIter_succ]

/-- Scanning a true symbol preserves the scan phase and bit index, increments the program
counter with its cap, and moves right. -/
theorem genStepCore_scan (P : GateProgram) (r : Fin (P.gateCount + 1)) (i : Fin (P.bitCount + 3)) :
    genStepCore P ⟨.scan, r, i⟩ (some true)
      = some (⟨⟨.scan, GenControl.cappedSucc ⟨.scan, r, i⟩, i⟩,
          Turing.TM0.Stmt.move Turing.Dir.right⟩) := by
  simp [genStepCore]

/-- Scanning a blank enters the mark phase and writes a true symbol, preserving both counters. -/
theorem genStepCore_scan_blank (P : GateProgram) (r : Fin (P.gateCount + 1))
    (i : Fin (P.bitCount + 3)) :
    genStepCore P ⟨.scan, r, i⟩ none
      = some (⟨⟨.mark, r, i⟩, Turing.TM0.Stmt.write (some true)⟩) := by
  simp [genStepCore]

/-- A mark-phase transition enters the term phase and moves right, independently of the scanned
symbol. -/
theorem genStepCore_mark (P : GateProgram) (r : Fin (P.gateCount + 1)) (i : Fin (P.bitCount + 3))
    (a : Option Bool) :
    genStepCore P ⟨.mark, r, i⟩ a
      = some (⟨⟨.term, r, i⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩) := by
  simp [genStepCore]

/-- A term-phase transition writes the false delimiter and enters `afterTerm`, preserving both
counters. -/
theorem genStepCore_term (P : GateProgram) (r : Fin (P.gateCount + 1)) (i : Fin (P.bitCount + 3))
    (a : Option Bool) :
    genStepCore P ⟨.term, r, i⟩ a
      = some (⟨⟨.afterTerm, r, i⟩, Turing.TM0.Stmt.write (some false)⟩) := by
  simp [genStepCore]

/-- When the selected prefix has a positive bit count, `afterTerm` moves right and enters
`emitWrite` at bit index zero. -/
theorem genStepCore_afterTerm (P : GateProgram) (r : Fin (P.gateCount + 1))
    (i : Fin (P.bitCount + 3)) (a : Option Bool) (h : 0 < P.prefixBitCount r.val) :
    genStepCore P ⟨.afterTerm, r, i⟩ a
      = some (⟨⟨.emitWrite, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩) := by
  simp [genStepCore, Nat.ne_of_gt h]

/-- When the selected prefix has no encoded bits, `afterTerm` writes a false symbol and enters
rewind with bit index zero. -/
theorem genStepCore_afterTerm_empty (P : GateProgram) (r : Fin (P.gateCount + 1))
    (i : Fin (P.bitCount + 3)) (a : Option Bool) (h : P.prefixBitCount r.val = 0) :
    genStepCore P ⟨.afterTerm, r, i⟩ a
      = some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.write (some false)⟩) := by
  simp [genStepCore, h]

/-- At a valid bit index, `emitWrite` on a blank writes the corresponding prefix bit and enters
`emitAdvance` with the same counters. -/
theorem genStepCore_emitWrite (P : GateProgram) (r : Fin (P.gateCount + 1))
    (j : Fin (P.bitCount + 3)) (hj : j.val < P.prefixBitCount r.val) :
    genStepCore P ⟨.emitWrite, r, j⟩ none
      = some (⟨⟨.emitAdvance, r, j⟩,
          Turing.TM0.Stmt.write (some ((P.prefixBits r.val).getD j.val false))⟩) := by
  simp [genStepCore, hj]

/-- If another encoded bit follows index `j`, `emitAdvance` moves right and enters `emitWrite`
at index `j + 1`. -/
theorem genStepCore_emitAdvance (P : GateProgram) (r : Fin (P.gateCount + 1))
    (j : Fin (P.bitCount + 3)) (a : Option Bool) (hj : j.val + 1 < P.prefixBitCount r.val) :
    genStepCore P ⟨.emitAdvance, r, j⟩ a
      = some (⟨⟨.emitWrite, r, ⟨j.val + 1, by
            have hle := P.prefixBitCount_le r.val
            omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩) := by
  simp [genStepCore, hj]

/-- If the prefix bit count is at most `j + 1`, `emitAdvance` writes the bit returned by `getD j
false` and enters rewind with bit index zero. -/
theorem genStepCore_emitLast (P : GateProgram) (r : Fin (P.gateCount + 1))
    (j : Fin (P.bitCount + 3)) (a : Option Bool) (hj : P.prefixBitCount r.val ≤ j.val + 1) :
    genStepCore P ⟨.emitAdvance, r, j⟩ a
      = some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩,
          Turing.TM0.Stmt.write (some ((P.prefixBits r.val).getD j.val false))⟩) := by
  simp [genStepCore, Nat.not_lt.mpr hj]

/-- On a nonblank symbol, rewind moves left, retains the program counter, and resets the bit
index to zero. -/
theorem genStepCore_rewind (P : GateProgram) (r : Fin (P.gateCount + 1)) (i : Fin (P.bitCount + 3))
    (a : Option Bool) (ha : a ≠ none) :
    genStepCore P ⟨.rewind, r, i⟩ a
      = some (⟨⟨.rewind, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.left⟩) := by
  simp [genStepCore, ha]

/-- On a blank symbol, rewind writes a blank and enters the back phase with bit index zero. -/
theorem genStepCore_rewind_blank (P : GateProgram) (r : Fin (P.gateCount + 1))
    (i : Fin (P.bitCount + 3)) :
    genStepCore P ⟨.rewind, r, i⟩ none
      = some (⟨⟨.back, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.write none⟩) := by
  simp [genStepCore]

/-- The back phase moves right and enters done with bit index zero, independently of the scanned
symbol. -/
theorem genStepCore_back (P : GateProgram) (r : Fin (P.gateCount + 1)) (i : Fin (P.bitCount + 3))
    (a : Option Bool) :
    genStepCore P ⟨.back, r, i⟩ a
      = some (⟨⟨.done, r, ⟨0, by omega⟩⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩) := by
  simp [genStepCore]

/-- For an in-range index `j`, taking `j + 1` Boolean entries equals taking `j` entries and
appending the value at index `j`. -/
theorem take_succ_getD (l : List Bool) (j : ℕ) (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j false] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j < t.length := by simpa using! hj
      simp only [List.take_succ_cons, List.getD_cons_succ]
      rw [ih j hj']
      rfl

/-- For an in-range index `j`, reversing the first `j + 1` Boolean entries places the entry at
`j` before the reversed first `j` entries. -/
theorem reverse_take_succ_getD (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).reverse = l.getD j false :: (l.take j).reverse := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j < t.length := by simpa using! hj
      simp only [List.take_succ_cons, List.getD_cons_succ]
      rw [List.reverse_cons, ih j hj']
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- Reversing a list of `n` copies of one element leaves it unchanged. -/
theorem replicate_reverse {α : Type} (n : ℕ) (a : α) :
    (List.replicate n a).reverse = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.reverse_cons]
    rw [ih]
    rw [← List.replicate_succ']
    rfl

/-- The minimum of `k` and `L` is strictly less than `L + 1`. -/
theorem min_lt_succ (k L : ℕ) : min k L < L + 1 := by
  have h := Nat.min_le_right k L
  omega

/-- For a scan control with counter `min k L` and bit index zero, the capped successor is the
counter `min (k + 1) L`. -/
theorem cappedSucc_scan {L S : ℕ} (k : ℕ) :
    GenControl.cappedSucc (L := L) (S := S) ⟨.scan, ⟨min k L, min_lt_succ k L⟩, ⟨0, by omega⟩⟩
      = ⟨min (k + 1) L, min_lt_succ (k + 1) L⟩ := by
  apply Fin.ext
  simp only [GenControl.cappedSucc]
  by_cases hk : k < L
  · rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    congr 1
    omega
  · have hle : L ≤ k := by omega
    rw [Nat.min_eq_right hle, Nat.min_eq_right (by omega)]
    congr 1
    omega

/-- Before the end of the unary input, one core step advances the scan configuration from
position `k` to `k + 1`. -/
theorem genStep_scan (P : GateProgram) (n k : ℕ) (hk : k < n) :
    Turing.TM0.step (genCoreMachine P) (genCfgScan P n k) = some (genCfgScan P n (k + 1)) := by
  have hne : n - k ≠ 0 := by omega
  have hhead : (List.replicate (n - k) (some true)).headI = some true :=
    replicate_headI_of_ne_zero (a := some true) hne
  have hctrl : GenControl.cappedSucc
        ⟨.scan, ⟨min k P.gateCount, min_lt_succ k P.gateCount⟩, ⟨0, by omega⟩⟩
      = ⟨min (k + 1) P.gateCount, min_lt_succ (k + 1) P.gateCount⟩ :=
    cappedSucc_scan (L := P.gateCount) (S := P.bitCount + 2) k
  have htape : (tapeOf (List.replicate k (some true)) (List.replicate (n - k) (some true))).move
      Turing.Dir.right
      = tapeOf (List.replicate (k + 1) (some true))
          (List.replicate (n - (k + 1)) (some true)) := by
    rw [tapeOf_move_right, hhead]
    have hleft : some true :: List.replicate k (some true) = List.replicate (k + 1) (some true) :=
      replicate_succ' (some true)
    have hright : (List.replicate (n - k) (some true)).tail
        = List.replicate (n - (k + 1)) (some true) := by
      rw [replicate_tail_of_ne_zero (a := some true) hne]
      congr 1
      all_goals omega
    rw [hleft, hright]
  rw [genStepCore_step]
  simp only [genCfgScan, genCtrlScan, tapeOf_head, hhead]
  rw [genStepCore_scan P ⟨min k P.gateCount, min_lt_succ k P.gateCount⟩ ⟨0, by omega⟩]
  simp only [Option.map_some]
  rw [hctrl, htape]
  all_goals rfl

/-- For `k ≤ n`, exactly `k` core steps from the initial configuration reach `genCfgScan P n k`. -/
theorem genScan_run (P : GateProgram) (n k : ℕ) (hk : k ≤ n) :
    genCoreIter P (genCfgInit P n) k = some (genCfgScan P n k) := by
  have hinit : genCfgInit P n = genCfgScan P n 0 := by
    simp [genCfgInit, genCfgScan, genCtrlScan]
  rw [hinit]
  induction k with
  | zero => simp [genCoreIter]
  | succ k ih =>
    have hk' : k < n := by omega
    rw [genCoreIter_succ, ih (by omega)]
    simp only [Option.bind_some]
    rw [genStep_scan P n k hk']
    all_goals rfl

/-- At the end of the unary input, one core step changes the scan configuration into the mark
configuration. -/
theorem genStep_scan_end (P : GateProgram) (n : ℕ) :
    Turing.TM0.step (genCoreMachine P) (genCfgScan P n n) = some (genCfgMark P n) := by
  rw [genStepCore_step]
  simp only [genCfgScan, genCtrlScan, tapeOf_head, Nat.sub_self, replicate_headI_zero]
  rw [genStepCore_scan_blank P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩]
  simp only [Option.map_some]
  rfl

/-- One core step from the mark configuration reaches the term configuration. -/
theorem genStep_mark (P : GateProgram) (n : ℕ) :
    Turing.TM0.step (genCoreMachine P) (genCfgMark P n) = some (genCfgTerm P n) := by
  rw [genStepCore_step]
  simp only [genCfgMark, tapeOf_head, List.headI_cons]
  rw [genStepCore_mark P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩ _]
  simp only [Option.map_some]
  rw [tapeOf_move_right]
  all_goals rfl

/-- One core step from the term configuration writes the delimiter and reaches `genCfgAfterTerm
P n`. -/
theorem genStep_term (P : GateProgram) (n : ℕ) :
    Turing.TM0.step (genCoreMachine P) (genCfgTerm P n) = some (genCfgAfterTerm P n) := by
  rw [genStepCore_step]
  simp only [genCfgTerm, tapeOf_head, List.headI_nil, default_optionBool]
  rw [genStepCore_term P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩ _]
  simp only [Option.map_some]
  rw [tapeOf_write]
  all_goals rfl

/-- Three core steps from the completed scan extend the unary width field and reach the
configuration after writing its delimiter. -/
theorem genWidth_run (P : GateProgram) (n : ℕ) :
    genCoreIter P (genCfgScan P n n) 3 = some (genCfgAfterTerm P n) := by
  rw [genCoreIter_succ_of_step (P := P) (genStep_scan_end P n)]
  rw [genCoreIter_succ_of_step (P := P) (genStep_mark P n)]
  rw [genCoreIter_succ_of_step (P := P) (genStep_term P n)]
  rfl

/-- The generator bit count is the program's prefix bit count at `min n P.gateCount`. -/
theorem genBitCount_eq (P : GateProgram) (n : ℕ) :
    genBitCount P n = P.prefixBitCount (min n P.gateCount) := rfl

/-- At a valid bit index `j`, advancing the emitted-prefix length to `j + 1` prepends the
encoded bit at `j` to `genEmitLeft P n j`. -/
theorem genEmitLeft_succ (P : GateProgram) (n j : ℕ) (hj : j < genBitCount P n) :
    genEmitLeft P n (j + 1) = some ((genBits P n).getD j false) :: genEmitLeft P n j := by
  have hlen : j < (genBits P n).length := by
    have h : (genBits P n).length = genBitCount P n := by
      rfl
    rw [h]
    exact hj
  unfold genEmitLeft
  rw [reverse_take_succ_getD (genBits P n) j hlen]
  simp only [List.map_cons, List.cons_append]

/-- When encoded bits are present, one core step from `genCfgAfterTerm` reaches the initial
bit-emission configuration. -/
theorem genStep_afterTerm (P : GateProgram) (n : ℕ) (hm : 0 < genBitCount P n) :
    Turing.TM0.step (genCoreMachine P) (genCfgAfterTerm P n) = some (genCfgEmit P n) := by
  have hcount : 0 < P.prefixBitCount (min n P.gateCount) := by
    show 0 < genBitCount P n
    exact hm
  rw [genStepCore_step]
  simp only [genCfgAfterTerm, genCtrlScan, tapeOf_head, replicate_headI_zero]
  rw [genStepCore_afterTerm P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩ _
    hcount]
  simp only [Option.map_some]
  rw [tapeOf_move_right]
  all_goals rfl

/-- At a valid bit index `j`, one core step writes that bit and changes `genCfgWrite` to
`genCfgAdv`. -/
theorem genStep_write (P : GateProgram) (n j : ℕ) (hj : j < genBitCount P n) :
    Turing.TM0.step (genCoreMachine P) (genCfgWrite P n j (by omega))
      = some (genCfgAdv P n j hj) := by
  have hcount : j < P.prefixBitCount (min n P.gateCount) := by
    show j < genBitCount P n
    exact hj
  have hidx : j < P.bitCount + 3 := by
    have hle : genBitCount P n ≤ P.bitCount := by
      simp only [genBitCount]
      exact P.prefixBitCount_le (min n P.gateCount)
    omega
  have hbits : P.prefixBits (min n P.gateCount) = genBits P n := by
    rw [genBits, GateProgram.prefixBits_min]
  rw [genStepCore_step]
  simp only [genCfgWrite, tapeOf_head, List.headI_nil, default_optionBool]
  rw [genStepCore_emitWrite P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩
    ⟨j, hidx⟩ hcount]
  simp only [Option.map_some]
  rw [hbits]
  all_goals rfl

/-- When another encoded bit follows `j`, one core step from `genCfgAdv` reaches the write
configuration at `j + 1`. -/
theorem genStep_adv (P : GateProgram) (n j : ℕ) (hj : j + 1 < genBitCount P n) :
    Turing.TM0.step (genCoreMachine P) (genCfgAdv P n j (by omega))
      = some (genCfgWrite P n (j + 1) (by omega)) := by
  have hcount : j + 1 < P.prefixBitCount (min n P.gateCount) := by
    show j + 1 < genBitCount P n
    exact hj
  have hidx : j < P.bitCount + 3 := by
    have hle : genBitCount P n ≤ P.bitCount := by
      simp only [genBitCount]
      exact P.prefixBitCount_le (min n P.gateCount)
    omega
  rw [genStepCore_step]
  simp only [genCfgAdv, tapeOf_head, List.headI_cons]
  rw [genStepCore_emitAdvance P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩
    ⟨j, hidx⟩ _ hcount]
  simp only [Option.map_some]
  rw [tapeOf_move_right]
  simp only [List.headI_cons, List.tail_cons]
  simp only [genCfgWrite, tapeOf_head, List.headI_nil, default_optionBool]
  rw [genEmitLeft_succ P n j (by omega)]
  all_goals rfl

/-- When `j` is the last encoded bit index, one core step from its advance configuration reaches
the corresponding rewind-start configuration. -/
theorem genStep_adv_last (P : GateProgram) (n j : ℕ) (hj : genBitCount P n = j + 1) :
    Turing.TM0.step (genCoreMachine P) (genCfgAdv P n j (by omega))
      = some (genCfgRewindStart P n j (by omega)) := by
  have hcount : P.prefixBitCount (min n P.gateCount) ≤ j + 1 := by
    show genBitCount P n ≤ j + 1
    omega
  have hidx : j < P.bitCount + 3 := by
    have hle : genBitCount P n ≤ P.bitCount := by
      simp only [genBitCount]
      exact P.prefixBitCount_le (min n P.gateCount)
    omega
  have hbits : P.prefixBits (min n P.gateCount) = genBits P n := by
    rw [genBits, GateProgram.prefixBits_min]
  rw [genStepCore_step]
  simp only [genCfgAdv, tapeOf_head, List.headI_cons]
  rw [genStepCore_emitLast P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩
    ⟨j, hidx⟩ _ hcount]
  simp only [Option.map_some]
  rw [hbits]
  all_goals rfl

/-- For a valid bit index `j`, iteration from the write configuration at zero reaches `genCfgAdv
P n j hj` after `2 * j + 1` core steps. -/
theorem genEmit_run (P : GateProgram) (n j : ℕ) (hj : j < genBitCount P n) :
    genCoreIter P (genCfgWrite P n 0 (by omega)) (2 * j + 1) = some (genCfgAdv P n j hj) := by
  induction j with
  | zero =>
    rw [genCoreIter_succ, genCoreIter_zero]
    simp only [Option.bind_some]
    rw [genStep_write P n 0 (by omega)]
    all_goals rfl
  | succ j ih =>
    have hj' : j + 1 < genBitCount P n := by omega
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
    rw [genCoreIter_append (ih (by omega))]
    rw [genCoreIter_succ, genCoreIter_succ, genCoreIter_zero]
    simp only [Option.bind_some]
    rw [genStep_adv P n j (by omega)]
    simp only [Option.bind_some]
    rw [genStep_write P n (j + 1) hj']
    all_goals rfl

/-- A nonempty list of optional Boolean symbols is reconstructed by placing its default head
before its tail. -/
theorem headI_tail_cons (r : List (Option Bool)) (h : r ≠ []) :
    r.headI :: r.tail = r := by
  cases r with
  | nil => exact (h rfl).elim
  | cons a t => rfl

/-- If the right list is nonempty and contains no blanks, one rewind step moves left, replacing
the left list by its tail and prepending its default head to the right list. -/
theorem genStep_rewind_left (P : GateProgram) (n : ℕ) (l : List (Option Bool))
    (r : List (Option Bool)) (hr : r ≠ []) (hne : ∀ a ∈ r, a ≠ none) :
    Turing.TM0.step (genCoreMachine P) (genCfgRewind P n l r)
      = some (genCfgRewind P n l.tail (l.headI :: r)) := by
  have hhead : r.headI ≠ none := by
    cases hr' : r with
    | nil => exact absurd hr' hr
    | cons a t =>
      simp only [List.headI_cons]
      exact hne a (by simp [hr'])
  rw [genStepCore_step]
  simp only [genCfgRewind, tapeOf_head, hhead]
  rw [genStepCore_rewind P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩ r.headI hhead]
  simp only [Option.map_some]
  rw [tapeOf_move_left]
  rw [headI_tail_cons r hr]

/-- If both tape lists contain no blanks and the right list is nonempty, `l.length + 1` rewind
steps reach a blank before `l.reverse ++ r`, with no listed cells to the left. -/
theorem genRewind_run (P : GateProgram) (n : ℕ) (l : List (Option Bool)) (r : List (Option Bool))
    (hr : r ≠ []) (hneL : ∀ a ∈ l, a ≠ none) (hneR : ∀ a ∈ r, a ≠ none) :
    genCoreIter P (genCfgRewind P n l r) (l.length + 1)
      = some (genCfgRewind P n [] (none :: l.reverse ++ r)) := by
  induction l generalizing r with
  | nil =>
    rw [genCoreIter_succ_of_step (P := P) (genStep_rewind_left P n [] r hr hneR)]
    simp only [List.length_nil]
    rw [genCoreIter_zero]
    simp only [List.tail_nil, List.headI_nil, default_optionBool, List.reverse_nil,
      List.nil_append, List.cons_append]
  | cons a l' ih =>
    rw [genCoreIter_succ_of_step (P := P) (genStep_rewind_left P n (a :: l') r hr hneR)]
    simp only [List.tail_cons, List.headI_cons, List.length_cons]
    have hneL' : ∀ x ∈ l', x ≠ none := by
      intro x hx
      exact hneL x (List.mem_cons_of_mem _ hx)
    have hne' : ∀ x ∈ a :: r, x ≠ none := by
      intro x hx
      rcases List.mem_cons.mp hx with hxa | hxr
      · rw [hxa]
        exact hneL a (List.mem_cons_self)
      · exact hneR x hxr
    rw [ih (a :: r) (by simp) hneL' hne']
    simp only [Option.some.injEq]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- One core step from the rewind-end configuration reaches the back configuration on the same
blank before the output word. -/
theorem genStep_rewind_end (P : GateProgram) (n : ℕ) :
    Turing.TM0.step (genCoreMachine P) (genCfgRewindEnd P n) = some (genCfgBack P n) := by
  rw [genStepCore_step]
  simp only [genCfgRewindEnd, tapeOf_head, List.headI_cons]
  rw [genStepCore_rewind_blank P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩]
  simp only [Option.map_some]
  rw [tapeOf_write]
  all_goals rfl

/-- One core step from the back configuration moves onto the output word and reaches the done
configuration. -/
theorem genStep_back (P : GateProgram) (n : ℕ) :
    Turing.TM0.step (genCoreMachine P) (genCfgBack P n) = some (genCfgDone P n) := by
  rw [genStepCore_step]
  simp only [genCfgBack, tapeOf_head, List.headI_cons]
  rw [genStepCore_back P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩ ⟨0, by omega⟩ _]
  simp only [Option.map_some]
  rw [tapeOf_move_right]
  all_goals rfl

/-- The done configuration has no successor under the core generator's step function. -/
theorem genStep_done (P : GateProgram) (n : ℕ) :
    Turing.TM0.step (genCoreMachine P) (genCfgDone P n) = none := by
  rw [genStepCore_step]
  simp only [genCfgDone, tapeOf_head, List.headI_cons]
  rw [genStepCore]
  rfl

/-- The designated generator step count `2 * n + 3 * genBitCount P n + 8`. -/
def genSteps (P : GateProgram) (n : ℕ) : ℕ := 2 * n + 3 * genBitCount P n + 8

/-- Every member of a list consisting of `n` copies of `c` equals `c`. -/
theorem mem_replicate_eq {α : Type} (n : ℕ) (c : α) (a : α) (h : a ∈ List.replicate n c) :
    a = c := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    simp only [List.replicate_succ, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact ih h

/-- Every cell listed in `genEmitLeft P n j` is nonblank. -/
theorem genEmitLeft_ne_none (P : GateProgram) (n j : ℕ) :
    ∀ a ∈ genEmitLeft P n j, a ≠ none := by
  intro a ha
  simp only [genEmitLeft, List.mem_append] at ha
  rcases ha with ha | ha
  · rcases List.mem_map.mp ha with ⟨b, hb, hba⟩
    rw [← hba]
    simp
  · cases ha with
    | head => simp
    | tail _ ha =>
      cases ha with
      | head => simp
      | tail _ ha =>
        have h' : a = some true := mem_replicate_eq n (some true) a ha
        rw [h']
        simp

/-- When the encoded bit count is zero, one core step from `genCfgAfterTerm` reaches the
empty-encoding rewind configuration. -/
theorem genStep_afterTerm_empty (P : GateProgram) (n : ℕ) (hm : genBitCount P n = 0) :
    Turing.TM0.step (genCoreMachine P) (genCfgAfterTerm P n) = some (genCfgRewindEmpty P n) := by
  have hcount : P.prefixBitCount (min n P.gateCount) = 0 := by
    show genBitCount P n = 0
    exact hm
  rw [genStepCore_step]
  simp only [genCfgAfterTerm, genCtrlScan, tapeOf_head, List.headI_cons]
  rw [genStepCore_afterTerm_empty P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩
    ⟨0, by omega⟩ _ hcount]
  simp only [Option.map_some]
  rw [tapeOf_write]
  all_goals rfl

/-- For a positive bit count `m`, reversing the cells left of the last emitted bit and appending
that bit reconstructs `genWordCells P n`. -/
theorem genEmitLeft_reverse_last (P : GateProgram) (n : ℕ) (m : ℕ)
    (hm : m = genBitCount P n) (hm0 : 0 < m) :
    (genEmitLeft P n (m - 1)).reverse ++ (some ((genBits P n).getD (m - 1) false) :: [])
      = genWordCells P n := by
  have hlen : (genBits P n).length = genBitCount P n := rfl
  have hmlen : (genBits P n).length ≤ m := by
    rw [hm, ← hlen]
  have htake : (genBits P n).take m
      = (genBits P n).take (m - 1) ++ ([(genBits P n).getD (m - 1) false] : List Bool) := by
    have h := take_succ_getD (genBits P n) (m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at h
  have htakefull : (genBits P n).take m = genBits P n :=
    take_eq_self_of_length_le (genBits P n) m hmlen
  have hbase : (some false :: some true :: List.replicate n (some true)).reverse
      = List.replicate (n + 1) (some true) ++ [some false] := by
    simp only [List.reverse_cons, replicate_reverse]
    rw [← List.replicate_succ']
  have hmap : (((genBits P n).take (m - 1)).reverse.map (fun b => some b)).reverse
      = ((genBits P n).take (m - 1)).map (fun b => some b) := by
    rw [List.map_reverse, List.reverse_reverse]
  have hmap2 : ((genBits P n).take (m - 1)).map (fun b => some b)
      ++ [some ((genBits P n).getD (m - 1) false)]
      = ((genBits P n).take m).map (fun b => some b) := by
    rw [htake, List.map_append]
    rfl
  calc
    (genEmitLeft P n (m - 1)).reverse ++ (some ((genBits P n).getD (m - 1) false) :: [])
        = (List.replicate (n + 1) (some true) ++ [some false])
            ++ ((genBits P n).take (m - 1)).map (fun b => some b)
            ++ [some ((genBits P n).getD (m - 1) false)] := by
          unfold genEmitLeft
          rw [List.reverse_append, hbase, hmap]
    _ = List.replicate (n + 1) (some true)
            ++ ([some false] ++ ((genBits P n).take m).map (fun b => some b)) := by
          rw [List.append_assoc, List.append_assoc, hmap2]
    _ = genWordCells P n := by
          rw [htakefull]
          unfold genWordCells
          rfl

/-- If the encoded bit count is zero, `n + 4` core steps from the empty-encoding rewind
configuration reach the done configuration. -/
theorem genRewind_empty (P : GateProgram) (n : ℕ) (hm : genBitCount P n = 0) :
    genCoreIter P (genCfgRewindEmpty P n) (n + 4) = some (genCfgDone P n) := by
  have hbits : genBits P n = [] := by
    have h : (genBits P n).length = genBitCount P n := rfl
    have h0 : (genBits P n).length = 0 := by rw [h]; exact hm
    exact List.length_eq_zero_iff.mp h0
  have hword : none :: ((some true :: List.replicate n (some true)).reverse ++ [some false])
      = none :: genWordCells P n := by
    have h1 : (some true :: List.replicate n (some true)).reverse
        = List.replicate (n + 1) (some true) := by
      simp only [List.reverse_cons, replicate_reverse]
      rw [← List.replicate_succ']
    rw [h1]
    unfold genWordCells
    rw [hbits, List.map_nil]
  have hleft : ∀ a ∈ some true :: List.replicate n (some true), a ≠ none := by
    intro a ha
    cases ha with
    | head => simp
    | tail _ ha =>
      have h' : a = some true := mem_replicate_eq n (some true) a ha
      rw [h']
      simp
  have hright : ∀ a ∈ [some false], a ≠ none := by
    intro a ha
    have : a = some false := by simpa using! ha
    simp [this]
  have hlen : (some true :: List.replicate n (some true)).length + 1 = n + 2 := by
    simp only [List.length_cons, List.length_replicate]
  have hrun := genRewind_run P n (some true :: List.replicate n (some true)) [some false]
    (by simp) hleft hright
  rw [hlen] at hrun
  have hcfg : genCfgRewindEmpty P n
      = genCfgRewind P n (some true :: List.replicate n (some true)) [some false] := rfl
  have heq : genCoreIter P (genCfgRewindEmpty P n) (n + 2)
      = some (genCfgRewind P n []
        (none :: ((some true :: List.replicate n (some true)).reverse ++ [some false]))) := by
    rw [hcfg]
    exact hrun
  have h1 : genCoreIter P (genCfgRewindEmpty P n) (n + 2) = some (genCfgRewindEnd P n) := by
    rw [heq]
    simp only [Option.some.injEq]
    unfold genCfgRewindEnd genCfgRewind
    rw [hword]
  have h2 : genCoreIter P (genCfgRewindEnd P n) 2 = some (genCfgDone P n) := by
    rw [genCoreIter_succ_of_step (P := P) (genStep_rewind_end P n)]
    rw [genCoreIter_succ_of_step (P := P) (genStep_back P n)]
    rfl
  rw [show n + 4 = (n + 2) + 2 by omega]
  rw [genCoreIter_append h1]
  exact h2

/-- For a positive bit count `m`, `n + m + 4` core steps from rewind at the last encoded bit
reach the done configuration. -/
theorem genRewind_last (P : GateProgram) (n : ℕ) (m : ℕ)
    (hm : m = genBitCount P n) (hm0 : 0 < m) :
    genCoreIter P (genCfgRewindStart P n (m - 1) (by omega)) (n + m + 4)
      = some (genCfgDone P n) := by
  have hword : none :: ((genEmitLeft P n (m - 1)).reverse
      ++ (some ((genBits P n).getD (m - 1) false) :: []))
      = none :: genWordCells P n := by
    rw [genEmitLeft_reverse_last P n m hm hm0]
  have hcfg : genCfgRewindStart P n (m - 1) (by omega)
      = genCfgRewind P n (genEmitLeft P n (m - 1))
          (some ((genBits P n).getD (m - 1) false) :: []) := rfl
  have hbitslen : (genBits P n).length = m := by
    have h : (genBits P n).length = genBitCount P n := rfl
    rw [h, hm]
  have hlen : (genEmitLeft P n (m - 1)).length + 1 = n + m + 2 := by
    simp only [genEmitLeft, List.length_append, List.length_map, List.length_reverse,
      List.length_take, List.length_cons, List.length_replicate]
    rw [Nat.min_eq_left (by omega)]
    omega
  have hright : ∀ a ∈ (some ((genBits P n).getD (m - 1) false) :: []), a ≠ none := by
    intro a ha
    have : a = some ((genBits P n).getD (m - 1) false) := by simpa using! ha
    simp [this]
  have hrun := genRewind_run P n (genEmitLeft P n (m - 1))
    (some ((genBits P n).getD (m - 1) false) :: []) (by simp) (genEmitLeft_ne_none P n (m - 1))
    hright
  rw [hlen] at hrun
  have heq : genCoreIter P (genCfgRewindStart P n (m - 1) (by omega)) (n + m + 2)
      = some (genCfgRewind P n []
        (none :: ((genEmitLeft P n (m - 1)).reverse
          ++ (some ((genBits P n).getD (m - 1) false) :: [])))) := by
    rw [hcfg]
    exact hrun
  have h1 : genCoreIter P (genCfgRewindStart P n (m - 1) (by omega)) (n + m + 2)
      = some (genCfgRewindEnd P n) := by
    rw [heq]
    simp only [Option.some.injEq]
    unfold genCfgRewindEnd genCfgRewind
    rw [hword]
  have h2 : genCoreIter P (genCfgRewindEnd P n) 2 = some (genCfgDone P n) := by
    rw [genCoreIter_succ_of_step (P := P) (genStep_rewind_end P n)]
    rw [genCoreIter_succ_of_step (P := P) (genStep_back P n)]
    rfl
  rw [show n + m + 4 = (n + m + 2) + 2 by omega]
  rw [genCoreIter_append h1]
  exact h2

/-- For a positive bit count `m`, `2 * m` core steps from the initial emission configuration
reach rewind at the last encoded bit. -/
theorem genEmit_last (P : GateProgram) (n : ℕ) (m : ℕ)
    (hm : m = genBitCount P n) (hm0 : 0 < m) :
    genCoreIter P (genCfgEmit P n) (2 * m)
      = some (genCfgRewindStart P n (m - 1) (by omega)) := by
  have hrun := genEmit_run P n (m - 1) (by omega)
  have hcfg : genCfgEmit P n = genCfgWrite P n 0 (by omega) := rfl
  have hstep : Turing.TM0.step (genCoreMachine P) (genCfgAdv P n (m - 1) (by omega))
      = some (genCfgRewindStart P n (m - 1) (by omega)) := by
    have hcount : P.prefixBitCount (min n P.gateCount) ≤ m - 1 + 1 := by
      show genBitCount P n ≤ m - 1 + 1
      omega
    have hidx : m - 1 < P.bitCount + 3 := by
      have hle : genBitCount P n ≤ P.bitCount := by
        simp only [genBitCount]
        exact P.prefixBitCount_le (min n P.gateCount)
      omega
    rw [genStepCore_step]
    simp only [genCfgAdv, tapeOf_head, List.headI_cons]
    rw [genStepCore_emitLast P ⟨min n P.gateCount, min_lt_succ n P.gateCount⟩
      ⟨m - 1, hidx⟩ _ hcount]
    simp only [Option.map_some]
    have hbits : P.prefixBits (min n P.gateCount) = genBits P n := by
      rw [genBits, GateProgram.prefixBits_min]
    rw [hbits]
    all_goals rfl
  rw [hcfg]
  rw [show 2 * m = (2 * (m - 1) + 1) + 1 by omega]
  rw [genCoreIter_append hrun]
  rw [genCoreIter_succ_of_step (P := P) hstep]
  rfl

/-- Starting from the initial configuration, `genSteps P n` core steps reach `genCfgDone P n`. -/
theorem gen_final (P : GateProgram) (n : ℕ) :
    genCoreIter P (genCfgInit P n) (genSteps P n) = some (genCfgDone P n) := by
  have h1 : genCoreIter P (genCfgInit P n) (n + 3) = some (genCfgAfterTerm P n) := by
    rw [genCoreIter_append (genScan_run P n n (by omega))]
    exact genWidth_run P n
  by_cases hm : genBitCount P n = 0
  · have h2 : genCoreIter P (genCfgAfterTerm P n) 1 = some (genCfgRewindEmpty P n) :=
      genStep_afterTerm_empty P n hm
    have h3 : genCoreIter P (genCfgRewindEmpty P n) (n + 4) = some (genCfgDone P n) :=
      genRewind_empty P n hm
    have hidx : genSteps P n = (n + 3) + (1 + (n + 4)) := by
      simp only [genSteps, hm]
      omega
    rw [hidx]
    rw [genCoreIter_append h1 (b := 1 + (n + 4))]
    rw [genCoreIter_append h2 (b := n + 4)]
    exact h3
  · have hm0 : 0 < genBitCount P n := by omega
    have h2 : genCoreIter P (genCfgAfterTerm P n) 1 = some (genCfgEmit P n) :=
      genStep_afterTerm P n hm0
    have h3 : genCoreIter P (genCfgEmit P n) (2 * genBitCount P n)
        = some (genCfgRewindStart P n (genBitCount P n - 1) (by omega)) :=
      genEmit_last P n (genBitCount P n) rfl hm0
    have h4 : genCoreIter P (genCfgRewindStart P n (genBitCount P n - 1) (by omega))
        (n + genBitCount P n + 4) = some (genCfgDone P n) :=
      genRewind_last P n (genBitCount P n) rfl hm0
    have hidx : genSteps P n
        = (n + 3) + (1 + (2 * genBitCount P n + (n + genBitCount P n + 4))) := by
      simp only [genSteps]
      omega
    rw [hidx]
    rw [genCoreIter_append h1 (b := 1 + (2 * genBitCount P n + (n + genBitCount P n + 4)))]
    rw [genCoreIter_append h2 (b := 2 * genBitCount P n + (n + genBitCount P n + 4))]
    rw [genCoreIter_append h3 (b := n + genBitCount P n + 4)]
    exact h4

/-- The standard initial configuration for the unary input equals `genCfgInit P n` with its
control encoded by `genVal`. -/
theorem genInit_eq (P : GateProgram) (n : ℕ) :
    Turing.TM0.init (uniformBqpUnaryInput n)
      = ⟨genVal P (genCfgInit P n).q, (genCfgInit P n).Tape⟩ := by
  have hq : genVal P (genCfgInit P n).q = 0 := by
    apply Fin.ext
    show (genEncode P.gateCount (P.bitCount + 2) (genCtrlScan P n 0)).val = 0
    simp only [genEncode, genLabel, genInner, GenState.idx, genCtrlScan, Fin.val_mk,
      Nat.min_eq_left (Nat.zero_le _)]
    omega
  have hinit : Turing.TM0.init (uniformBqpUnaryInput n)
      = ⟨(0 : Fin (genControlSize P.gateCount (P.bitCount + 2) + 1)), (genCfgInit P n).Tape⟩ := by
    unfold Turing.TM0.init
    congr 1
  calc
    Turing.TM0.init (uniformBqpUnaryInput n) = ⟨0, (genCfgInit P n).Tape⟩ := hinit
    _ = ⟨genVal P (genCfgInit P n).q, (genCfgInit P n).Tape⟩ := by rw [hq]

/-- Every cell in the generator's complete output word is nonblank. -/
theorem genWordCells_ne_none (P : GateProgram) (n : ℕ) :
    ∀ a ∈ genWordCells P n, a ≠ none := by
  intro a ha
  have hmem : a ∈ genWordCells P n := ha
  simp only [genWordCells, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact mem_replicate_eq (n + 1) (some true) a hmem ▸ (by simp)
  · cases hmem with
    | head => simp
    | tail _ hmem =>
      rcases List.mem_map.mp hmem with ⟨b, hb, hba⟩
      rw [← hba]
      simp

/-- Extracting Boolean values from the output cells yields the encoding of width `n + 1` and
gate prefix `P.gates.take n`. -/
theorem genWordCells_bits (P : GateProgram) (n : ℕ) :
    (genWordCells P n).map (fun o => o.getD false)
      = encodeUniformBqpWord (n + 1) (P.gates.take n) := by
  have hbits : genBits P n = (P.gates.take n).flatMap encodeFiniteGateCode := by
    rw [genBits, GateProgram.prefixBits_min]
  simp only [genWordCells, List.map_append, List.map_replicate, List.map_cons, List.map_map]
  rw [hbits]
  simp only [encodeUniformBqpWord, encodeUnaryField]
  simp

/-- Reading the final tape until a blank with fuel `n + uniformBqpTimeBound
(gateProgramGenerator P) n + 1` returns the encoded width `n + 1` and gate prefix
`P.gates.take n`. -/
theorem gen_read (P : GateProgram) (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelReadOutputUntilBlank
      (n + uniformBqpTimeBound (gateProgramGenerator P) n + 1) (genCfgDone P n).Tape.right₀
      = some (encodeUniformBqpWord (n + 1) (P.gates.take n)) := by
  have hbits : (genBits P n).length ≤ P.bitCount := by
    simp only [genBits]
    exact P.prefixBitCount_le (min n P.gateCount)
  have hlen : (genWordCells P n).length ≤ n + uniformBqpTimeBound (gateProgramGenerator P) n + 1 := by
    have hbits' : (genBits P n).length ≤ P.bitCount := hbits
    have hcoef : P.bitCount + 2 ≤ 2 + 9 + 3 * P.bitCount := by omega
    have hmul : (P.bitCount + 2) * (n + 1) ≤ (2 + 9 + 3 * P.bitCount) * (n + 1) := by
      nlinarith
    have htime : P.bitCount + 2 ≤ (2 + 9 + 3 * P.bitCount) * (n + 1) := by
      nlinarith
    simp only [genWordCells, List.length_append, List.length_replicate, List.length_cons,
      List.length_map, uniformBqpTimeBound, uniformBqpPolynomial, gateProgramGenerator,
      gateProgramTimeCoefficient, Nat.pow_one]
    calc
      (n + 1) + (genBits P n).length + 1 ≤ (n + 1) + P.bitCount + 1 := by omega
      _ ≤ n + (2 + 9 + 3 * P.bitCount) * (n + 1) + 1 := by omega
  have hnb : ∀ a ∈ genWordCells P n, a ≠ none := genWordCells_ne_none P n
  have hcells : (genWordCells P n).headI :: (genWordCells P n).tail = genWordCells P n := by
    cases h : genWordCells P n with
    | nil => exact absurd h (genWordCells_ne_nil P n)
    | cons a t => simp
  have hnb' : ∀ a ∈ (genWordCells P n).headI :: (genWordCells P n).tail, a ≠ none := by
    intro a ha
    have ha' : a ∈ genWordCells P n := by
      rw [← hcells]
      exact ha
    exact genWordCells_ne_none P n a ha'
  have hlen' : ((genWordCells P n).headI :: (genWordCells P n).tail).length
      ≤ n + uniformBqpTimeBound (gateProgramGenerator P) n + 1 := by
    rw [hcells]
    exact hlen
  simp only [genCfgDone, tapeOf_right₀]
  rw [readOutput_of_list _ hlen' hnb']
  simp only [Option.some.injEq]
  rw [hcells]
  exact genWordCells_bits P n

/-- Iteration of the encoded generator on the unary input reaches the encoded done configuration
after `genSteps P n` steps. -/
theorem gen_iter_final (P : GateProgram) (n : ℕ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine
      (Turing.TM0.init (uniformBqpUnaryInput n)) (genSteps P n)
      = some ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ := by
  have hrun : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine
      ⟨genVal P (genCfgInit P n).q, (genCfgInit P n).Tape⟩ (genSteps P n)
      = some ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ := by
    have h := genCoreIter_transfer P (genCfgInit P n) (genSteps P n)
    rw [gen_final P n] at h
    exact h
  have hinit : Turing.TM0.init (uniformBqpUnaryInput n)
      = ⟨genVal P (genCfgInit P n).q, (genCfgInit P n).Tape⟩ := genInit_eq P n
  have hiter : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine
      (Turing.TM0.init (uniformBqpUnaryInput n)) (genSteps P n)
      = Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine
        ⟨genVal P (genCfgInit P n).q, (genCfgInit P n).Tape⟩ (genSteps P n) :=
    congrArg (fun cfg => Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine cfg (genSteps P n))
      hinit
  rw [hiter, hrun]

/-- The designated step count `genSteps P n` lies within the gate-program generator's declared
time bound. -/
theorem gen_steps_le_timeBound (P : GateProgram) (n : ℕ) :
    genSteps P n ≤ uniformBqpTimeBound (gateProgramGenerator P) n := by
  have hle : genBitCount P n ≤ P.bitCount := by
    simp only [genBitCount]
    exact P.prefixBitCount_le (min n P.gateCount)
  simp only [genSteps, uniformBqpTimeBound, uniformBqpPolynomial, gateProgramGenerator,
    gateProgramTimeCoefficient, Nat.pow_one]
  nlinarith

/-- The encoded circuit consisting of width `n + 1` and the first `n` program gates has length
at most `n` plus the generator's time bound. -/
theorem gen_encode_length_le (P : GateProgram) (n : ℕ) :
    (encodeUniformBqpWord (n + 1) (P.gates.take n)).length
      ≤ n + uniformBqpTimeBound (gateProgramGenerator P) n := by
  have hflat : ((P.gates.take n).flatMap encodeFiniteGateCode).length ≤ P.bitCount := by
    have h := P.prefixBitCount_le (min n P.gateCount)
    rw [GateProgram.prefixBitCount, GateProgram.prefixBits, GateProgram.take_min_eq] at h
    exact h
  simp only [encodeUniformBqpWord, encodeUnaryField, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil, uniformBqpTimeBound,
    uniformBqpPolynomial, gateProgramGenerator, gateProgramTimeCoefficient, Nat.pow_one]
  nlinarith

/-- On unary input length `n`, bounded generation returns width `n + 1` and the gate prefix
`P.gates.take n`. -/
theorem gen_generated (P : GateProgram) (n : ℕ) :
    uniformBqpGeneratedAt (gateProgramGenerator P) n = some (n + 1, P.gates.take n) := by
  have hcfg : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine
      (Turing.TM0.init (uniformBqpUnaryInput n)) (genSteps P n)
      = some ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ := gen_iter_final P n
  have hstop : Turing.TM0.step (gateProgramGenerator P).machine
      ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ = none := by
    change Turing.TM0.step (genMachine P)
      ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ = none
    have h := genStep P (genCfgDone P n).q (genCfgDone P n).Tape
    have hnone : genStepCore P (genCfgDone P n).q (genCfgDone P n).Tape.head = none := by
      simp [genStepCore, genCfgDone]
    rw [hnone] at h
    exact h
  have hread := gen_read P n
  have h := Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelGeneratedAt_of_run (g := gateProgramGenerator P) (n := n)
    (t := genSteps P n) (cfg := ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩)
    (gen_steps_le_timeBound P n) hcfg hstop (n + 1) (P.gates.take n) hread
  rwa [Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.modelGeneratedAt_eq] at h

/-- The gate prefix `P.gates.take n` is legal on a register of width `n + 1`. -/
theorem gen_word_legal (P : GateProgram) (n : ℕ) :
    finiteWordLegal (n + 1) (P.gates.take n) = true :=
  P.staircase_legal n

/-- Every circuit returned by bounded generation for a gate-program generator is legal at its
reported width. -/
theorem gen_wellformed (P : GateProgram) : generatorWellformed (gateProgramGenerator P) := by
  intro n q gs h
  rw [gen_generated P n] at h
  have h' : (n + 1, P.gates.take n) = (q, gs) := by injection h
  cases h'
  exact gen_word_legal P n

/-- For the gate-program generator, `BitMachineAfter` agrees with `iterStep` from the standard
initial configuration on any input and at any step count. -/
theorem bitMachineAfter_eq_iterStep_gen (P : GateProgram) (input : List (Option Bool)) (t : ℕ) :
    BitMachineAfter (gateProgramGenerator P).machine input t
      = Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine (Turing.TM0.init input) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [BitMachineAfter, ih, Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep_succ]

/-- The encoded gate-program generator reaches a halting configuration on unary input length `n`
after `genSteps P n` steps. -/
theorem gen_halts_at (P : GateProgram) (n : ℕ) :
    BitMachineHaltsAt (gateProgramGenerator P).machine (uniformBqpUnaryInput n) (genSteps P n) := by
  refine ⟨⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩, ?_, ?_⟩
  · have hcfg : Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp.iterStep (gateProgramGenerator P).machine
        (Turing.TM0.init (uniformBqpUnaryInput n)) (genSteps P n)
        = some ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ := gen_iter_final P n
    simpa only [bitMachineAfter_eq_iterStep_gen] using! hcfg
  · have h := genStep_transport P (genCfgDone P n)
    rw [genStep_done P n] at h
    change Turing.TM0.step (genMachine P)
      ⟨genVal P (genCfgDone P n).q, (genCfgDone P n).Tape⟩ = none
    exact h

/-- Every gate-program generator halts after finitely many steps on each unary input. -/
theorem gen_halts (P : GateProgram) : generatorHaltsEffectively (gateProgramGenerator P) := by
  intro n
  exact ⟨genSteps P n, gen_halts_at P n⟩

/-- Every gate-program generator has a polynomial bound on its halting time for unary inputs. -/
theorem gen_clocked (P : GateProgram) : generatorClocked (gateProgramGenerator P) := by
  refine ⟨(gateProgramGenerator P).timeCoefficient, (gateProgramGenerator P).timeDegree, ?_⟩
  intro n
  refine ⟨genSteps P n, ?_, gen_halts_at P n⟩
  have hle : genBitCount P n ≤ P.bitCount := by
    simp only [genBitCount]
    exact P.prefixBitCount_le (min n P.gateCount)
  simp only [genSteps, uniformBqpPolynomial, gateProgramGenerator, gateProgramTimeCoefficient,
    Nat.pow_one]
  nlinarith

/-- Every gate-program generator satisfies the bit-Turing-machine backend premise: it halts on
every unary input and its totalized circuit encoding has polynomially bounded length. -/
theorem gen_bitTm_backend (P : GateProgram) : bitTmBackendPremise (gateProgramGenerator P) := by
  refine ⟨gen_halts P, ?_⟩
  refine ⟨P.bitCount + 3, 1, ?_⟩
  intro n
  have hgen := gen_generated P n
  have hflat : ((P.gates.take n).flatMap encodeFiniteGateCode).length ≤ P.bitCount := by
    have h := P.prefixBitCount_le (min n P.gateCount)
    rw [GateProgram.prefixBitCount, GateProgram.prefixBits, GateProgram.take_min_eq] at h
    exact h
  have henc : (encodeUniformBqpWord (n + 1) (P.gates.take n)).length
      ≤ (P.bitCount + 3) * (n + 1) := by
    simp only [encodeUniformBqpWord, encodeUnaryField, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    nlinarith
  have hL : (encodeUniformBqpWord (uniformBqpGeneratedTotal (gateProgramGenerator P) n).1
      (uniformBqpGeneratedTotal (gateProgramGenerator P) n).2).length
      = (encodeUniformBqpWord (n + 1) (P.gates.take n)).length := by
    simp only [uniformBqpGeneratedTotal, hgen]
    rfl
  rw [hL]
  simpa only [uniformBqpPolynomial, Nat.pow_one] using! henc

/-- Every gate-program generator successfully produces legal circuits with a halting witness and
the declared time, gate-count, width, and encoded-output bounds. This verifies the local
generator-validity condition in the uniform machine setting of [BernsteinVazirani1997]. -/
theorem gen_valid (P : GateProgram) : uniformBqpGeneratorValid (gateProgramGenerator P) := by
  intro n
  have hgen := gen_generated P n
  have htime : genSteps P n ≤ uniformBqpTimeBound (gateProgramGenerator P) n :=
    gen_steps_le_timeBound P n
  have htake : (P.gates.take n).length ≤ P.gateCount := by
    rw [List.length_take, GateProgram.gateCount]
    exact Nat.min_le_right _ _
  have hword : (P.gates.take n).length ≤ uniformBqpWordBound (gateProgramGenerator P) n := by
    simp only [uniformBqpWordBound, uniformBqpPolynomial, gateProgramGenerator, Nat.pow_zero,
      Nat.mul_one]
    exact htake
  have hspace : n + 1 ≤ uniformBqpSpaceBound (gateProgramGenerator P) n := by
    simp only [uniformBqpSpaceBound, uniformBqpPolynomial, gateProgramGenerator, Nat.pow_one,
      Nat.one_mul]
    exact Nat.le_refl _
  exact ⟨n + 1, P.gates.take n, hgen, ⟨genSteps P n, htime, gen_halts_at P n⟩,
    gen_word_legal P n, hword, hspace, gen_encode_length_le P n⟩

/-- Duplicating the width-`n + 1` circuit with gate prefix `P.gates.take n` yields a legal gate
word on the doubled register. -/
theorem gen_duplicate_legal (P : GateProgram) (n : ℕ) :
    finiteWordLegal (duplicateWord (n + 1) (P.gates.take n)).1
      (duplicateWord (n + 1) (P.gates.take n)).2 = true := by
  have hleg : finiteWordLegal (n + 1) (P.gates.take n) = true := P.staircase_legal n
  rw [finiteWordLegal, List.all_eq_true] at hleg
  have hall : ∀ g ∈ P.gates.take n, finiteCodeLegal (n + 1) g = true := hleg
  simp only [duplicateWord, finiteWordLegal, List.all_append, List.all_map, Bool.and_eq_true]
  constructor
  · exact List.all_eq_true.mpr (fun g hgmem =>
      finiteCodeLegal_mono (hall g hgmem) (by omega))
  · exact List.all_eq_true.mpr (fun g hgmem =>
      finiteCodeLegal_pad (n + 1) (hall g hgmem))

/-- Duplicating the generated circuit doubles both its width `n + 1` and the length of its gate
prefix. -/
theorem gen_duplicate_size (P : GateProgram) (n : ℕ) :
    (duplicateWord (n + 1) (P.gates.take n)).1 = 2 * (n + 1) ∧
      (duplicateWord (n + 1) (P.gates.take n)).2.length = 2 * (P.gates.take n).length := by
  refine ⟨?_, ?_⟩
  · rfl
  · simp only [duplicateWord, List.length_append, List.length_map]
    omega

/-- Collects well-formedness, normal form, polynomial clocking, halting, bit-machine backend,
and generator validity for the echo generator and all gate-program generators, together with
the exact generated prefixes and legality of their duplicated words. It also includes the
echo word's doubled width and finite-digit backend property, providing the local clause-six
package in the setting of [BernsteinVazirani1997]. -/
theorem clause6_complete :
    generatorWellformed echoGenerator ∧
      generatorNormalForm echoGenerator ∧
      generatorClocked echoGenerator ∧
      generatorHaltsEffectively echoGenerator ∧
      bitTmBackendPremise echoGenerator ∧
      uniformBqpGeneratorValid echoGenerator ∧
      (∀ n : ℕ, finiteWordLegal (duplicateWord (n + 1) [echoGate]).1
        (duplicateWord (n + 1) [echoGate]).2 = true) ∧
      (∀ n : ℕ, (duplicateWord (n + 1) [echoGate]).1 = 2 * (n + 1)) ∧
      (∀ n : ℕ, finiteDigitBackendPremise (n + 1, [echoGate])) ∧
      (∀ (P : GateProgram) (n : ℕ),
        uniformBqpGeneratedAt (gateProgramGenerator P) n = some (n + 1, P.gates.take n)) ∧
      (∀ P : GateProgram,
        generatorWellformed (gateProgramGenerator P) ∧
          generatorNormalForm (gateProgramGenerator P) ∧
          generatorClocked (gateProgramGenerator P) ∧
          generatorHaltsEffectively (gateProgramGenerator P) ∧
          bitTmBackendPremise (gateProgramGenerator P) ∧
          uniformBqpGeneratorValid (gateProgramGenerator P)) ∧
      (∀ (P : GateProgram) (n : ℕ),
        finiteWordLegal (duplicateWord (n + 1) (P.gates.take n)).1
          (duplicateWord (n + 1) (P.gates.take n)).2 = true) := by
  refine ⟨echo_wellformed, echo_normal_form, echo_clocked, echo_halts, echo_bitTm_backend,
    echo_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact echo_duplicate_legal n
  · intro n
    exact (echo_duplicate_size n).1
  · intro n
    exact echo_finiteDigitBackend n
  · intro P n
    exact gen_generated P n
  · intro P
    exact ⟨gen_wellformed P, gen_normal_form P, gen_clocked P, gen_halts P,
      gen_bitTm_backend P, gen_valid P⟩
  · intro P n
    exact gen_duplicate_legal P n

end UniformBqpMachine
end Qatlib.Papers.QComplexity97.MachineDefs
