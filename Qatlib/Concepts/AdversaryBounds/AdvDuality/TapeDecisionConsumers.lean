/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Mathlib.Data.List.GetD
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
# Parity decision by deterministic and randomized tape machines

`parityTapeMachine` scans a Boolean word and computes parity in a number of transitions equal to
the word length. `parityNoisyCoinMachine` first uses two coins to select a possible output flip
and then performs the same scan, giving success probability `3 / 4` and path time `x.length + 2`
for every coin assignment.

The module proves invariance under equivalences of machine labels and derives membership of
parity in `TapeInP` and of parity and its complement in `TapeInBPP`. These explicit classical
machines provide examples in the computation framework discussed in [NielsenChuang2010].

## Main statements

* `parity_tape_actual_linear_halt`: gives the deterministic parity output and exact halting
  configuration.
* `parity_noisy_coin_actual_error_and_worst_path_time`: gives success probability `3 / 4` and
  the time of every randomized path.
* `parity_real_tape_p_bpp_consumers`: establishes the stated tape-complexity memberships.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib
open Qatlib

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped BigOperators Classical

/-- The parity of a Boolean list, computed by folding exclusive-or from false. -/
def parityBool (x : List Bool) : Bool := x.foldl Bool.xor false

/-- The deterministic tape machine that accumulates exclusive-or while moving right and halts on
the first blank symbol. -/
def parityTapeMachine : Turing.TM0.Machine (Option Bool) Bool
  | _, none => none
  | q, some b => some (Bool.xor q b, Turing.TM0.Stmt.move Turing.Dir.right)

/-- A fixed left exclusive-or factor can be pulled out of a left fold of exclusive-or. -/
private theorem foldl_xor (l : List Bool) (p q : Bool) :
    (l.foldl Bool.xor (Bool.xor p q)) = Bool.xor p (l.foldl Bool.xor q) := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons]
      rw [Bool.xor_assoc]
      exact ih _

/-- The parity of `b :: l` is the exclusive-or of `b` and the parity of `l`. -/
theorem parityBool_cons (b : Bool) (l : List Bool) :
    parityBool (b :: l) = Bool.xor b (parityBool l) := by
  unfold parityBool
  rw [List.foldl_cons, Bool.false_xor]
  conv_lhs => rw [← Bool.xor_false b]
  exact foldl_xor l b false

/-- After moving right `j` times from a tape initialized by `l`, the head contains `l.getI j`. -/
theorem tape_iterate_move_right_head (l : List (Option Bool)) (j : ℕ) :
    ((Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ l)).head = l.getI j := by
  rw [Turing.Tape.move_right_n_head]
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

/-- After `j ≤ x.length` steps, the parity machine's state is the parity of the first `j` bits
and its head has moved right `j` positions. -/
theorem parityTapeMachine_after (x : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    BitMachineAfter parityTapeMachine (x.map some) j =
      some ⟨(x.take j).foldl Bool.xor false,
        (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (x.map some))⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj' : j ≤ x.length := Nat.le_of_succ_le hj
      have hjl : j < x.length := Nat.lt_of_succ_le hj
      have hhead : ((Turing.Tape.move Turing.Dir.right)^[j]
            (Turing.Tape.mk₁ (x.map some))).head = some x[j] := by
        rw [tape_iterate_move_right_head, List.getI_eq_getElem _ (by simpa using hjl)]
        simp [List.getElem_map]
      simp only [BitMachineAfter]
      rw [ih hj', Option.bind_some]
      rw [show Turing.TM0.step parityTapeMachine ⟨(x.take j).foldl Bool.xor false,
              (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (x.map some))⟩ =
            some ⟨Bool.xor ((x.take j).foldl Bool.xor false) x[j],
              ((Turing.Tape.move Turing.Dir.right)^[j]
                (Turing.Tape.mk₁ (x.map some))).move Turing.Dir.right⟩ from
          TM0_step_eq_some parityTapeMachine _ _ _ (by
            rw [show (⟨(x.take j).foldl Bool.xor false,
                  (Turing.Tape.move Turing.Dir.right)^[j]
                    (Turing.Tape.mk₁ (x.map some))⟩ :
                  Turing.TM0.Cfg (Option Bool) Bool).Tape.head = some x[j] from hhead]
            rfl)]
      congr 1
      congr 1
      · rw [List.take_succ_eq_append_getElem hjl, List.foldl_append]
        simp
      · rw [Function.iterate_succ_apply']

/-- The parity machine returns `parityBool x` at time `x.length` and is then in a configuration
whose next transition halts. -/
theorem parity_tape_actual_linear_halt :
    ∀ x : List Bool,
      parityBool x = x.foldl Bool.xor false ∧
        tapeDecision parityTapeMachine id (x.map some) x.length = some (parityBool x) ∧
          ∃ cfg : Turing.TM0.Cfg (Option Bool) Bool,
            BitMachineAfter parityTapeMachine (x.map some) x.length = some cfg ∧
              cfg.q = parityBool x ∧ Turing.TM0.step parityTapeMachine cfg = none := by
  intro x
  set Tn := (Turing.Tape.move Turing.Dir.right)^[x.length] (Turing.Tape.mk₁ (x.map some))
    with hTn
  have hafter := parityTapeMachine_after x x.length (le_refl _)
  have hheadN : Tn.head = none := by
    rw [hTn, tape_iterate_move_right_head, List.getI_eq_default _ (by simp)]
    rfl
  have hstepN : Turing.TM0.step parityTapeMachine
      ⟨(x.take x.length).foldl Bool.xor false, Tn⟩ = none := by
    rw [TM0_step_eq_none]
    rw [show (⟨(x.take x.length).foldl Bool.xor false, Tn⟩ :
          Turing.TM0.Cfg (Option Bool) Bool).Tape.head = none from hheadN]
    rfl
  have hq : (x.take x.length).foldl Bool.xor false = parityBool x := by
    simp [List.take_length, parityBool]
  refine ⟨rfl, ?_, ⟨(x.take x.length).foldl Bool.xor false, Tn⟩, hafter, hq, hstepN⟩
  rw [clocked_tape_decision_halt_and_timeout]
  exact ⟨x.length, ⟨(x.take x.length).foldl Bool.xor false, Tn⟩, le_refl _, hafter, hstepN,
    by rw [hq]; rfl⟩

/-- The control label recording the first coin of the noisy parity machine. -/
def parityNoisyStageOneLabel (c₁ : Bool) : Fin 8 :=
  ⟨1 + c₁.toNat, by cases c₁ <;> decide⟩

/-- The control label encoding a fixed noise bit and the current parity accumulator. -/
def parityNoisyScanLabel (n p : Bool) : Fin 8 :=
  ⟨3 + 2 * n.toNat + p.toNat, by cases n <;> cases p <;> decide⟩

/-- A coin-indexed tape machine that selects a noise bit from its first two coins, scans the
input parity, and halts on a blank. -/
def parityNoisyCoinMachine (coin : Bool) : Turing.TM0.Machine (Option Bool) (Fin 8)
  | ⟨0, _⟩, γ => some (⟨1 + coin.toNat, by cases coin <;> decide⟩, Turing.TM0.Stmt.write γ)
  | ⟨1, _⟩, γ => some (parityNoisyScanLabel false false, Turing.TM0.Stmt.write γ)
  | ⟨2, _⟩, γ => some (parityNoisyScanLabel coin false, Turing.TM0.Stmt.write γ)
  | ⟨3, _⟩, none => none
  | ⟨3, _⟩, some b => some (parityNoisyScanLabel false (Bool.xor false b),
      Turing.TM0.Stmt.move Turing.Dir.right)
  | ⟨4, _⟩, none => none
  | ⟨4, _⟩, some b => some (parityNoisyScanLabel false (Bool.xor true b),
      Turing.TM0.Stmt.move Turing.Dir.right)
  | ⟨5, _⟩, none => none
  | ⟨5, _⟩, some b => some (parityNoisyScanLabel true (Bool.xor false b),
      Turing.TM0.Stmt.move Turing.Dir.right)
  | ⟨6, _⟩, none => none
  | ⟨6, _⟩, some b => some (parityNoisyScanLabel true (Bool.xor true b),
      Turing.TM0.Stmt.move Turing.Dir.right)
  | ⟨_, _⟩, _ => none

/-- The acceptance map for noisy parity labels, accepting labels four and five. -/
def parityNoisyAccept : Fin 8 → Bool
  | ⟨4, _⟩ => true
  | ⟨5, _⟩ => true
  | _ => false

/-- On a scan label, the acceptance map returns the exclusive-or of the parity accumulator and
the noise bit. -/
theorem parityNoisyAccept_scanLabel (n p : Bool) :
    parityNoisyAccept (parityNoisyScanLabel n p) = Bool.xor p n := by
  cases n <;> cases p <;> rfl

/-- At label zero, the noisy parity machine records the current coin and rewrites the current
tape symbol unchanged. -/
theorem parityNoisyCoinMachine_zero (coin : Bool) (γ : Option Bool) (h : 0 < 8) :
    parityNoisyCoinMachine coin ⟨0, h⟩ γ =
      some (parityNoisyStageOneLabel coin, Turing.TM0.Stmt.write γ) := rfl

/-- At label one, the noisy parity machine begins scanning with false noise and false parity. -/
theorem parityNoisyCoinMachine_one (coin : Bool) (γ : Option Bool) (h : 1 < 8) :
    parityNoisyCoinMachine coin ⟨1, h⟩ γ =
      some (parityNoisyScanLabel false false, Turing.TM0.Stmt.write γ) := rfl

/-- At label two, the noisy parity machine begins scanning with the current coin as noise and
false parity. -/
theorem parityNoisyCoinMachine_two (coin : Bool) (γ : Option Bool) (h : 2 < 8) :
    parityNoisyCoinMachine coin ⟨2, h⟩ γ =
      some (parityNoisyScanLabel coin false, Turing.TM0.Stmt.write γ) := rfl

/-- The second setup transition selects noise equal to the conjunction of the two setup coins
and starts with false parity. -/
theorem parityNoisyCoinMachine_stageOne (coin c₁ : Bool) (γ : Option Bool) :
    parityNoisyCoinMachine coin (parityNoisyStageOneLabel c₁) γ =
      some (parityNoisyScanLabel (c₁ && coin) false, Turing.TM0.Stmt.write γ) := by
  cases c₁ <;> rfl

/-- In a scan state, a blank halts the machine; a Boolean symbol updates parity by exclusive-or
and moves the head right. -/
theorem parityNoisyCoinMachine_scanLabel (coin n p : Bool) (γ : Option Bool) :
    parityNoisyCoinMachine coin (parityNoisyScanLabel n p) γ =
      match γ with
      | none => none
      | some b => some (parityNoisyScanLabel n (Bool.xor p b),
          Turing.TM0.Stmt.move Turing.Dir.right) := by
  cases n <;> cases p <;> cases γ <;> rfl

/-- A noisy parity scan configuration satisfies `coinHalt` exactly when its tape head is blank. -/
theorem coinHalt_noisy_scan (n p : Bool) (T : Turing.Tape (Option Bool)) :
    coinHalt parityNoisyCoinMachine ⟨parityNoisyScanLabel n p, T⟩ = T.head.isNone := by
  cases h : T.head with
  | none => simp [coinHalt, parityNoisyCoinMachine_scanLabel, h]
  | some b => simp [coinHalt, parityNoisyCoinMachine_scanLabel, h]

/-- Scanning the remaining `m` input bits with `m` supplied coins consumes exactly `m` steps and
applies `accept` to the label containing the accumulated suffix parity. -/
theorem parityNoisy_scan_run (x : List Bool) (accept : Fin 8 → Bool) (noise : Bool) :
    ∀ (m : ℕ) (j : ℕ), j + m = x.length → ∀ (p : Bool) (coins : List Bool),
      coins.length = m →
      coinTapeRunAux parityNoisyCoinMachine accept coins
          ⟨parityNoisyScanLabel noise p,
            (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (x.map some))⟩ =
        (some (accept (parityNoisyScanLabel noise (Bool.xor p (parityBool (x.drop j))))), m) := by
  intro m
  induction m with
  | zero =>
      intro j hjm p coins hc
      obtain rfl : coins = [] := List.eq_nil_of_length_eq_zero hc
      have hj : j = x.length := by omega
      subst hj
      have hhead : ((Turing.Tape.move Turing.Dir.right)^[x.length]
          (Turing.Tape.mk₁ (x.map some))).head = none := by
        rw [tape_iterate_move_right_head, List.getI_eq_default _ (by simp)]
        rfl
      rw [coinTapeRunAux_of_coinHalt _ _ [] _ (by
        rw [coinHalt_noisy_scan, hhead]; rfl)]
      simp [List.drop_length, parityBool]
  | succ m ih =>
      intro j hjm p coins hc
      cases coins with
      | nil => simp at hc
      | cons c cs =>
          have hcs : cs.length = m := by
            simp only [List.length_cons] at hc
            omega
          have hjl : j < x.length := by omega
          have hhead : ((Turing.Tape.move Turing.Dir.right)^[j]
              (Turing.Tape.mk₁ (x.map some))).head = some x[j] := by
            rw [tape_iterate_move_right_head, List.getI_eq_getElem _ (by simpa using hjl)]
            simp [List.getElem_map]
          have hhalt : coinHalt parityNoisyCoinMachine
              ⟨parityNoisyScanLabel noise p,
                (Turing.Tape.move Turing.Dir.right)^[j]
                  (Turing.Tape.mk₁ (x.map some))⟩ = false := by
            rw [coinHalt_noisy_scan, hhead]
            rfl
          have hstep : Turing.TM0.step (parityNoisyCoinMachine c)
              ⟨parityNoisyScanLabel noise p,
                (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (x.map some))⟩ =
                some ⟨parityNoisyScanLabel noise (Bool.xor p x[j]),
                  ((Turing.Tape.move Turing.Dir.right)^[j]
                    (Turing.Tape.mk₁ (x.map some))).move Turing.Dir.right⟩ :=
            TM0_step_eq_some (parityNoisyCoinMachine c) _ _ _ (by
              rw [show (⟨parityNoisyScanLabel noise p,
                    (Turing.Tape.move Turing.Dir.right)^[j]
                      (Turing.Tape.mk₁ (x.map some))⟩ :
                    Turing.TM0.Cfg (Option Bool) (Fin 8)).Tape.head = some x[j] from hhead]
              rw [parityNoisyCoinMachine_scanLabel])
          rw [coinTapeRunAux_cons_of_step_some _ _ c cs _ _ hhalt hstep]
          rw [← Function.iterate_succ_apply' (Turing.Tape.move Turing.Dir.right) j
            (Turing.Tape.mk₁ (x.map some))]
          rw [ih (j + 1) (by omega) (Bool.xor p x[j]) cs hcs]
          have hdrop : parityBool (x.drop j) = Bool.xor x[j] (parityBool (x.drop (j + 1))) := by
            rw [List.drop_eq_getElem_cons hjl, parityBool_cons]
          rw [hdrop, ← Bool.xor_assoc]
          rfl

/-- A full noisy parity run uses exactly `x.length + 2` steps and returns the acceptance value
for noise `c₁ && c₂` and parity `parityBool x`. -/
theorem parityNoisy_full_run (x : List Bool) (accept : Fin 8 → Bool) (c₁ c₂ : Bool)
    (rest : List Bool) (hc : rest.length = x.length) :
    coinTapeRunAux parityNoisyCoinMachine accept (c₁ :: c₂ :: rest)
        (Turing.TM0.init (x.map some)) =
      (some (accept (parityNoisyScanLabel (c₁ && c₂) (parityBool x))), x.length + 2) := by
  have hinit : (Turing.TM0.init (x.map some) : Turing.TM0.Cfg (Option Bool) (Fin 8)) =
      ⟨⟨0, by norm_num⟩, Turing.Tape.mk₁ (x.map some)⟩ := rfl
  have hhalt0 : coinHalt parityNoisyCoinMachine
      ⟨⟨0, by norm_num⟩, Turing.Tape.mk₁ (x.map some)⟩ = false := by
    simp only [coinHalt, parityNoisyCoinMachine_zero, Option.isNone_some, Bool.false_and]
  have hstep0 : ∀ c : Bool, Turing.TM0.step (parityNoisyCoinMachine c)
      ⟨⟨0, by norm_num⟩, Turing.Tape.mk₁ (x.map some)⟩ =
        some ⟨parityNoisyStageOneLabel c, Turing.Tape.mk₁ (x.map some)⟩ := by
    intro c
    rw [TM0_step_eq_some _ _ _ _ (parityNoisyCoinMachine_zero c _ _)]
    simp [TM0StmtApply]
  rw [hinit, coinTapeRunAux_cons_of_step_some _ _ c₁ (c₂ :: rest) _ _ hhalt0 (hstep0 c₁)]
  have hhalt1 : ∀ c₁ : Bool, coinHalt parityNoisyCoinMachine
      ⟨parityNoisyStageOneLabel c₁, Turing.Tape.mk₁ (x.map some)⟩ = false := by
    intro c₁
    simp only [coinHalt, parityNoisyCoinMachine_stageOne, Option.isNone_some, Bool.false_and]
  have hstep1 : ∀ c₁ c₂ : Bool, Turing.TM0.step (parityNoisyCoinMachine c₂)
      ⟨parityNoisyStageOneLabel c₁, Turing.Tape.mk₁ (x.map some)⟩ =
        some ⟨parityNoisyScanLabel (c₁ && c₂) false, Turing.Tape.mk₁ (x.map some)⟩ := by
    intro c₁ c₂
    rw [TM0_step_eq_some _ _ _ _ (parityNoisyCoinMachine_stageOne c₂ c₁ _)]
    simp [TM0StmtApply]
  rw [coinTapeRunAux_cons_of_step_some _ _ c₂ rest _ _ (hhalt1 c₁) (hstep1 c₁ c₂)]
  rw [← Function.iterate_zero_apply (Turing.Tape.move Turing.Dir.right)
    (Turing.Tape.mk₁ (x.map some))]
  rw [parityNoisy_scan_run x accept (c₁ && c₂) x.length 0 (by omega) false rest hc]
  rw [List.drop_zero, Bool.false_xor]
  rfl

/-- Enumerating a finite function built with `Fin.cons` gives the head value followed by the
enumeration of its tail. -/
theorem ofFn_cons {α : Type*} {t : ℕ} (b : α) (v : Fin t → α) :
    List.ofFn (Fin.cons b v) = b :: List.ofFn v := by
  rw [List.ofFn_succ, Fin.cons_zero]
  congr 1

/-- Enumerating a function on `Fin (n + 2)` gives its first two values followed by the
enumeration of the twice-shifted tail. -/
theorem List_ofFn_add_two (n : ℕ) (ω : Fin (n + 2) → Bool) :
    List.ofFn ω = ω 0 :: (fun i : Fin (n + 1) => ω i.succ) 0 ::
      List.ofFn (fun i : Fin n => ω i.succ.succ) := by
  rw [List.ofFn_succ, List.ofFn_succ]

/-- Taking the first `m ≤ n` values of `List.ofFn f` agrees with enumerating the restriction of
`f` to `Fin m`. -/
theorem List_take_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (m : ℕ) (h : m ≤ n) :
    (List.ofFn f).take m = List.ofFn (fun i : Fin m => f ⟨i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left h]
  · intro i hi1 hi2
    simp [List.getElem_take]

/-- Every coin sequence of length at least `x.length + 2` makes the noisy parity machine return
a value. -/
theorem parityNoisy_all_terminate (x : List Bool) (accept : Fin 8 → Bool) :
    ∀ t : ℕ, x.length + 2 ≤ t → ∀ ω : Fin t → Bool,
      ((coinTapeRun parityNoisyCoinMachine accept (x.map some) (List.ofFn ω)).1).isSome := by
  intro t ht ω
  set m := x.length + 2 with hm
  have hmu : (List.ofFn ω).take m =
      List.ofFn (fun i : Fin m => ω ⟨i.val, by omega⟩) :=
    List_take_ofFn ω m (by omega)
  have hrun : coinTapeRunAux parityNoisyCoinMachine accept
      (List.ofFn (fun i : Fin m => ω ⟨i.val, by omega⟩))
      (Turing.TM0.init (x.map some)) =
      (some (accept (parityNoisyScanLabel (ω ⟨0, by omega⟩ && ω ⟨1, by omega⟩)
        (parityBool x))), m) := by
    rw [List_ofFn_add_two]
    exact parityNoisy_full_run x accept _ _ _ List.length_ofFn
  have happ := coinTapeRunAux_append parityNoisyCoinMachine accept
    (List.ofFn (fun i : Fin m => ω ⟨i.val, by omega⟩)) (Turing.TM0.init (x.map some))
    _ m hrun (List.drop m (List.ofFn ω))
  rw [← hmu, List.take_append_drop] at happ
  show ((coinTapeRunAux parityNoisyCoinMachine accept (List.ofFn ω)
    (Turing.TM0.init (x.map some))).1).isSome
  rw [happ]
  rfl

/-- The equivalence between a Boolean head with a `Fin t`-indexed tail and a Boolean function on
`Fin (t + 1)`. -/
def finBoolConsEquiv (t : ℕ) : Bool × (Fin t → Bool) ≃ (Fin (t + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by
    obtain ⟨b, v⟩ := p
    ext1
    · simp [Fin.cons_zero]
    · simp [Fin.tail_cons]
  right_inv w := Fin.cons_self_tail w

/-- The equivalence between two Boolean heads with a `Fin n`-indexed tail and a Boolean function
on `Fin (n + 2)`. -/
private def finBoolBoolProdEquiv (n : ℕ) : Bool × Bool × (Fin n → Bool) ≃ (Fin (n + 2) → Bool) :=
  ((Equiv.refl Bool).prodCongr (finBoolConsEquiv n)).trans (finBoolConsEquiv (n + 1))

/-- Enumerating the two-head finite-function equivalence gives the two heads followed by the
enumerated tail. -/
theorem ofFn_finBoolBoolProdEquiv (n : ℕ) (b₀ b₁ : Bool) (v : Fin n → Bool) :
    List.ofFn (finBoolBoolProdEquiv n (b₀, b₁, v)) = b₀ :: b₁ :: List.ofFn v := by
  show List.ofFn (Fin.cons b₀ (Fin.cons b₁ v)) = _
  rw [ofFn_cons, ofFn_cons]

/-- Exclusive-or with `c` leaves a Boolean `p` unchanged exactly when `c` is false. -/
private theorem xor_eq_self_iff (p c : Bool) : (Bool.xor p c = p) ↔ (c = false) := by
  cases p <;> cases c <;> decide

/-- The noisy parity machine has fair-coin success probability `3 / 4`. Every coin assignment of
length `x.length + 2` returns a value in exactly that many steps. -/
theorem parity_noisy_coin_actual_error_and_worst_path_time :
    ∀ x : List Bool,
      fairTapeSuccess parityNoisyCoinMachine parityNoisyAccept (x.map some) (x.length + 2)
          (parityBool x) = 3 / 4 ∧
        ∀ ω : Fin (x.length + 2) → Bool,
          (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
              (List.ofFn ω)).1 ≠ none ∧
            (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
              (List.ofFn ω)).2 = x.length + 2 := by
  intro x
  refine ⟨?_, fun ω => ?_⟩
  · have hF : ∀ b₀ b₁ : Bool, ∀ v : Fin x.length → Bool,
        (if (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
              (List.ofFn (finBoolBoolProdEquiv x.length (b₀, b₁, v)))).1 =
            some (parityBool x) then (1 : ℝ) else 0) =
          (if (b₀ && b₁) = false then (1 : ℝ) else 0) := by
      intro b₀ b₁ v
      rw [ofFn_finBoolBoolProdEquiv]
      rw [show coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
            (b₀ :: b₁ :: List.ofFn v) =
          (some (parityNoisyAccept (parityNoisyScanLabel (b₀ && b₁) (parityBool x))),
            x.length + 2) from
        parityNoisy_full_run x parityNoisyAccept b₀ b₁ (List.ofFn v) List.length_ofFn]
      simp only [parityNoisyAccept_scanLabel, Option.some.injEq]
      simp only [xor_eq_self_iff]
    have hconst : ∀ b₀ b₁ : Bool,
        (∑ _v : Fin x.length → Bool, (if (b₀ && b₁) = false then (1 : ℝ) else 0)) =
          2 ^ x.length * (if (b₀ && b₁) = false then (1 : ℝ) else 0) := by
      intro b₀ b₁
      simp [Finset.sum_const]
    have h3 : (∑ b₀ : Bool, ∑ b₁ : Bool, (if (b₀ && b₁) = false then (1 : ℝ) else 0)) = 3 := by
      have h3n : (∑ b₀ : Bool, ∑ b₁ : Bool, (if (b₀ && b₁) = false then (1 : ℕ) else 0)) = 3 := by
        decide
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← h3n]
      push_cast [Nat.cast_sum]
      rfl
    have hnum : (∑ ω : Fin (x.length + 2) → Bool,
          if (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
              (List.ofFn ω)).1 = some (parityBool x) then (1 : ℝ) else 0) = 2 ^ x.length * 3 := by
      calc (∑ ω : Fin (x.length + 2) → Bool,
              if (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
                  (List.ofFn ω)).1 = some (parityBool x) then (1 : ℝ) else 0)
          = ∑ p : Bool × Bool × (Fin x.length → Bool),
              if (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
                  (List.ofFn (finBoolBoolProdEquiv x.length p))).1 = some (parityBool x)
                then (1 : ℝ) else 0 :=
            (Equiv.sum_comp (finBoolBoolProdEquiv x.length) _).symm
        _ = ∑ p : Bool × Bool × (Fin x.length → Bool),
              (if (p.1 && p.2.1) = false then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            obtain ⟨b₀, b₁, v⟩ := p
            exact hF b₀ b₁ v
        _ = ∑ b₀ : Bool, ∑ q : Bool × (Fin x.length → Bool),
              (if (b₀ && q.1) = false then (1 : ℝ) else 0) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
        _ = ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ _v : Fin x.length → Bool,
              (if (b₀ && b₁) = false then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun b₀ _ => ?_
            rw [← Finset.univ_product_univ, Finset.sum_product]
        _ = ∑ b₀ : Bool, ∑ b₁ : Bool, (2 ^ x.length *
              (if (b₀ && b₁) = false then (1 : ℝ) else 0)) :=
            Finset.sum_congr rfl fun b₀ _ => Finset.sum_congr rfl fun b₁ _ => hconst b₀ b₁
        _ = 2 ^ x.length * 3 := by
            simp_rw [← Finset.mul_sum]
            rw [h3]
    unfold fairTapeSuccess
    rw [hnum]
    rw [pow_add, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (0 : ℝ) < 2).ne')]
    norm_num
  · have hr : coinTapeRun parityNoisyCoinMachine parityNoisyAccept (x.map some)
        (List.ofFn ω) =
        (some (parityNoisyAccept (parityNoisyScanLabel (ω 0 && (fun i : Fin (x.length + 1) =>
            ω i.succ) 0) (parityBool x))), x.length + 2) := by
      rw [List_ofFn_add_two x.length ω]
      exact parityNoisy_full_run x parityNoisyAccept (ω 0) ((fun i : Fin (x.length + 1) =>
          ω i.succ) 0) (List.ofFn (fun i : Fin x.length => ω i.succ.succ)) List.length_ofFn
    rw [hr]
    exact ⟨Option.some_ne_none _, rfl⟩

variable {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']

/-- Transport a tape machine's control labels along an equivalence, preserving its tape alphabet
and tape operations. -/
def TM0Relabel (e : Λ' ≃ Λ) (M : Turing.TM0.Machine Γ Λ) : Turing.TM0.Machine Γ Λ' :=
  fun l γ => (M (e l) γ).map fun p => (e.symm p.1, p.2)

/-- A step of the relabeled tape machine is the corresponding original step with its resulting
control label mapped back by the equivalence. -/
theorem step_TM0Relabel (e : Λ' ≃ Λ)
    (M : Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    Turing.TM0.step (TM0Relabel e M) ⟨e.symm cfg.q, cfg.Tape⟩ =
      (Turing.TM0.step M cfg).map fun c => ⟨e.symm c.q, c.Tape⟩ := by
  obtain ⟨q, T⟩ := cfg
  rw [TM0_step_apply, TM0_step_apply]
  simp only [TM0Relabel, Equiv.apply_symm_apply, Option.map_map]
  congr 1

/-- Bounded decision runs commute with relabeling when the acceptance map is transported along
the label equivalence. -/
theorem tapeDecisionRun_TM0Relabel (e : Λ' ≃ Λ)
    (M : Turing.TM0.Machine Γ Λ) (accept : Λ' → Bool) :
    ∀ (t : ℕ) (cfg : Turing.TM0.Cfg Γ Λ),
      tapeDecisionRun (TM0Relabel e M) accept t ⟨e.symm cfg.q, cfg.Tape⟩ =
        tapeDecisionRun M (fun l => accept (e.symm l)) t cfg := by
  intro t
  induction t with
  | zero =>
      intro cfg
      simp only [tapeDecisionRun]
      rw [step_TM0Relabel]
      simp only [Option.map_eq_none_iff]
  | succ t ih =>
      intro cfg
      simp only [tapeDecisionRun]
      rw [step_TM0Relabel]
      cases hs : Turing.TM0.step M cfg with
      | none => simp only [Option.map_none]
      | some cfg₁ =>
          simp only [Option.map_some]
          exact ih cfg₁

/-- If the label equivalence preserves the default initial label, tape decisions are unchanged
after transporting the acceptance map. -/
theorem tapeDecision_TM0Relabel (e : Λ' ≃ Λ)
    (M : Turing.TM0.Machine Γ Λ) (accept : Λ' → Bool)
    (hinit : e.symm default = default) (input : List Γ) (t : ℕ) :
    tapeDecision (TM0Relabel e M) accept input t =
      tapeDecision M (fun l => accept (e.symm l)) input t := by
  simp only [tapeDecision, Turing.TM0.init]
  conv_lhs => rw [show (default : Λ') = e.symm (default : Λ) from hinit.symm]
  exact tapeDecisionRun_TM0Relabel e M accept t ⟨default, Turing.Tape.mk₁ input⟩

/-- For every label and tape symbol, the noisy parity machine halts independently of the current
coin value. -/
theorem parityNoisyCoinMachine_halt_iff (l : Fin 8) (γ : Option Bool) :
    (parityNoisyCoinMachine false l γ = none) ↔ (parityNoisyCoinMachine true l γ = none) := by
  fin_cases l <;> cases γ with
  | none => decide
  | some b => cases b <;> decide

/-- Postcomposing the acceptance function with `g` maps the returned Boolean by `g` and
preserves the consumed-step count. -/
theorem coinTapeRunAux_accept_map (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (g : Bool → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      coinTapeRunAux M (fun l => g (accept l)) coins cfg =
        Prod.map (Option.map g) id (coinTapeRunAux M accept coins cfg) := by
  intro coins
  induction coins with
  | nil =>
      intro cfg
      by_cases hc : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt _ _ [] cfg hc, coinTapeRunAux_of_coinHalt _ _ [] cfg hc]
        rfl
      · have h' : coinHalt M cfg = false := by simpa using hc
        rw [coinTapeRunAux_nil_of_not_coinHalt _ _ cfg h',
          coinTapeRunAux_nil_of_not_coinHalt _ _ cfg h']
        rfl
  | cons c cs ih =>
      intro cfg
      by_cases hc : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt _ _ (c :: cs) cfg hc,
          coinTapeRunAux_of_coinHalt _ _ (c :: cs) cfg hc]
        rfl
      · have h' : coinHalt M cfg = false := by simpa using hc
        cases hs : Turing.TM0.step (M c) cfg with
        | none =>
            rw [coinTapeRunAux_cons_of_step_none _ _ c cs cfg h' hs,
              coinTapeRunAux_cons_of_step_none _ _ c cs cfg h' hs]
            rfl
        | some cfg' =>
            rw [coinTapeRunAux_cons_of_step_some _ _ c cs cfg cfg' h' hs,
              coinTapeRunAux_cons_of_step_some _ _ c cs cfg cfg' h' hs, ih cfg']
            rcases coinTapeRunAux M accept cs cfg' with ⟨r, k⟩
            rfl

/-- The language of odd-parity Boolean words belongs to `TapeInP` and `TapeInBPP`, and its
even-parity complement belongs to `TapeInBPP`. -/
theorem parity_real_tape_p_bpp_consumers :
    TapeInP (fun x => parityBool x = true) ∧
      TapeInBPP (fun x => parityBool x = true) ∧
        TapeInBPP (fun x => parityBool x = false) := by
  have hinit2 : (finTwoEquiv.symm default : Fin 2) = default := by decide
  have hacc2 : (fun l => finTwoEquiv (finTwoEquiv.symm l)) = id := by
    funext l
    exact Equiv.apply_symm_apply finTwoEquiv l
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, TM0Relabel finTwoEquiv parityTapeMachine, finTwoEquiv, 1, 1, fun input =>
      ⟨input.length, ?_, ?_⟩⟩
    · simp only [pow_one, one_mul]
      exact Nat.le_add_right _ _
    · rw [tapeDecision_TM0Relabel finTwoEquiv parityTapeMachine _ hinit2 (input.map some)
          input.length, hacc2]
      rw [(parity_tape_actual_linear_halt input).2.1]
      cases h : parityBool input <;> simp [h]
  · refine ⟨7, parityNoisyCoinMachine, parityNoisyAccept, 2, 1,
      parityNoisyCoinMachine_halt_iff, fun input => ?_⟩
    have hterm : ∀ ω : Fin (2 * input.length ^ 1 + 2) → Bool,
        (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (input.map some)
          (List.ofFn ω)).1 ≠ none := by
      intro ω hn
      have h := parityNoisy_all_terminate input parityNoisyAccept (2 * input.length ^ 1 + 2)
        (by simp; omega) ω
      rw [hn] at h
      simp at h
    refine ⟨hterm, ?_⟩
    have htarget : ∀ {inst : Decidable ((fun x => parityBool x = true) input)},
        @ite Bool ((fun x => parityBool x = true) input) inst true false = parityBool input := by
      intro inst
      cases h : parityBool input with
      | false => rw [if_neg (by show ¬ (parityBool input = true); rw [h]; decide)]
      | true => rw [if_pos h]
    rw [htarget]
    have hpad := fairTapeSuccess_eq_of_forall_isSome parityNoisyCoinMachine parityNoisyAccept
      (input.map some) (input.length + 2) (parityBool input)
      (fun t ht ω => parityNoisy_all_terminate input parityNoisyAccept t ht ω)
      (2 * input.length ^ 1 + 2) (by simp; omega)
    rw [hpad, (parity_noisy_coin_actual_error_and_worst_path_time input).1]
    norm_num
  · refine ⟨7, parityNoisyCoinMachine, fun l => !parityNoisyAccept l, 2, 1,
      parityNoisyCoinMachine_halt_iff, fun input => ?_⟩
    have hmap : ∀ coins : List Bool,
        coinTapeRun parityNoisyCoinMachine (fun l => !parityNoisyAccept l) (input.map some) coins =
          Prod.map (Option.map (!·)) id
            (coinTapeRun parityNoisyCoinMachine parityNoisyAccept (input.map some) coins) :=
      fun coins => coinTapeRunAux_accept_map parityNoisyCoinMachine parityNoisyAccept
        (!·) coins (Turing.TM0.init (input.map some))
    have hterm : ∀ ω : Fin (2 * input.length ^ 1 + 2) → Bool,
        (coinTapeRun parityNoisyCoinMachine (fun l => !parityNoisyAccept l) (input.map some)
          (List.ofFn ω)).1 ≠ none := by
      intro ω
      rw [hmap]
      have h := parityNoisy_all_terminate input parityNoisyAccept (2 * input.length ^ 1 + 2)
        (by simp; omega) ω
      rcases hr : coinTapeRun parityNoisyCoinMachine parityNoisyAccept (input.map some)
        (List.ofFn ω) with ⟨r₁, r₂⟩
      rw [hr] at h
      simp only [Prod.map, id_eq]
      cases r₁ with
      | none => simp at h
      | some a => simp
    refine ⟨hterm, ?_⟩
    have htarget : ∀ {inst : Decidable ((fun x => parityBool x = false) input)},
        @ite Bool ((fun x => parityBool x = false) input) inst true false = !parityBool input := by
      intro inst
      cases h : parityBool input with
      | false => rw [if_pos h]; rfl
      | true => rw [if_neg (by show ¬ (parityBool input = false); rw [h]; decide)]; rfl
    rw [htarget]
    have hflip : fairTapeSuccess parityNoisyCoinMachine (fun l => !parityNoisyAccept l)
        (input.map some) (2 * input.length ^ 1 + 2) (!parityBool input) =
        fairTapeSuccess parityNoisyCoinMachine parityNoisyAccept (input.map some)
          (2 * input.length ^ 1 + 2) (parityBool input) := by
      unfold fairTapeSuccess
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      rw [hmap]
      rcases hr : coinTapeRun parityNoisyCoinMachine parityNoisyAccept (input.map some)
        (List.ofFn ω) with ⟨r₁, r₂⟩
      simp only [Prod.map, id_eq]
      cases r₁ with
      | none => simp
      | some a => cases a <;> cases h : parityBool input <;> simp
    rw [hflip]
    have hpad := fairTapeSuccess_eq_of_forall_isSome parityNoisyCoinMachine parityNoisyAccept
      (input.map some) (input.length + 2) (parityBool input)
      (fun t ht ω => parityNoisy_all_terminate input parityNoisyAccept t ht ω)
      (2 * input.length ^ 1 + 2) (by simp; omega)
    rw [hpad, (parity_noisy_coin_actual_error_and_worst_path_time input).1]
    norm_num

end Qatlib.Concepts.AdversaryBounds.AdvDuality
