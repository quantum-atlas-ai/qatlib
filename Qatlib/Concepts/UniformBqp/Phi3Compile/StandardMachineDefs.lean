/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision
import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Qatlib.Concepts.AdversaryBounds.AdvDuality.TapeDecisionConsumers
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeStandardDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.WalkFind.SearchAlgorithm.FiniteBasisPadding
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGate
import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGateDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationQuan
import Qatlib.Foundations.StandardModel.WindowSim.Theorem2QtmCircuitSimulationQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.ClockedOracle.StackProgram
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
namespace StandardMachine

open Matrix

inductive BoundedGate (n : ℕ) where
  | x (i : Fin n)
  | cx (c t : Fin n)
  | ccx (a b c : Fin n)
  deriving DecidableEq

def BoundedGate.arity {n : ℕ} : BoundedGate n → ℕ
  | .x _ => 1
  | .cx _ _ => 2
  | .ccx _ _ _ => 3

def BoundedGate.act {n : ℕ} : BoundedGate n → Reg n → Reg n
  | .x i => fun x => Function.update x i (x i ^^ true)
  | .cx c t => fun x => Function.update x t (x t ^^ x c)
  | .ccx a b c => fun x => Function.update x c (x c ^^ (x a && x b))

def BoundedGate.wellformed {n : ℕ} : BoundedGate n → Prop
  | .x _ => True
  | .cx c t => c ≠ t
  | .ccx a b c => c ≠ a ∧ c ≠ b

def BoundedGate.support {n : ℕ} : BoundedGate n → List (Fin n)
  | .x i => [i]
  | .cx c t => [c, t]
  | .ccx a b c => [a, b, c]

def BoundedGate.wordSupport {n : ℕ} : List (BoundedGate n) → List (Fin n)
  | [] => []
  | g :: l => g.support ++ BoundedGate.wordSupport l

theorem BoundedGate.act_involutive {n : ℕ} (g : BoundedGate n) (hg : g.wellformed) :
    Function.Involutive (g.act : Reg n → Reg n) := by
  cases g with
  | x i =>
      intro x
      apply funext
      intro w
      by_cases hw : w = i
      · subst hw
        simp [BoundedGate.act, Function.update]
      · simp [BoundedGate.act, Function.update, hw]
  | cx c t =>
      intro x
      apply funext
      intro w
      by_cases hw : w = t
      · subst hw
        have hct : c ≠ w := hg
        simp [BoundedGate.act, Function.update, hct]
      · simp [BoundedGate.act, Function.update, hw]
  | ccx a b c =>
      intro x
      apply funext
      intro w
      by_cases hw : w = c
      · subst hw
        have hca : w ≠ a := hg.1
        have hcb : w ≠ b := hg.2
        have hca' : a ≠ w := fun h => hca h.symm
        have hcb' : b ≠ w := fun h => hcb h.symm
        simp [BoundedGate.act, Function.update, hca', hcb']
      · simp [BoundedGate.act, Function.update, hw]

noncomputable def BoundedGate.matrix {n : ℕ} (g : BoundedGate n) : Matrix (Reg n) (Reg n) ℂ :=
  permMatrix g.act

def BoundedGate.run {n : ℕ} : List (BoundedGate n) → Reg n → Reg n
  | [], reg => reg
  | g :: l, reg => BoundedGate.run l (g.act reg)

noncomputable def BoundedGate.wordMatrix {n : ℕ} : List (BoundedGate n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: l => BoundedGate.wordMatrix l * g.matrix

def addrWire (m : ℕ) {n : ℕ} (w : Fin n) : Fin (n + m) := Fin.castAdd m w

def ancWire (n : ℕ) {m : ℕ} (a : Fin m) : Fin (n + m) := Fin.natAdd n a

theorem addrWire_val (m : ℕ) {n : ℕ} (w : Fin n) : (addrWire m w).val = w.val := rfl

theorem ancWire_val (n : ℕ) {m : ℕ} (a : Fin m) : (ancWire n a).val = n + a.val := rfl

theorem addrWire_ne_ancWire (n m : ℕ) (w : Fin n) (a : Fin m) : addrWire m w ≠ ancWire n a := by
  intro h
  have hv := congrArg Fin.val h
  simp only [addrWire_val, ancWire_val] at hv
  omega

def ancOf {n m : ℕ} : List (Fin n × Fin m) → List (Fin m)
  | [] => []
  | (_, a) :: rest => a :: ancOf rest

def lastPair {n m : ℕ} : List (Fin n × Fin m) → Option (Fin n × Fin m)
  | [] => none
  | [p] => some p
  | _ :: q :: rest => lastPair (q :: rest)

def conjChain {n m : ℕ} (prev : Fin m) : List (Fin n × Fin m) → List (BoundedGate (n + m))
  | [] => []
  | (c, a) :: rest => .ccx (ancWire n prev) (addrWire m c) (ancWire n a) :: conjChain a rest

def conjAccum {n m : ℕ} (l : List (Fin n × Fin m)) (prev : Fin m) :
    List (BoundedGate (n + m)) :=
  conjChain prev l

def conjLadder {n m : ℕ} : List (Fin n × Fin m) → List (BoundedGate (n + m))
  | [] => []
  | (c, a) :: rest => .cx (addrWire m c) (ancWire n a) :: conjAccum rest a

def ladderChain {n m : ℕ} : List (Fin n × Fin m) → Reg (n + m) → Bool
  | [], _ => true
  | (c, _) :: rest, x => x (addrWire m c) && ladderChain rest x

def ladderWires {n m : ℕ} (l : List (Fin n × Fin m)) : List (Fin (n + m)) :=
  (ancOf l).map (ancWire n) ++ (l.map (fun p => addrWire m p.1))

def PairsDisjoint {n m : ℕ} (l : List (Fin n × Fin m)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, p = q ∨ (p.1 ≠ q.1 ∧ p.2 ≠ q.2)

def ctrlConjAll {n m : ℕ} (l : List (Fin n × Fin m)) (x : Reg (n + m)) : Bool :=
  (l.map (fun p => x (addrWire m p.1))).all id

def otherWires {n : ℕ} (t : Fin n) : List (Fin n) :=
  (List.finRange n).erase t

theorem otherWires_mem {n : ℕ} (t : Fin n) {w : Fin n} :
    w ∈ otherWires t ↔ w ≠ t := by
  rw [otherWires, List.Nodup.mem_erase_iff (List.nodup_finRange n)]
  simp

theorem otherWires_length {n : ℕ} (t : Fin n) : (otherWires t).length = n - 1 := by
  unfold otherWires
  rw [List.length_erase_of_mem (List.mem_finRange t)]
  simp

def mcxPairs {n : ℕ} (t : Fin n) : List (Fin n × Fin (n - 1)) :=
  List.zip (otherWires t) (List.finRange (n - 1))

def patternFix {n : ℕ} (m : ℕ) (p : Reg n) (t : Fin n) : List (BoundedGate (n + m)) :=
  ((otherWires t).filter (fun w => p w = false)).map (fun w => .x (addrWire m w))

def mcxProgramAll {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) :
    List (BoundedGate (n + m)) :=
  match lastPair l with
  | none => [.x (addrWire m t)]
  | some (_, a) =>
      let ladder := conjLadder l
      ladder ++ [.cx (ancWire n a) (addrWire m t)] ++ ladder.reverse

def mcxAllPerm {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) (x : Reg (n + m)) : Reg (n + m) :=
  if ∀ c ∈ l.map (fun q => q.1), x (addrWire m c) then
    Function.update x (addrWire m t) (x (addrWire m t) ^^ true)
  else x

def mcxProgram {n : ℕ} (t : Fin n) (p : Reg n) : List (BoundedGate (n + (n - 1))) :=
  let fix := patternFix (n - 1) p t
  match lastPair (mcxPairs t) with
  | none => [.x (addrWire (n - 1) t)]
  | some (_, a) =>
      let ladder := conjLadder (mcxPairs t)
      fix ++ ladder ++ [.cx (ancWire n a) (addrWire (n - 1) t)] ++ ladder.reverse ++ fix.reverse

def mcxPerm {n m : ℕ} (t : Fin n) (p : Reg n) (x : Reg (n + m)) : Reg (n + m) :=
  if ∀ w : Fin n, w ≠ t → x (addrWire m w) = p w then
    Function.update x (addrWire m t) (x (addrWire m t) ^^ true)
  else x

inductive DLambdaOp (n : ℕ) where
  | hGate (i : Fin n)
  | tGate (i : Fin n)
  | tGateAdj (i : Fin n)
  | cnot (c t : Fin n)
  deriving DecidableEq

def DLambdaOp.arity {n : ℕ} : DLambdaOp n → ℕ
  | .hGate _ => 1
  | .tGate _ => 1
  | .tGateAdj _ => 1
  | .cnot _ _ => 2

def DLambdaOp.wires {n : ℕ} : DLambdaOp n → Finset (Fin n)
  | .hGate i => {i}
  | .tGate i => {i}
  | .tGateAdj i => {i}
  | .cnot c t => {c, t}

def dLambdaValid : ∀ {n : ℕ}, DLambdaOp n → Prop
  | _, .hGate _ => True
  | _, .tGate _ => True
  | _, .tGateAdj _ => True
  | _, .cnot c t => c ≠ t

noncomputable def dLambdaReflection : ∀ {n : ℕ}, DLambdaOp n → ReflectionGate n
  | _, .hGate i => Sum.inl (i, Hadamard)
  | _, .tGate i => Sum.inl (i, tGate)
  | _, .tGateAdj i => Sum.inl (i, tGateAdj)
  | _, .cnot c t => Sum.inr (c, t)

theorem dLambdaReflection_legal {n : ℕ} {op : DLambdaOp n} (h : dLambdaValid op) :
    reflectionGateLegal (dLambdaReflection op) := by
  cases op with
  | hGate i => simp [dLambdaReflection, reflectionGateLegal, hadamard_unitary]
  | tGate i => simp [dLambdaReflection, reflectionGateLegal, tGate_mem_unitary]
  | tGateAdj i => simp [dLambdaReflection, reflectionGateLegal, tGateAdj_mem_unitary]
  | cnot c t => simp only [dLambdaReflection, reflectionGateLegal]; exact h

noncomputable def dLambdaCircuit {n : ℕ} (ops : List (DLambdaOp n)) : Circuit (Reg n) :=
  reflectionCompile (ops.map dLambdaReflection)

def dLambdaNot {n : ℕ} (i : Fin n) : List (DLambdaOp n) :=
  [.hGate i, .tGate i, .tGate i, .tGate i, .tGate i, .hGate i]

def dLambdaToffoli {n : ℕ} (a b t : Fin n) : List (DLambdaOp n) :=
  [.hGate t, .cnot b t, .tGateAdj t, .cnot a t, .tGate t, .cnot b t, .tGateAdj t,
    .cnot a t, .tGate b, .tGate t, .hGate t, .cnot a b, .tGate a, .tGateAdj b,
    .cnot a b]

def ClockedSize (q m : ℕ) : ℕ := (m + 1) * (q + 1)

instance clockedSizeNeZero (q m : ℕ) : NeZero (ClockedSize q m) := by
  refine ⟨?_⟩
  simp only [ClockedSize]
  exact Nat.mul_ne_zero (Nat.succ_ne_zero m) (Nat.succ_ne_zero q)

def clockedLabel {q m : ℕ} (i : Fin (m + 1)) (j : Fin (q + 1)) : Fin (ClockedSize q m) :=
  ⟨i.val * (q + 1) + j.val, by
    have hi : i.val * (q + 1) ≤ m * (q + 1) :=
      Nat.mul_le_mul_right (q + 1) (Nat.le_pred_of_lt i.isLt)
    have hj : j.val ≤ q := Nat.le_pred_of_lt j.isLt
    have hlt : m * (q + 1) + q < (m + 1) * (q + 1) := by
      rw [Nat.succ_mul]
      omega
    simp only [ClockedSize]
    omega⟩

@[simp] theorem clockedLabel_val {q m : ℕ} (i : Fin (m + 1)) (j : Fin (q + 1)) :
    (clockedLabel i j).val = i.val * (q + 1) + j.val := rfl

def clockedPhase {q m : ℕ} (l : Fin (ClockedSize q m)) : Fin (m + 1) :=
  ⟨l.val / (q + 1), by
    have hlt : l.val < (m + 1) * (q + 1) := by
      simpa only [ClockedSize] using! l.isLt
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)]
    exact hlt⟩

def clockedBase {q m : ℕ} (l : Fin (ClockedSize q m)) : Fin (q + 1) :=
  ⟨l.val % (q + 1), Nat.mod_lt _ (Nat.succ_pos q)⟩

theorem clockedLabel_div_mod {q m : ℕ} (i : Fin (m + 1)) (j : Fin (q + 1)) :
    (clockedLabel i j).val / (q + 1) = i.val ∧ (clockedLabel i j).val % (q + 1) = j.val := by
  rw [clockedLabel_val]
  constructor
  · have h := Nat.div_add_mod' (i.val * (q + 1) + j.val) (q + 1)
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt] at h
    have hdiv : (i.val * (q + 1) + j.val) / (q + 1) * (q + 1) = i.val * (q + 1) := by
      omega
    exact Nat.mul_right_cancel (by omega : 0 < q + 1) hdiv
  · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]

theorem clockedPhase_label {q m : ℕ} (i : Fin (m + 1)) (j : Fin (q + 1)) :
    clockedPhase (clockedLabel i j) = i := by
  apply Fin.ext
  exact (clockedLabel_div_mod i j).1

theorem clockedBase_label {q m : ℕ} (i : Fin (m + 1)) (j : Fin (q + 1)) :
    clockedBase (clockedLabel i j) = j := by
  apply Fin.ext
  exact (clockedLabel_div_mod i j).2

def clockedMachine {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))) (m : ℕ) :
    Turing.TM0.Machine (Option Bool) (Fin (ClockedSize q m)) :=
  fun l γ =>
    let j := clockedBase l
    let i := clockedPhase l
    if h : i.val < m then
      (M j γ).map fun p => (clockedLabel ⟨i.val + 1, by omega⟩ p.1, p.2)
    else
      none

def clockedAccept {q m : ℕ} (accept : Fin (q + 1) → Bool) : Fin (ClockedSize q m) → Bool :=
  fun l => accept (clockedBase l)

def clockedCoinMachine {q : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1))) (m : ℕ) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (ClockedSize q m)) :=
  fun c => clockedMachine (M c) m

def clockedCoinAccept {q m : ℕ} (accept : Fin (q + 1) → Bool) : Fin (ClockedSize q m) → Bool :=
  clockedAccept accept

def scanClockMachine : Turing.TM0.Machine (Option Bool) (Fin 1) :=
  fun _ γ =>
    match γ with
    | some _ => some (0, Turing.TM0.Stmt.move Turing.Dir.right)
    | none => none

def scanClockAccept : Fin 1 → Bool := fun _ => false

theorem clockedLabel_decompose {q m : ℕ} (l : Fin (ClockedSize q m)) :
    l = clockedLabel (clockedPhase l) (clockedBase l) := by
  apply Fin.ext
  simp only [clockedLabel_val, clockedPhase, clockedBase]
  exact (Nat.div_add_mod' l.val (q + 1)).symm

def clockedPhaseOf {m : ℕ} (i : ℕ) (h : i ≤ m) : Fin (m + 1) :=
  ⟨i, Nat.lt_succ_of_le h⟩

open Qatlib
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal

structure GeneralNativeMachine (Q A : Type) [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] where

  rule : Rule Q A

  start : Q

  stayFree : stayFree rule

  wellformed : rule.GloballyWellformed

def GeneralNativeMachine.localQTM {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) : LocalQTM Q A :=
  toLocalQTM M.rule M.start M.stayFree M.wellformed

theorem GeneralNativeMachine.fiveConditions {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) :
    LocalQTMFiveConditions M.localQTM :=
  toLocalQTM_fiveConditions M.rule M.start M.stayFree M.wellformed

theorem GeneralNativeMachine.adjacentCombined {Q A : Type} [Fintype Q]
    [DecidableEq Q] [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A)
    (q₁ q₂ : Q) (a₁ a₂ : A) (c d : A) :
    ∑ q' : Q,
      (star (M.localQTM.step q₁ a₁ QtmMove.right q' c) * M.localQTM.step q₂ a₂ QtmMove.stay q' d
        + star (M.localQTM.step q₁ a₁ QtmMove.stay q' c) * M.localQTM.step q₂ a₂ QtmMove.left q' d) = 0 :=
  qtm_adjacent_combined_of_global M.rule M.wellformed q₁ q₂ a₁ a₂ c d

theorem two_pow_ge_self : ∀ n : ℕ, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    by_cases hn : n = 0
    · subst n
      simp
    · have h2 : n + 1 ≤ 2 * n := by omega
      calc n + 1 ≤ 2 * n := h2
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ n * 2 := by ring

theorem cellState_card (Q A : Type) [Fintype Q] [Fintype A] :
    Fintype.card (CellState Q A) = 3 * (Fintype.card Q + 1) * Fintype.card A := by
  simp [CellState, Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.mul_assoc]

theorem cellState_card_cases (Q A : Type) [Fintype Q] [Fintype A] :
    Fintype.card (CellState Q A) = 0 ∨ 2 ≤ Fintype.card (CellState Q A) := by
  rw [cellState_card]
  by_cases hA : Fintype.card A = 0
  · left
    simp [hA]
  · right
    have hA1 : 1 ≤ Fintype.card A := by omega
    have hQ1 : 1 ≤ Fintype.card Q + 1 := by omega
    have h3 : 3 ≤ 3 * (Fintype.card Q + 1) := Nat.mul_le_mul_left 3 hQ1
    have h4 : 1 * 3 ≤ Fintype.card A * (3 * (Fintype.card Q + 1)) :=
      Nat.mul_le_mul hA1 h3
    have h5 : 3 * (Fintype.card Q + 1) * Fintype.card A
        = Fintype.card A * (3 * (Fintype.card Q + 1)) := by ring
    omega

def cellBasisWidth (Q A : Type) [Fintype Q] [Fintype A] : ℕ :=
  Fintype.card (CellState Q A)

theorem cellBasisWidth_bound (Q A : Type) [Fintype Q] [Fintype A] :
    Fintype.card (CellState Q A) ≤ 2 ^ cellBasisWidth Q A :=
  two_pow_ge_self _

noncomputable def generalBasisCode (Q A : Type) [Fintype Q] [Fintype A] :
    CellState Q A → Reg (cellBasisWidth Q A) :=
  finiteBasisCode (CellState Q A) (cellBasisWidth Q A) (cellBasisWidth_bound Q A)

theorem generalBasisCode_injective (Q A : Type) [Fintype Q] [Fintype A] :
    Function.Injective (generalBasisCode Q A) :=
  finiteBasisCode_injective (cellBasisWidth_bound Q A)

def generalWindowSize (n t : ℕ) : ℕ := max t n

theorem generalWindowSize_ge_t (n t : ℕ) : t ≤ generalWindowSize n t := le_max_left _ _

theorem generalWindowSize_ge_n (n t : ℕ) : n ≤ generalWindowSize n t := le_max_right _ _

def generalWindowCells (n t : ℕ) : ℕ := 2 * generalWindowSize n t + 1

def generalRegisterWidth (Q A : Type) [Fintype Q] [Fintype A] (n t : ℕ) : ℕ :=
  generalWindowCells n t * cellBasisWidth Q A + 3

end StandardMachine
end Qatlib.Concepts.UniformBqp.Phi3Compile
