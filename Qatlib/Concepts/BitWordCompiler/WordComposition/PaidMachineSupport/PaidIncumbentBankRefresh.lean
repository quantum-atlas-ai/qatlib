/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.BankRefresh

inductive Slot where
  | bank (b : Bool)
  | incoming
  | temp
  deriving DecidableEq, Fintype

inductive Label where
  | start
  | drain (target : Bool) (l : Fin 1)
  | transfer (target : Bool) (restore : Bool) (l : Fin 1)
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.start⟩

abbrev Local := Bool × Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

def getIO (v : Local) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol := v.2
def putIO (v : Local) (bit : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) :
    Local := (v.1, bit)
def state (banks : Bool → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (incoming temp : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .bank b => banks b
  | .incoming => incoming
  | .temp => temp

def drainCode (target : Bool) : Fin 1 → Slot := fun _ => .bank target
def transferCode (target restore : Bool) : Fin 2 → Slot
  | 0 => if restore then .temp else .incoming
  | _ => if restore then .bank target else .temp
def afterTransfer (target restore : Bool) : Label :=
  if restore then .done else .transfer target true 0

def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .start => .goto (fun v => .drain (!v.1) 0)
  | .drain target l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (drainCode target) (Label.drain target)
      (.transfer target false 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .transfer target restore l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (transferCode target restore)
      (Label.transfer target restore) (afterTransfer target restore)
      getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .done => .load (fun v => (v.1, none)) .halt

private theorem drainCode_inj (target : Bool) : Function.Injective (drainCode target) := by
  intro a b _
  exact Subsingleton.elim a b

private theorem transferCode_inj (target restore : Bool) :
    Function.Injective (transferCode target restore) := by
  cases restore <;> intro a b h <;> fin_cases a <;> fin_cases b <;>
    simp [transferCode] at h ⊢

private theorem frame_eq {K : Type} [DecidableEq K] (code : K → Slot)
    (hinj : Function.Injective code) (S T : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (data : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits)
    (hi : ∀ k, T (code k) = data k)
    (ho : ∀ j, (∀ k, code k ≠ j) → T j = S j) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code S data = T := by
  classical
  funext j
  by_cases h : ∃ k, code k = j
  · obtain ⟨k, rfl⟩ := h
    rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code S data hinj k,
        hi]
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator.frame_outside code S data j (by simpa using h)]
    exact (ho j (by simpa using h)).symm

private theorem lift {K Λ : Type} [DecidableEq K]
    (code : K → Slot) (hinj : Function.Injective code) (labels : Λ → Label)
    (ret : Label) (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol)
    (hcode : ∀ l, program (labels l) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt code labels ret getIO putIO (M l))
    (v : Local) (S T : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (s t : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (l : Λ) (last : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol)
    (budget : ℕ)
    (e : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution M ⟨some l, getIO v, s⟩ ⟨none, last, t⟩ budget)
    (hS : ∀ k, S (code k) = s k) (hT : ∀ k, T (code k) = t k)
    (hout : ∀ j, (∀ k, code k ≠ j) → T j = S j) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (labels l), v, S⟩
      ⟨some ret, putIO v last, T⟩ budget := by
  obtain ⟨ticks, hr, hc⟩ := e
  obtain ⟨hR, hC⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution code labels ret getIO putIO
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code S) (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code S data hinj k)
    (fun data k bit => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update code S data hinj k bit)
    (fun _ _ => rfl) (fun _ _ _ => rfl) M program hcode v ticks _ _ hr
  have hi :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same code S s hinj hS
  have hf := frame_eq code hinj S T t hT hout
  have hv : putIO v (getIO v) = v := by cases v; rfl
  refine ⟨ticks, ?_, ?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg, Option.map_some, Option.getD_some,
      Option.map_none, Option.getD_none, hv, hi, hf] using hR
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg, Option.map_some, Option.getD_some, hv, hi]
      using hC.trans_le hc

def budget (old incoming : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : ℕ :=
  1 + (old.length ^ 2 + 3 * old.length + 3) +
    (incoming.length * (2 * incoming.length + 5) + 3) +
    (incoming.length * (2 * incoming.length + 5) + 3) + 1

theorem source_exec (active : Bool) (banks : Bool → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (incoming : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some .start, (active, none), state banks incoming []⟩
      ⟨none, (active, none), state (Function.update banks (!active) incoming) [] []⟩
      (budget (banks (!active)) incoming) := by
  let target := !active
  let cleared := Function.update banks target []
  let S0 := state banks incoming []
  let S1 := state cleared incoming []
  let S2 := state cleared [] incoming.reverse
  let S3 := state (Function.update banks target incoming) [] []
  have start : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .start, (active, none), S0⟩
      ⟨some (.drain target 0), (active, none), S0⟩ 1 := ⟨1, rfl, le_rfl⟩
  have ed : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram
      ⟨some 0, none, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack (banks target)⟩
      ⟨none, none, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack []⟩
      ((banks target).length ^ 2 + 3 * (banks target).length + 3) :=
    ⟨(banks target).length + 1, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run _ _, (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock _ _).le⟩
  have drain := lift (drainCode target) (drainCode_inj target) (Label.drain target)
    (.transfer target false 0) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl)
    (active, none) S0 S1 (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack (banks target))
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack []) 0 none _ ed
    (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; simp [S1, state, cleared, drainCode, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack])
    (by
      intro j hj
      cases j with
      | bank b =>
          have h : b ≠ target := by intro h; subst b; exact hj 0 rfl
          simp [S0, S1, state, cleared, Function.update_of_ne h]
      | incoming | temp => rfl)
  have et : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram
      ⟨some 0, none, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair incoming []⟩
      ⟨none, none, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] incoming.reverse⟩
      (incoming.length * (2 * incoming.length + 5) + 3) := by
    refine ⟨incoming.length + 1, ?_, ?_⟩
    · simpa only [List.append_nil] using
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run incoming [] none
    · simpa only [List.length_nil, Nat.add_zero] using
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock incoming [] none).le
  have transfer := lift (transferCode target false) (transferCode_inj target false)
    (Label.transfer target false) (afterTransfer target false) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram
    (fun _ => rfl) (active, none) S1 S2 (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair incoming [])
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] incoming.reverse) 0 none _ et
    (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl)
    (by
      intro j hj
      cases j with
      | bank _ => rfl
      | incoming => exact (hj 0 rfl).elim
      | temp => exact (hj 1 rfl).elim)
  have er : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram
      ⟨some 0, none, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair incoming.reverse []⟩
      ⟨none, none, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] incoming⟩
      (incoming.length * (2 * incoming.length + 5) + 3) := by
    refine ⟨incoming.reverse.length + 1, ?_, ?_⟩
    · simpa only [List.reverse_reverse, List.append_nil] using
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run incoming.reverse [] none
    · simpa only [List.length_reverse, List.length_nil, Nat.add_zero] using
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock incoming.reverse [] none).le
  have restore := lift (transferCode target true) (transferCode_inj target true)
    (Label.transfer target true) (afterTransfer target true) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram
    (fun _ => rfl) (active, none) S2 S3 (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair incoming.reverse [])
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] incoming) 0 none _ er
    (by intro k; fin_cases k <;> simp [S2, state, transferCode, cleared, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair])
    (by intro k; fin_cases k <;> simp [S3, state, transferCode, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair])
    (by
      intro j hj
      cases j with
      | bank b =>
          have h : b ≠ target := by intro h; subst b; exact hj 1 rfl
          simp [S2, S3, state, cleared, Function.update_of_ne h]
      | incoming => rfl
      | temp => exact (hj 0 rfl).elim)
  have done : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .done, (active, none), S3⟩
      ⟨none, (active, none), S3⟩ 1 := ⟨1, rfl, le_rfl⟩
  simpa only [getIO, putIO, afterTransfer, Bool.false_eq_true, if_false, if_true,
    target, S0, S3, budget] using (((start.trans drain).trans transfer).trans restore).trans done

theorem budget_bound (old incoming : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    budget old incoming ≤ 20 * (1 + old.length + incoming.length) ^ 2 := by
  dsimp [budget]
  nlinarith [Nat.zero_le (old.length * incoming.length)]

theorem active_preserved (active : Bool) (banks : Bool → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (incoming : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    state (Function.update banks (!active) incoming) [] [] (.bank active) = banks active := by
  cases active <;> simp [state]

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.BankRefresh
