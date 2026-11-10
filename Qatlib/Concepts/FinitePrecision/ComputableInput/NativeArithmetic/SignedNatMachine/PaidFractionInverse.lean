/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.PaidPairMultiplication
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
set_option warningAsError false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidFractionInverse

inductive Slot where | arg (i : Fin 4) | raw | reader | markers | payload | temp | first | second | output
  deriving DecidableEq, Fintype
inductive Label where
  | start (l : Fin 1) | read (i : Fin 4) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Label) | discard (l : Fin 1)
  | copy (which : Bool) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.Label) | compare (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.Label)
  | clearCopy (which : Bool) (l : Fin 1) | choose | zero
  | emit (i : Fin 4) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.Label) | drain (i : Fin 4) (l : Fin 1) | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.start 0⟩
abbrev Local :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local × Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.Local
instance : Inhabited Local := ⟨(((false, none), none), ((.eq, none, none), none))⟩
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

def operands (a b c d : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Fin 4 →
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits | 0 => a | 1 => b | 2 => c | _ => d

def state (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (raw reader first second out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .arg i => args i | .raw => raw | .reader => reader | .first => first | .second => second | .output => out
  | _ => []

def getRead (v : Local) := v.1
def putRead (v : Local)
    (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local) : Local := (x, v.2)
def getCmp (v : Local) := v.2
def putCmp (v : Local)
    (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.Local) : Local :=
    (v.1, x)
def getIO (v : Local) := v.1.2
def putIO (v : Local) (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    ((v.1.1, x), v.2)
def order (v : Local) := v.2.1.1

def route : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1
def startCode : Fin 2 → Slot | 0 => .raw | _ => .reader
def readCode (i : Fin 4) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Slot → Slot
  | .reader => .reader | .markers => .markers | .payload => .payload
  | .value => .arg i | .temporary => .temp | .output => .output

def copyCode (which : Bool) : Fin 3 → Slot
  | 0 => .arg (if which then 1 else 0) | 1 => .temp | _ => if which then .second else .first

def compareCode : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.Slot → Slot
  | .first => .first | .second => .second | .temp => .temp | .left => .markers | .right => .payload

def emitCode (i : Fin 4) : Fin 3 → Slot | 0 => .arg (route i) | 1 => .temp | _ => .output

def zeroCodec : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0 ++
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0 ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1 ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0))
def input (p n r s : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p ++
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s))
def output (p n r s : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    if p = n then zeroCodec else Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n))
def afterRead (i : Fin 4) : Label :=
    if h : i.val + 1 < 4 then .read ⟨i.val + 1, h⟩ (.read .unary) else .discard 0
def afterCopy (which : Bool) : Label := if which then .compare .start else .copy true .emit

def afterEmit (i : Fin 4) : Label :=
    if h : i.val + 1 < 4 then .emit ⟨i.val + 1, h⟩ .count else .drain 0 0
def afterDrain (i : Fin 4) : Label := if h : i.val + 1 < 4 then .drain ⟨i.val + 1, h⟩ 0 else .done

def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .start l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt startCode Label.start (.read 0 (.read .unary)) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .read i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (readCode i) (Label.read i) (afterRead i) getRead putRead (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program l)
  | .discard l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (fun _ : Fin 1 => .output) Label.discard (.copy false .emit) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .copy which l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (copyCode which) (Label.copy which) (afterCopy which) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program l)
  | .compare l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt compareCode Label.compare (.clearCopy false 0) getCmp putCmp (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.program l)
  | .clearCopy which l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (fun _ : Fin 1 => if which then .second else .first) (Label.clearCopy which)
      (if which then .choose else .clearCopy true 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .choose => .branch (fun v => decide (order v = .eq)) (.goto (fun _ => .zero)) (.goto (fun _ => .emit 0 .count))
  | .zero => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.pushBits .output zeroCodec (.goto (fun _ => .drain 0 0))
  | .emit i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (emitCode i) (Label.emit i) (afterEmit i) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program l)
  | .drain i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (fun _ : Fin 1 => .arg i) (Label.drain i) (afterDrain i) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .done => .load (fun _ => default) .halt

private theorem frame_eq {K : Type} [DecidableEq K] (code : K → Slot) (hinj : Function.Injective code)
    (S T : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (data : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (hi : ∀ k, T (code k) = data k)
    (ho : ∀ j, (∀ k, code k ≠ j) → T j = S j) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code S data = T := by
  classical
  funext j
  by_cases hj : ∃ k, code k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code S data hinj k,
        hi]
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator.frame_outside code S data j (by simpa using! hj)]
    exact (ho j (by simpa using! hj)).symm

private theorem lift {K Λ σ : Type} [DecidableEq K]
    (code : K → Slot) (hinj : Function.Injective code) (labels : Λ → Label) (ret : Label)
    (get : Local → σ) (put : Local → σ → Local)
    (hg : ∀ v x, get (put v x) = x) (hp : ∀ v x y, put (put v x) y = put v y)
    (hs : ∀ v, put v (get v) = v)
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (hcode : ∀ l, program (labels l) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt code labels ret get put (M l))
    (v : Local) (S T : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (s t : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (l : Λ) (last : σ) (budget : ℕ)
    (e : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution M ⟨some l, get v, s⟩ ⟨none, last, t⟩ budget)
    (hS : ∀ k, S (code k) = s k) (hT : ∀ k, T (code k) = t k)
    (hout : ∀ j, (∀ k, code k ≠ j) → T j = S j) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (labels l), v, S⟩ ⟨some ret, put v last, T⟩ budget := by
  obtain ⟨ticks, hr, hc⟩ := e
  obtain ⟨hn, hnc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution code labels ret get put
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code S data hinj k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update code S data hinj k bits)
    hg hp M program hcode v ticks _ _ hr
  have hi :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same code S s hinj hS
  have hf := frame_eq code hinj S T t hT hout
  refine ⟨ticks, ?_, ?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none, hs, hi, hf] using! hn
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,
      Option.map_some, Option.getD_some, hs, hi] using! hnc.trans_le hc

private theorem startCode_inj  : Function.Injective (startCode) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [startCode]

private theorem readCode_inj (i : Fin 4) : Function.Injective (readCode i) := by
  intro x y h
  cases x <;> cases y <;> simp_all [readCode]

private theorem copyCode_inj (which : Bool) : Function.Injective (copyCode which) := by
  intro x y h
  cases which <;> fin_cases x <;> fin_cases y <;> simp_all [copyCode]

private theorem compareCode_inj  : Function.Injective (compareCode) := by
  intro x y h
  cases x <;> cases y <;> simp_all [compareCode]

private theorem emitCode_inj (i : Fin 4) : Function.Injective (emitCode i) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [emitCode]

def readLast (n : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local :=
    ((true, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat.lastField n.bits none),
    none)

theorem start_call (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.start 0), v, state (operands [] [] [] []) bits.reverse [] [] [] []⟩
      ⟨some (.read 0 (.read .unary)), putIO v none, state (operands [] [] [] []) [] bits [] [] []⟩
      (20 * (1 + bits.length) ^ 2) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run bits.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock bits.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift startCode startCode_inj Label.start (.read 0 (.read .unary))
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _
    ⟨bits.length + 1, hr, hc.le.trans (by nlinarith)⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

theorem read_call (i : Fin 4) (n : ℕ) (tail encoded : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (harg : args i = []) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.read i (.read .unary)), v, state args [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail) [] [] encoded⟩
      ⟨some (afterRead i), putRead v (readLast n),
        state (Function.update args i n.bits) [] tail [] [] ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ encoded)⟩
      (500 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail).length + encoded.length) ^ 2) := by
  obtain ⟨ticks, hr, hc⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.complete n tail encoded
      (getRead v)
  refine lift (readCode i) (readCode_inj i) (Label.read i) (afterRead i)
    getRead putRead (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨ticks, hr, hc⟩ ?_ ?_ ?_
  · intro k; cases k <;> simp [readCode, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.store, harg]
  · intro k; cases k <;> simp [readCode, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.store]
  · intro j hj
    cases j with
    | arg j =>
      have h : i ≠ j := fun he => hj .value (by simp [readCode, he])
      simp [state, Ne.symm h]
    | _ => first
      | rfl
      | exact (hj .reader rfl).elim
      | exact (hj .output rfl).elim

theorem discard_call (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (encoded : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.discard 0), v, state args [] [] [] [] encoded⟩
      ⟨some (.copy false .emit), putIO v none, state args [] [] [] [] []⟩
      (encoded.length ^ 2 + 3 * encoded.length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run encoded (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock encoded
      (getIO v)
  refine lift (fun _ : Fin 1 => .output) (fun _ _ _ => Subsingleton.elim _ _) Label.discard (.copy false .emit)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨encoded.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim

def copyState (which : Bool) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (word other : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  if which then state args [] [] other word [] else state args [] [] word other []

theorem copy_call (which : Bool) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bits other : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (harg : args (if which then 1 else 0) = bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.copy which .emit), v, copyState which args [] other⟩
      ⟨some (afterCopy which), putIO v none, copyState which args bits.reverse other⟩
      (25 * (1 + bits.length) ^ 2) := by
  have hr :=
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.copy_complete bits [] (getIO v)).1
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.copy_clock_bound bits []
      (getIO v)
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hr hc
  refine lift (copyCode which) (copyCode_inj which) (Label.copy which) (afterCopy which)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨2 * bits.length + 3, hr, hc⟩ ?_ ?_ ?_
  · intro k; cases which <;> fin_cases k <;> simp [copyCode, copyState, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing.triple] at * <;> exact harg
  · intro k; cases which <;> fin_cases k <;> simp [copyCode, copyState, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing.triple] at * <;> exact harg
  · intro j hj
    cases which <;> cases j <;> first | rfl | exact (hj 1 rfl).elim | exact (hj 2 rfl).elim

def cmpLast (p n : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.Local :=
    ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.order p.bits.reverse n.bits.reverse, none, none), none)

theorem compare_call (p n : ℕ) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.compare .start), v, state args [] [] p.bits.reverse n.bits.reverse []⟩
      ⟨some (.clearCopy false 0), putCmp v (cmpLast p n), state args [] [] p.bits.reverse n.bits.reverse []⟩
      (100 * (1 + p.bits.length + n.bits.length) ^ 2) := by
  obtain ⟨ticks, hr, hc⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.complete p.bits.reverse n.bits.reverse (getCmp v)
  simp only [List.length_reverse] at hc
  refine lift compareCode compareCode_inj Label.compare (.clearCopy false 0)
    getCmp putCmp (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨ticks, hr, hc⟩ ?_ ?_ ?_
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro j hj
    cases j <;> rfl

theorem clear_call (which : Bool) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bits other : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.clearCopy which 0), v, copyState which args bits other⟩
      ⟨some (if which then .choose else .clearCopy true 0), putIO v none, copyState which args [] other⟩
      (bits.length ^ 2 + 3 * bits.length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run bits (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock bits (getIO v)
  refine lift (fun _ : Fin 1 => if which then .second else .first) (fun _ _ _ => Subsingleton.elim _ _)
    (Label.clearCopy which) (if which then .choose else .clearCopy true 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨bits.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; cases which <;> rfl
  · intro k; fin_cases k; cases which <;> rfl
  · intro j hj
    cases which <;> cases j <;> first | rfl | exact (hj 0 rfl).elim

theorem emit_call (i : Fin 4) (n : ℕ) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (harg : args (route i) = n.bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.emit i .count), v, state args [] [] [] [] out⟩
      ⟨some (afterEmit i), putIO v none, state args [] [] [] [] ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ out)⟩
      (100 * (1 + n.bits.length + out.length) ^ 2) := by
  have hr :=
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.complete n out (getIO v)).1
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.clock_bound n out (getIO v)
  refine lift (emitCode i) (emitCode_inj i) (Label.emit i) (afterEmit i)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨4 * n.bits.length + 5, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> simp [emitCode, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing.triple, harg]
  · intro k; fin_cases k <;> simp [emitCode, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing.triple, harg]
  · intro j hj
    cases j <;> first | rfl | exact (hj 2 rfl).elim

theorem drain_call (i : Fin 4) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.drain i 0), v, state args [] [] [] [] out⟩
      ⟨some (afterDrain i), putIO v none, state (Function.update args i []) [] [] [] [] out⟩
      ((args i).length ^ 2 + 3 * (args i).length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run (args i)
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock (args i)
      (getIO v)
  refine lift (fun _ : Fin 1 => .arg i) (fun _ _ _ => Subsingleton.elim _ _) (Label.drain i) (afterDrain i)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨(args i).length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; simp [state]
  · intro j hj
    cases j with
    | arg j =>
      have h : i ≠ j := fun he => hj 0 (by simp [he])
      simp [state, Ne.symm h]
    | _ => rfl

theorem order_eq (p n : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.order p.bits.reverse n.bits.reverse = .eq ↔ p = n := by
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.order,
      List.reverse_reverse, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  split_ifs <;> simp_all <;> omega

theorem choose_call (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .choose, v, state args [] [] [] [] []⟩
      ⟨some (if order v = .eq then .zero else .emit 0 .count), v, state args [] [] [] [] []⟩ 1 := by
  by_cases h : order v = .eq
  all_goals refine ⟨1, ?_, ?_⟩
  all_goals simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, TM2.stepAux, program, h]

theorem zero_call (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .zero, v, state args [] [] [] [] []⟩
      ⟨some (.drain 0 0), v, state args [] [] [] [] zeroCodec.reverse⟩ 100 := by
  have hs : Function.update (state args [] [] [] [] []) Slot.output zeroCodec.reverse =
      state args [] [] [] [] zeroCodec.reverse := by
    funext j
    cases j <;> simp [state]
  refine ⟨1, ?_, ?_⟩
  · change TM2.step program ⟨some .zero, v, state args [] [] [] [] []⟩ = _
    simp only [TM2.step, program, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.pushBits_step, TM2.stepAux, state,
      List.append_nil, hs]
  · simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, program, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.pushBits_clock, zeroCodec, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits, state]

private theorem sq_fee (c r t L : ℕ) (h : r + t ≤ L) :
    c * (1 + r + t) ^ 2 ≤ c * (1 + L) ^ 2 := by
  have hs := Nat.pow_le_pow_left (show 1 + r + t ≤ 1 + L by omega) 2
  exact Nat.mul_le_mul_left c hs

private theorem double_fee (c r t L : ℕ) (h : r + t ≤ 2 * L) :
    c * (1 + r + t) ^ 2 ≤ (4 * c) * (1 + L) ^ 2 := by
  have hs := Nat.pow_le_pow_left (show 1 + r + t ≤ 2 * (1 + L) by omega) 2
  exact (Nat.mul_le_mul_left c hs).trans_eq (by ring)

private theorem drain_fee {m L : ℕ} (h : m ≤ L) : m ^ 2 + 3 * m + 3 ≤ 10 * (1 + L) ^ 2 := by
  have hs := Nat.pow_le_pow_left h 2
  nlinarith only [h, hs]

theorem finish_call (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) (L : ℕ)
    (hl : ∀ i, (args i).length ≤ L) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (.drain 0 0), v, state args [] [] [] [] out⟩
      ⟨none, default, state (operands [] [] [] []) [] [] [] [] out⟩ (50 * (1 + L) ^ 2) := by
  let d1 := Function.update args 0 []
  let d2 := Function.update d1 1 []
  let d3 := Function.update d2 2 []
  have e0 := (drain_call 0 args out v).mono (drain_fee (hl 0))
  have e1 := (drain_call 1 d1 out (putIO v none)).mono (drain_fee (hl 1))
  have e2 := (drain_call 2 d2 out (putIO v none)).mono (drain_fee (hl 2))
  have e3 := (drain_call 3 d3 out (putIO v none)).mono (drain_fee (hl 3))
  have hd : Function.update d3 3 [] = operands [] [] [] [] := by funext i; fin_cases i <;> rfl
  have ec := ((e0.trans e1).trans e2).trans e3
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program _ ⟨some .done, putIO v none, state (Function.update d3 3 []) [] [] [] [] out⟩ _ at ec
  rw [hd] at ec
  have ee : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some .done, putIO v none, state (operands [] [] [] []) [] [] [] [] out⟩
      ⟨none, default, state (operands [] [] [] []) [] [] [] [] out⟩ 1 := ⟨1, rfl, le_rfl⟩
  apply (ec.trans ee).mono
  have hp : 0 < (1 + L) ^ 2 := by positivity
  omega

theorem input_length (p n r s : ℕ) :
    (input p n r s).length = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s).length := by
  simp only [input, List.length_append]
  omega

theorem emit_swapped (p n r s : ℕ) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.emit 0 .count), v, state (operands p.bits n.bits r.bits s.bits) [] [] [] [] []⟩
      ⟨some (.drain 0 0), putIO v none, state (operands p.bits n.bits r.bits s.bits) [] [] [] []
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n))).reverse⟩
      (1600 * (1 + (input p n r s).length) ^ 2) := by
  let args := operands p.bits n.bits r.bits s.bits
  let L := (input p n r s).length
  have hlen := input_length p n r s
  have hp : p.bits.length ≤ L := by
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; dsimp only [L]; omega
  have hn : n.bits.length ≤ L := by
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; dsimp only [L]; omega
  have hr : r.bits.length ≤ L := by
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; dsimp only [L]; omega
  have hs : s.bits.length ≤ L := by
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; dsimp only [L]; omega
  have e0 :=
      (emit_call 0 r args [] v (by rfl)).mono
      (double_fee 100 _ _ L (by simp only [List.length_nil, Nat.add_zero]; omega))
  have e1 := (emit_call 1 s args (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r).reverse (putIO v none) (by rfl)).mono
    (double_fee 100 _ _ L (by simp only [List.length_reverse]; dsimp only [L]; omega))
  have e2 := (emit_call 2 p args (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s).reverse (putIO v none) (by rfl)).mono
    (double_fee 100 _ _ L (by simp only [List.length_reverse, List.length_append]; dsimp only [L]; omega))
  have e3 := (emit_call 3 n args (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p)).reverse (putIO v none) (by rfl)).mono
    (double_fee 100 _ _ L (by simp only [List.length_reverse, List.length_append]; dsimp only [L]; omega))
  simp only [List.append_nil, List.reverse_append, List.append_assoc] at e0 e1 e2 e3
  have e := ((e0.trans e1).trans e2).trans e3
  have he := e.mono (show _ ≤ 1600 * (1 + L) ^ 2 by omega)
  simpa only [List.reverse_append, List.append_assoc] using! he

theorem source_exec (p n r s : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init Slot.raw (input p n r s).reverse)
      ⟨none, default, state (operands [] [] [] []) [] [] [] [] (output p n r s).reverse⟩
      (10000 * (1 + (input p n r s).length) ^ 2) := by
  let bits := input p n r s
  let L := bits.length
  let args := operands p.bits n.bits r.bits s.bits
  let a0 := operands [] [] [] []
  let a1 := Function.update a0 0 p.bits
  let a2 := Function.update a1 1 n.bits
  let a3 := Function.update a2 2 r.bits
  let a4 := Function.update a3 3 s.bits
  let v1 := putRead (putIO default none) (readLast p)
  let v2 := putRead v1 (readLast n)
  let v3 := putRead v2 (readLast r)
  let v4 := putRead v3 (readLast s)
  have hlen := input_length p n r s
  change L = _ at hlen
  have hargs : ∀ i, (args i).length ≤ L := by
    intro i; fin_cases i
    · change p.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
    · change n.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
    · change r.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
    · change s.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
  have e0 := start_call bits default
  have e1 := (read_call 0 p (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s)) [] a0 (putIO default none) (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_nil]; omega))
  have e2 := (read_call 1 n (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p).reverse a1 v1 (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_reverse]; omega))
  have e3 := (read_call 2 r (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits s) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse a2 v2 (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_reverse]; omega))
  have e4 := (read_call 3 s [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits p ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r)).reverse a3 v3 (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_reverse, List.length_nil]; omega))
  simp only [List.append_nil, List.reverse_append, List.append_assoc] at e1 e2 e3 e4
  have er := (((e0.trans e1).trans e2).trans e3).trans e4
  have ha4 : a4 = args := by funext i; fin_cases i <;> rfl
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program _ ⟨some (.discard 0), v4, state a4 [] [] [] [] _⟩ _ at er
  rw [ha4] at er
  simp only [← List.reverse_append] at er
  simp only [List.append_assoc] at er
  have ed :=
      (discard_call args bits.reverse v4).mono
      (drain_fee (show bits.reverse.length ≤ L by simp only [List.length_reverse]; exact le_refl _))
  have ec0 := (copy_call false args p.bits [] v4 (by rfl)).mono
    (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.add_le_add_left (hargs 0) 1) 2))
  have ec1 := (copy_call true args n.bits p.bits.reverse v4 (by rfl)).mono
    (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.add_le_add_left (hargs 1) 1) 2))
  have ecmp :=
      (compare_call p n args v4).mono
      (sq_fee 100 _ _ L (by simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega))
  let v5 := putCmp v4 (cmpLast p n)
  have ed0 := (clear_call false args p.bits.reverse n.bits.reverse v5).mono
    (drain_fee (show p.bits.reverse.length ≤ L by simpa only [List.length_reverse] using! hargs 0))
  have ed1 := (clear_call true args n.bits.reverse [] v5).mono
    (drain_fee (show n.bits.reverse.length ≤ L by simpa only [List.length_reverse] using! hargs 1))
  have ech := choose_call args v5
  have hc : order v5 = .eq ↔ p = n := by
    change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare.order p.bits.reverse n.bits.reverse = .eq ↔ p = n; exact order_eq p n
  simp only [hc] at ech
  have eb := (((((((er.trans ed).trans ec0).trans ec1).trans ecmp).trans ed0).trans ed1).trans ech)
  have hi : (TM2.init Slot.raw bits.reverse : Config) = ⟨some (.start 0), default, state a0 bits.reverse [] [] [] []⟩ := by
    have hS : Function.update (fun _ => []) Slot.raw bits.reverse = state a0 bits.reverse [] [] [] [] := by
      funext j
      cases j with
      | arg i => fin_cases i <;> simp [state, a0, operands]
      | _ => simp [state]
    change (⟨some (.start 0), default, Function.update (fun _ => []) Slot.raw bits.reverse⟩ : Config) = _
    rw [hS]
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init Slot.raw bits.reverse)
    ⟨none, default, state a0 [] [] [] [] (output p n r s).reverse⟩ (10000 * (1 + L) ^ 2)
  rw [hi]
  by_cases hz : p = n
  · simp only [if_pos hz] at eb
    have e := (eb.trans (zero_call args v5)).trans (finish_call args zeroCodec.reverse v5 L hargs)
    have he := e.mono (show _ ≤ 10000 * (1 + L) ^ 2 by
      have hp : 0 < (1 + L) ^ 2 := by positivity
      dsimp only [L, bits] at hp ⊢
      omega)
    simpa only [output, if_pos hz] using! he
  · simp only [if_neg hz] at eb
    have em := emit_swapped p n r s v5
    have e := (eb.trans em).trans (finish_call args _ v5 L hargs)
    have he := e.mono (show _ ≤ 10000 * (1 + L) ^ 2 by
      have hp : 0 < (1 + L) ^ 2 := by positivity
      dsimp only [L, bits] at hp ⊢
      omega)
    simpa only [output, if_neg hz] using! he

theorem zeroCodec_length : zeroCodec.length = 6 := by decide +kernel

theorem output_length (p n r s : ℕ) : (output p n r s).length ≤ (input p n r s).length + 2 := by
  have hl := input_length p n r s
  have hm : 4 ≤ (input p n r s).length := by
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hl; omega
  by_cases hz : p = n
  · simp only [output, if_pos hz, zeroCodec_length]
    omega
  · simp only [output, if_neg hz, List.length_append]
    omega

theorem raw_inverse :
    ∃ (q coef : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < coef ∧ ∀ p n r s : ℕ,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input p n r s) (output p n r s)
        (coef * (1 + (input p n r s).length) ^ 2)
        (coef * (1 + (input p n r s).length) ^ 2) := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler program Slot.raw Slot.output
  refine ⟨q, 20000 * C, M, Nat.mul_pos (by decide) hC, ?_⟩
  intro p n r s
  obtain ⟨ticks, hr, hc⟩ := source_exec p n r s
  have he (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : state (operands [] [] [] []) [] [] [] [] bits =
      Function.update (fun _ => []) Slot.output bits := by
    funext j
    cases j with
    | arg i => fin_cases i <;> simp [state, operands]
    | _ => simp [state]
  rw [he] at hr
  have hh := hM (input p n r s) (output p n r s) ticks default hr
  have hout : 1 + (output p n r s).length ≤ 3 * (1 + (input p n r s).length) := by
    have hl := output_length p n r s
    omega
  have hout2 := Nat.pow_le_pow_left hout 2
  have hb : C * ((1 + (input p n r s).length) ^ 2 +
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks (TM2.init Slot.raw (input p n r s).reverse) +
      (1 + (output p n r s).length) ^ 2) ≤
      20000 * C * (1 + (input p n r s).length) ^ 2 := by
    have hm : (1 + (input p n r s).length) ^ 2 +
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks (TM2.init Slot.raw (input p n r s).reverse) +
        (1 + (output p n r s).length) ^ 2 ≤
        20000 * (1 + (input p n r s).length) ^ 2 := by
      nlinarith only [hc, hout2]
    exact (Nat.mul_le_mul_left C hm).trans_eq (by ring)
  exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hh hb hb

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidFractionInverse
