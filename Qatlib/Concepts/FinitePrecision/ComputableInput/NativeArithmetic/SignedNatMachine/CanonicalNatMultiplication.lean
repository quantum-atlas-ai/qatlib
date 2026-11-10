/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.PaidBinaryMultiplication
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.CanonicalNatMultiplication

inductive Slot where
  | raw | reader | markers | payload | first | second | result | temp | output
  deriving DecidableEq, Fintype
inductive Label where
  | start (l : Fin 1) | read (which : Bool) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Label)
  | clear (l : Fin 1) | multiply (l : PaidBinaryMultiplication.Label) | normalize (l : Fin 1)
  | reverse (l : Fin 1) | emit (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.Label) | drain (l : Fin 1) | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.start 0⟩
abbrev Local :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local × PaidBinaryMultiplication.Local
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

def state (raw reader markers payload first second result temp output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .raw => raw | .reader => reader | .markers => markers | .payload => payload
  | .first => first | .second => second | .result => result | .temp => temp | .output => output

def getRead (v : Local) := v.1
def putRead (v : Local)
    (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local) : Local := (x, v.2)
def getMultiply (v : Local) := v.2
def putMultiply (v : Local) (x : PaidBinaryMultiplication.Local) : Local := (v.1, x)
def getIO (v : Local) := v.2.2
def putIO (v : Local) (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    (v.1, v.2.1, x)

def startCode : Fin 2 → Slot | 0 => .raw | _ => .reader
def readCode (which : Bool) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Slot → Slot
  | .reader => .reader | .markers => .markers | .payload => .payload
  | .value => if which then .second else .first | .temporary => .temp | .output => .output
def clearCode (_ : Fin 1) : Slot := .output
def multiplyCode : PaidBinaryMultiplication.Slot → Slot
  | .left => .first | .right => .second | .acc => .payload | .temp => .temp
  | .copy => .raw | .arg => .markers | .sum => .reader | .output => .result
def normalizeCode (_ : Fin 1) : Slot := .result
def reverseCode : Fin 2 → Slot | 0 => .result | _ => .first
def emitCode : Fin 3 → Slot | 0 => .first | 1 => .temp | _ => .output
def drainCode (_ : Fin 1) : Slot := .first

def afterRead (which : Bool) : Label := if which then .clear 0 else .read true (.read .unary)

def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .start l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt startCode Label.start (.read false (.read .unary)) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .read which l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (readCode which) (Label.read which) (afterRead which) getRead putRead (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program l)
  | .clear l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt clearCode Label.clear (.multiply .loop) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .multiply l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt multiplyCode Label.multiply (.normalize 0) getMultiply putMultiply (PaidBinaryMultiplication.program l)
  | .normalize l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt normalizeCode Label.normalize (.reverse 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryNormalize.program l)
  | .reverse l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt reverseCode Label.reverse (.emit .count) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .emit l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt emitCode Label.emit (.drain 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program l)
  | .drain l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt drainCode Label.drain .done getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
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

private theorem startCode_inj : Function.Injective (startCode) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [startCode]

private theorem readCode_inj (which : Bool) : Function.Injective (readCode which) := by
  cases which <;> intro x y h <;> cases x <;> cases y <;> simp_all [readCode]

private theorem clearCode_inj : Function.Injective (clearCode) := by
  intro x y _
  exact Subsingleton.elim x y

private theorem multiplyCode_inj : Function.Injective multiplyCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [multiplyCode]

private theorem normalizeCode_inj : Function.Injective (normalizeCode) := by
  intro x y _
  exact Subsingleton.elim x y

private theorem reverseCode_inj : Function.Injective (reverseCode) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [reverseCode]

private theorem emitCode_inj : Function.Injective (emitCode) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [emitCode]

private theorem drainCode_inj : Function.Injective (drainCode) := by
  intro x y _
  exact Subsingleton.elim x y

def readLast (n : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local :=
    ((true, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat.lastField n.bits none),
    none)
def operandState (which : Bool) (reader value other out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  state [] reader [] [] (if which then other else value) (if which then value else other) [] [] out

theorem read_call (which : Bool) (n : ℕ) (tail other out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.read which (.read .unary)), v, operandState which (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail) [] other out⟩
      ⟨some (afterRead which), putRead v (readLast n), operandState which tail n.bits other ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ out)⟩
      (500 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail).length + out.length) ^ 2) := by
  obtain ⟨ticks, hr, hc⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.complete n tail out
      (getRead v)
  refine lift (readCode which) (readCode_inj which) (Label.read which) (afterRead which)
    getRead putRead (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨ticks, hr, hc⟩ ?_ ?_ ?_
  · intro k; cases which <;> cases k <;> rfl
  · intro k; cases which <;> cases k <;> rfl
  · intro j hj
    cases which <;> cases j <;> first
    | rfl
    | exact (hj .reader rfl).elim
    | exact (hj .markers rfl).elim
    | exact (hj .payload rfl).elim
    | exact (hj .value rfl).elim
    | exact (hj .temporary rfl).elim
    | exact (hj .output rfl).elim

theorem start_call (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.start 0), v, state (input.reverse) [] [] [] [] [] [] [] []⟩
      ⟨some (.read false (.read .unary)), putIO v none, state [] (input) [] [] [] [] [] [] []⟩
      (input.length * (2 * input.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run input.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock input.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift startCode startCode_inj Label.start (.read false (.read .unary))
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨input.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim

theorem clear_call (a b out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.clear 0), v, state [] [] [] [] (a) (b) [] [] (out)⟩
      ⟨some (.multiply .loop), putIO v none, state [] [] [] [] (a) (b) [] [] []⟩
      (out.length ^ 2 + 3 * out.length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run out (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock out (getIO v)
  refine lift clearCode clearCode_inj Label.clear (.multiply .loop)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨out.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim

theorem multiply_call (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) (h : getMultiply v = default) : ∃ result,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.multiply .loop), v, state [] [] [] [] a b [] [] []⟩
      ⟨some (.normalize 0), putMultiply v default, state [] [] [] [] [] [] result.reverse [] []⟩
      (4000 * (a.length + b.length + 1) ^ 3) ∧
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue result = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b ∧ result.length ≤ a.length + 2 * b.length := by
  obtain ⟨result, ticks, hr, hc, hv, hl⟩ := PaidBinaryMultiplication.source_multiplier a b
  have e : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution PaidBinaryMultiplication.program
      ⟨some .loop, getMultiply v, PaidBinaryMultiplication.state a b [] [] [] [] [] []⟩
      ⟨none, default, PaidBinaryMultiplication.state [] [] [] [] [] [] [] result.reverse⟩
      (4000 * (a.length + b.length + 1) ^ 3) := by
    simpa only [h] using!
        (⟨ticks, hr, hc⟩ : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution PaidBinaryMultiplication.program _ _ _)
  refine ⟨result, ?_, hv, hl⟩
  refine lift multiplyCode multiplyCode_inj Label.multiply (.normalize 0)
    getMultiply putMultiply (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    PaidBinaryMultiplication.program (fun _ => rfl) v _ _ _ _ _ _ _ e ?_ ?_ ?_
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj .left rfl).elim
    | exact (hj .right rfl).elim
    | exact (hj .acc rfl).elim
    | exact (hj .temp rfl).elim
    | exact (hj .copy rfl).elim
    | exact (hj .arg rfl).elim
    | exact (hj .sum rfl).elim
    | exact (hj .output rfl).elim

theorem reverse_call (n : ℕ) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.reverse 0), v, state [] [] [] [] [] [] (n.bits.reverse) [] []⟩
      ⟨some (.emit .count), putIO v none, state [] [] [] [] (n.bits) [] [] [] []⟩
      (n.bits.length * (2 * n.bits.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run n.bits.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock n.bits.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift reverseCode reverseCode_inj Label.reverse (.emit .count)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨n.bits.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim

theorem emit_call (n : ℕ) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.emit .count), v, state [] [] [] [] (n.bits) [] [] [] []⟩
      ⟨some (.drain 0), putIO v none, state [] [] [] [] (n.bits) [] [] [] ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse)⟩
      (100 * (1 + n.bits.length) ^ 2) := by
  have hr :=
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.complete n [] (getIO v)).1
  have hc := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.clock_bound n [] (getIO v)
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hr hc
  refine lift emitCode emitCode_inj Label.emit (.drain 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨4 * n.bits.length + 5, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim
    | exact (hj 2 rfl).elim

theorem drain_call (n : ℕ) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.drain 0), v, state [] [] [] [] (n.bits) [] [] [] ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse)⟩
      ⟨some (.done), putIO v none, state [] [] [] [] [] [] [] [] ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse)⟩
      (n.bits.length ^ 2 + 3 * n.bits.length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run n.bits (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock n.bits
      (getIO v)
  refine lift drainCode drainCode_inj Label.drain (.done)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨n.bits.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim

theorem normalize_call (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) : ∃ last,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.normalize 0), v, state [] [] [] [] [] [] bits [] []⟩
      ⟨some (.reverse 0), putIO v last,
        state [] [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue bits.reverse).bits.reverse [] []⟩
      (20 * (1 + bits.length) ^ 2) := by
  obtain ⟨ticks, last, hr, hc⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryNormalize.complete bits (getIO v)
  refine ⟨last, ?_⟩
  refine lift normalizeCode normalizeCode_inj Label.normalize (.reverse 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryNormalize.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨ticks, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim

private theorem budget_le (L S R N : ℕ) (hs : S ≤ 1 + L) (hr : R ≤ 1 + L) (hn : N ≤ 1 + L) :
    L * (2 * L + 5) + 3 + 500 * (1 + L) ^ 2 + 500 * (1 + L) ^ 2 +
      (L ^ 2 + 3 * L + 3) + 4000 * S ^ 3 + 20 * (1 + R) ^ 2 +
      (N * (2 * N + 5) + 3) + 100 * (1 + N) ^ 2 + (N ^ 2 + 3 * N + 3) + 1 ≤
        20000 * (1 + L) ^ 3 := by
  have hs3 := Nat.pow_le_pow_left hs 3
  have hr2 := Nat.pow_le_pow_left hr 2
  have hn2 := Nat.pow_le_pow_left hn 2
  have h23 := Nat.pow_le_pow_right (show 0 < 1 + L by omega) (by decide : 2 ≤ 3)
  have h3 : 0 < (1 + L) ^ 3 := by positivity
  nlinarith only [hs3, hr, hr2, hn, hn2, h23, h3]

theorem product_bits_length (a b : ℕ) : (a * b).bits.length ≤ a.bits.length + 2 * b.bits.length := by
  obtain ⟨result, _, _, _, hv, hl⟩ := PaidBinaryMultiplication.source_multiplier a.bits b.bits
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryNormalize.canonical_length result
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits] at hv
  rw [hv] at hc
  exact hc.trans hl

theorem source_exec (a b : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      (TM2.init Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse)
      ⟨none, default, state [] [] [] [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).reverse⟩
      (20000 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 3) := by
  let input :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b
  let v1 := putRead (putIO default none) (readLast a)
  let v2 := putRead v1 (readLast b)
  let v3 := putIO v2 none
  let v4 := putMultiply v3 default
  have e0 := start_call input default
  have e1 :=
      read_call false a (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b) [] []
      (putIO default none)
  have e2 :=
      read_call true b [] a.bits
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).reverse v1
  have e3 :=
      clear_call a.bits b.bits
      ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).reverse) v2
  obtain ⟨r, e4, hv, hl⟩ := multiply_call a.bits b.bits v3 (by rfl)
  obtain ⟨last, e5⟩ := normalize_call r.reverse v4
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits] at hv
  simp only [List.reverse_reverse, hv] at e5
  let v5 := putIO v4 last
  have e6 := reverse_call (a * b) v5
  let v6 := putIO v5 none
  have e7 := emit_call (a * b) v6
  let v7 := putIO v6 none
  have e8 := drain_call (a * b) v7
  let v8 := putIO v7 none
  have e9 : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some .done, v8, state [] [] [] [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).reverse⟩
      ⟨none, default, state [] [] [] [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).reverse⟩ 1 :=
    ⟨1, rfl, le_rfl⟩
  have e01 := e0.trans e1
  have e012 := e01.trans (by simpa only [List.append_nil] using! e2)
  have e03 := e012.trans (by simpa only [List.nil_append] using! e3)
  have e04 := e03.trans e4
  have e05 := e04.trans e5
  have e06 := e05.trans e6
  have e07 := e06.trans e7
  have e08 := e07.trans e8
  have e09 := e08.trans e9
  have hi : (TM2.init Slot.raw input.reverse : Config) =
      ⟨some (.start 0), default, state input.reverse [] [] [] [] [] [] [] []⟩ := by
    have he : Function.update (fun _ => []) Slot.raw input.reverse =
        state input.reverse [] [] [] [] [] [] [] [] := by
      funext j
      cases j <;> simp [state]
    change (⟨some (.start 0), default, Function.update (fun _ => []) Slot.raw input.reverse⟩ : Config) = _
    rw [he]
  rw [hi]
  apply e09.mono
  have hfields : input.length = 2 * (a.bits.length + b.bits.length) + 2 := by
    simp only [input, List.length_append,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length]
    omega
  have hsum : a.bits.length + b.bits.length + 1 ≤ 1 + input.length := by omega
  have hr : r.length ≤ 1 + input.length := by omega
  have hp := product_bits_length a b
  have hn : (a * b).bits.length ≤ 1 + input.length := by omega
  simp only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero]
  have hlen1 :
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).length +
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length = input.length := by
        simp only [input, List.length_append]
  rw [show 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).length = 1 + input.length by omega,
    hlen1, show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).length = input.length by omega]
  exact budget_le input.length (a.bits.length + b.bits.length + 1) r.length
      (a * b).bits.length hsum hr hn

theorem raw_multiplier :
    ∃ (q c : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < c ∧ ∀ a b : ℕ,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b))
        (c * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 3)
        (c * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 3) := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler program Slot.raw Slot.output
  refine ⟨q, 40000 * C, M, Nat.mul_pos (by decide) hC, ?_⟩
  intro a b
  obtain ⟨steps, hr, hc⟩ := source_exec a b
  have he (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : state [] [] [] [] [] [] [] [] bits =
      Function.update (fun _ => []) Slot.output bits := by
    funext j
    cases j <;> simp [state]
  rw [he] at hr
  have hh :=
      hM (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)) steps default hr
  have hout : 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).length ≤ 4 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) := by
    have hn := product_bits_length a b
    simp only [List.length_append, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length]
    omega
  have hout2 := Nat.pow_le_pow_left hout 2
  have h23 :=
      Nat.pow_le_pow_right
      (show 0 < 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length by omega) (by decide : 2 ≤ 3)
  have hb : C * ((1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 2 +
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse) +
      (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).length) ^ 2) ≤
      40000 * C * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 3 := by
    have hm : (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 2 +
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse) +
        (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).length) ^ 2 ≤
        40000 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 3 := by
      nlinarith only [hc, hout2, h23]
    exact (Nat.mul_le_mul_left C hm).trans_eq (by ring)
  exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hh hb hb

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.CanonicalNatMultiplication
