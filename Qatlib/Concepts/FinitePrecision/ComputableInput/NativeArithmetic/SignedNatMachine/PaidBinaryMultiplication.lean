/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.BinaryProductDefs

/-!
# Binary multiplication with explicit stack costs

`program` implements binary multiplication by conditional addition and shifting, calling the
framed binary adder on each true multiplier bit. `loop_exec` relates the machine execution to
`BinaryProductDefs.loop` while tracking stack-clock cost.

`source_multiplier` supplies a terminating computation, the product-value identity, and an
output-length bound. Its stack-clock estimate is cubic in the total operand length.

## Main statements

* `step_exec`: one conditional addition and shift with a quadratic span bound.
* `loop_exec`: execution of the entire multiplication loop.
* `source_multiplier`: a binary product word with cubic cost and a linear length bound.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidBinaryMultiplication

/-- The eight Boolean-stack slots for the operands, accumulator, copying and addition workspace,
and output. -/
inductive Slot where | left | right | acc | temp | copy | arg | sum | output deriving DecidableEq, Fintype
/-- Control labels for the multiplier loop, copying, addition, restoration, shifting, and
cleanup. -/
inductive Label where
  | loop | copy (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.Label) | copyTransfer (l : Fin 1) | add (l : Fin 3)
  | restore (l : Fin 1) | shift | clear (l : Fin 1) | finish (l : Fin 1) | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.loop⟩
/-- The framed-adder local state together with an optional Boolean symbol for stack subroutines. -/
abbrev Local :=
    FramedBinaryAddition.Local × Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol
/-- Configurations of the binary multiplication stack machine. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

/-- Construct a stack state from the two operands, accumulator, temporary words, and output. -/
def state (a b acc temp copy arg sum output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .left => a | .right => b | .acc => acc | .temp => temp
  | .copy => copy | .arg => arg | .sum => sum | .output => output

/-- Extract the framed binary adder component of the local state. -/
def getAdd (v : Local) := v.1
/-- Replace the framed binary adder component while preserving the optional input and output
symbol. -/
def putAdd (v : Local) (x : FramedBinaryAddition.Local) : Local := (x, v.2)
/-- Extract the optional Boolean symbol used by the input and output subroutines. -/
def getIO (v : Local) := v.2
/-- Replace the optional Boolean symbol used by the input and output subroutines while
preserving the remaining local data. -/
def putIO (v : Local) (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    (v.1, x)

/-- Embed the copying subroutine using the left operand, temporary, and copy slots. -/
def copyCode : Fin 3 → Slot | 0 => .left | 1 => .temp | _ => .copy
/-- Embed the transfer from the copy slot to the addition-argument slot. -/
def copyTransferCode : Fin 2 → Slot | 0 => .copy | _ => .arg
/-- Embed the framed adder using the output slot as input, the accumulator and argument as
operands, and the sum slot as output. -/
def addCode : Fin 4 → Slot | 0 => .output | 1 => .acc | 2 => .arg | _ => .sum
/-- Embed the transfer from the sum slot back to the accumulator. -/
def restoreCode : Fin 2 → Slot | 0 => .sum | _ => .acc
/-- Select the left-operand slot for cleanup after the multiplier is exhausted. -/
def clearCode (_ : Fin 1) : Slot := .left
/-- Embed the final transfer from the accumulator to the output slot. -/
def finishCode : Fin 2 → Slot | 0 => .acc | _ => .output

/-- The binary shift-and-add multiplication program, including operand copying, addition calls,
and workspace cleanup. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .loop => .pop .right putIO (.branch (fun v => (getIO v).isSome)
      (.branch (fun v => (getIO v).getD false) (.goto (fun _ => .copy .emit)) (.goto (fun _ => .shift)))
      (.goto (fun _ => .clear 0)))
  | .copy l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt copyCode Label.copy (.copyTransfer 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program l)
  | .copyTransfer l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt copyTransferCode Label.copyTransfer (.add 2) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .add l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt addCode Label.add (.restore 0) getAdd putAdd (FramedBinaryAddition.program l)
  | .restore l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt restoreCode Label.restore .shift getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .shift => .push .left (fun _ => false) (.goto (fun _ => .loop))
  | .clear l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt clearCode Label.clear (.finish 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .finish l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt finishCode Label.finish .done getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .done => .load (fun _ => default) .halt

/-- A stack frame equals a target state when they agree on every embedded slot and the target
preserves every slot outside the embedding. -/
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

/-- Lift a terminating subroutine execution to the enclosing program with the same cost bound,
using an injective stack embedding and compatible local-state accessors. Slots outside the
embedding retain their contents. -/
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

/-- `copyCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem copyCode_inj : Function.Injective copyCode := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [copyCode]

/-- `copyTransferCode` is injective, so distinct subroutine stacks occupy distinct machine
slots. -/
private theorem copyTransferCode_inj : Function.Injective copyTransferCode := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [copyTransferCode]

/-- `addCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem addCode_inj : Function.Injective addCode := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [addCode]

/-- `restoreCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem restoreCode_inj : Function.Injective restoreCode := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [restoreCode]

/-- `clearCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem clearCode_inj : Function.Injective clearCode := by
  intro x y _
  exact Subsingleton.elim x y

/-- `finishCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem finishCode_inj : Function.Injective finishCode := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [finishCode]

/-- Copy the left operand into the copy slot in reversed order, preserving the operands and
accumulator, within `25 * (1 + a.length) ^ 2` cost. -/
theorem copy_call (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.copy .emit), v, state (a) (b) (acc) [] [] [] [] []⟩
      ⟨some (.copyTransfer 0), putIO v none, state (a) (b) (acc) [] (a.reverse) [] [] []⟩
      (25 * (1 + a.length) ^ 2) := by
  have hr :=
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.copy_complete a [] (getIO v)).1
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.copy_clock_bound a [] (getIO v)
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hr hc
  refine lift copyCode copyCode_inj Label.copy (.copyTransfer 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨2 * a.length + 3, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim
    | exact (hj 2 rfl).elim

/-- Transfer the reversed copy into the addition-argument slot and enter the adder, with the
displayed quadratic cost bound. -/
theorem copyTransfer_call (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.copyTransfer 0), v, state (a) (b) (acc) [] (a.reverse) [] [] []⟩
      ⟨some (.add 2), putIO v none, state (a) (b) (acc) [] [] (a) [] []⟩
      (a.length * (2 * a.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run a.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock a.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift copyTransferCode copyTransferCode_inj Label.copyTransfer (.add 2)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨a.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim

/-- With the adder local state initialized, consume the accumulator and copied argument to
produce their reversed sum in the sum slot within the stated quadratic bound. -/
theorem add_call (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) (h : getAdd v = default) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.add 2), v, state (a) (b) (acc) [] [] (a) [] []⟩
      ⟨some (.restore 0), putAdd v default, state (a) (b) [] [] [] [] ((PaidBinaryAddition.output acc a).reverse) []⟩
      (30 * (acc.length + a.length + 1) ^ 2) := by
  have e : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution FramedBinaryAddition.program
      ⟨some 2, getAdd v, FramedBinaryAddition.state [] acc a []⟩
      ⟨none, default, FramedBinaryAddition.state [] [] [] (PaidBinaryAddition.output acc a).reverse⟩
      (30 * (acc.length + a.length + 1) ^ 2) := by
    simpa only [h, List.length_nil, Nat.add_zero, List.append_nil, pow_two, Nat.mul_assoc]
      using! FramedBinaryAddition.add_exec acc a false []
  refine lift addCode addCode_inj Label.add (.restore 0)
    getAdd putAdd (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    FramedBinaryAddition.program (fun _ => rfl) v _ _ _ _ _ _ _ e ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim
    | exact (hj 2 rfl).elim
    | exact (hj 3 rfl).elim

/-- Transfer the reversed sum back to the accumulator and enter the shift phase within the
stated cost bound. -/
theorem restore_call (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.restore 0), v, state (a) (b) [] [] [] [] (acc.reverse) []⟩
      ⟨some (.shift), putIO v none, state (a) (b) (acc) [] [] [] [] []⟩
      (acc.length * (2 * acc.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run acc.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock acc.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift restoreCode restoreCode_inj Label.restore (.shift)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨acc.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim

/-- Clear the shifted left operand after the right operand is exhausted, preserving the
accumulator and entering the final transfer. -/
theorem clear_call (a acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.clear 0), v, state (a) [] (acc) [] [] [] [] []⟩
      ⟨some (.finish 0), putIO v none, state [] [] (acc) [] [] [] [] []⟩
      (a.length ^ 2 + 3 * a.length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run a (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock a (getIO v)
  refine lift clearCode clearCode_inj Label.clear (.finish 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨a.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim

/-- Transfer the accumulator to the output in reversed order and reach the final label within
the stated cost bound. -/
theorem finish_call (acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (Label.finish 0), v, state [] [] (acc) [] [] [] [] []⟩
      ⟨some (.done), putIO v none, state [] [] [] [] [] [] [] (acc.reverse)⟩
      (acc.length * (2 * acc.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run acc [] (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock acc [] (getIO v)
  simp only [List.length_nil, Nat.add_zero, List.append_nil] at hr hc
  refine lift finishCode finishCode_inj Label.finish (.done)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨acc.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj 0 rfl).elim
    | exact (hj 1 rfl).elim

/-- Updating the right-operand slot in a loop state replaces only that operand. -/
private theorem right_update (a b acc rest : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (state a b acc [] [] [] [] []) Slot.right rest = state a rest acc [] [] [] [] [] := by
  funext j
  cases j <;> simp [state]

/-- Updating the left-operand slot in a loop state replaces only that operand. -/
private theorem left_update (a b acc rest : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (state a b acc [] [] [] [] []) Slot.left rest = state rest b acc [] [] [] [] [] := by
  funext j
  cases j <;> simp [state]

/-- Pop the next multiplier bit and branch to copying for a true bit or directly to shifting for
a false bit. -/
theorem loop_step (a bs acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bit : Bool) (v : Local) :
    TM2.step program ⟨some .loop, v, state a (bit :: bs) acc [] [] [] [] []⟩ =
      some ⟨some (if bit then .copy .emit else .shift), putIO v (some bit), state a bs acc [] [] [] [] []⟩ := by
  cases bit <;> simp [TM2.step, program, TM2.stepAux, getIO, putIO, right_update, state]

/-- Popping a multiplier bit has stack-clock cost `2 * bs.length + 4`. -/
theorem loop_clock (a bs acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bit : Bool) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some .loop, v, state a (bit :: bs) acc [] [] [] [] []⟩ =
      2 * bs.length + 4 := by
  cases bit <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, TM2.step, program, TM2.stepAux,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, state, getIO, putIO] <;> omega

/-- An empty right operand sends the multiplication loop to cleanup with an empty optional
symbol. -/
theorem loop_stop (a acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    TM2.step program ⟨some .loop, v, state a [] acc [] [] [] [] []⟩ =
      some ⟨some (.clear 0), putIO v none, state a [] acc [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, state, getIO, putIO]

/-- Detecting the exhausted multiplier has stack-clock cost three. -/
theorem loop_stop_clock (a acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some .loop, v, state a [] acc [] [] [] [] []⟩ = 3 := by
  simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, TM2.step,
      program, TM2.stepAux, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, state, getIO, putIO]

/-- The shift phase prefixes a false bit to the left operand and returns to the multiplication
loop. -/
theorem shift_step (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    TM2.step program ⟨some .shift, v, state a b acc [] [] [] [] []⟩ =
      some ⟨some .loop, v, state (false :: a) b acc [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, left_update, state]

/-- Shifting the left operand has stack-clock cost `2 * a.length + 4`. -/
theorem shift_clock (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some .shift, v, state a b acc [] [] [] [] []⟩ = 2 * a.length + 4 := by
  simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, TM2.step,
      program, TM2.stepAux, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, state]
  omega

/-- A single machine step with an exact stack-clock cost gives an execution bounded by that
cost. -/
private theorem one (s t : Config) (c : ℕ) (hr : TM2.step program s = some t)
    (hc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 s = c) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program s t c :=
  ⟨1, (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_one program s).trans hr, hc.le⟩

/-- Bound the costs of a multiplier iteration by `1000 * Q ^ 2` when the relevant word lengths
satisfy the stated bounds by `Q`. -/
private theorem step_budget (A L C R Q : ℕ)
    (hA : A + 1 ≤ Q) (hL : L ≤ Q) (hC : C + 1 ≤ Q) (hR : R + 1 ≤ Q) :
    2 * L + 4 + 25 * (1 + A) ^ 2 + (A * (2 * A + 5) + 3) +
      30 * (C + A + 1) ^ 2 + (R * (2 * R + 5) + 3) + (2 * A + 4) ≤ 1000 * Q ^ 2 := by
  have hA2 := Nat.pow_le_pow_left (show A ≤ Q by omega) 2
  have hR2 := Nat.pow_le_pow_left (show R ≤ Q by omega) 2
  have h1 := Nat.pow_le_pow_left (show 1 + A ≤ Q by omega) 2
  have h2 := Nat.pow_le_pow_left (show C + A + 1 ≤ 2 * Q by omega) 2
  have hQQ : Q ≤ Q ^ 2 := Nat.le_pow (by decide)
  nlinarith only [hA, hL, hR, hA2, hR2, h1, h2, hQQ]

/-- Bound the exhausted-multiplier cleanup costs by `1000 * Q ^ 2` under the stated operand and
accumulator bounds. -/
private theorem base_budget (A C Q : ℕ) (hQ : 1 ≤ Q) (hA : A + 1 ≤ Q) (hC : C + 1 ≤ Q) :
    3 + (A ^ 2 + 3 * A + 3) + (C * (2 * C + 5) + 3) + 1 ≤ 1000 * Q ^ 2 := by
  have hA2 := Nat.pow_le_pow_left (show A ≤ Q by omega) 2
  have hC2 := Nat.pow_le_pow_left (show C ≤ Q by omega) 2
  have hQQ : Q ≤ Q ^ 2 := Nat.le_pow (by decide)
  nlinarith only [hQ, hA, hC, hA2, hC2, hQQ]

/-- One multiplier iteration consumes a bit, conditionally adds the left operand to the
accumulator, and shifts the left operand. Its cost is bounded by `1000 *
BinaryProductDefs.span a (bit :: bs) acc ^ 2`. -/
theorem step_exec (a bs acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bit : Bool) (io : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : ∃ last,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some .loop, (default, io), state a (bit :: bs) acc [] [] [] [] []⟩
      ⟨some .loop, (default, last),
        state (false :: a) bs (if bit then PaidBinaryAddition.output acc a else acc) [] [] [] [] []⟩
      (1000 * BinaryProductDefs.span a (bit :: bs) acc ^ 2) := by
  have e0 :=
      one _ _ _ (loop_step a bs acc bit (default, io)) (loop_clock a bs acc bit (default, io))
  have hQ := BinaryProductDefs.span_pos a (bit :: bs) acc
  have hlen := BinaryProductDefs.current_lengths a (bit :: bs) acc
  have hb : bs.length ≤ BinaryProductDefs.span a (bit :: bs) acc := by
    unfold BinaryProductDefs.span
    simp only [List.length_cons]
    omega
  cases bit with
  | false =>
    have e1 :=
        one _ _ _ (shift_step a bs acc (default, some false))
        (shift_clock a bs acc (default, some false))
    refine ⟨some false, ?_⟩
    apply (e0.trans e1).mono
    have hQQ :
        BinaryProductDefs.span a (false :: bs) acc ≤ BinaryProductDefs.span a
        (false :: bs) acc ^ 2 := Nat.le_pow (by decide)
    nlinarith only [hQ, hlen.1, hb, hQQ]
  | true =>
    let r := PaidBinaryAddition.output acc a
    have e1 := copy_call a bs acc (default, some true)
    have e2 := copyTransfer_call a bs acc (default, none)
    have e3 := add_call a bs acc (default, none) (by rfl)
    have e4 := restore_call a bs r (default, none)
    have e5 := one _ _ _ (shift_step a bs r (default, none)) (shift_clock a bs r (default, none))
    have e := ((((e0.trans e1).trans e2).trans e3).trans e4).trans e5
    refine ⟨none, e.mono ?_⟩
    have hr : r.length + 1 ≤ BinaryProductDefs.span a (true :: bs) acc := by
      have hh := BinaryProductDefs.add_length acc a
      unfold BinaryProductDefs.span
      simp only [List.length_cons]
      dsimp only [r]
      omega
    exact step_budget a.length bs.length acc.length r.length _ hlen.1 hb hlen.2 hr

/-- The multiplier loop halts with the reversed value of `BinaryProductDefs.loop a b acc` in the
output slot, within `1000 * (b.length + 1) * BinaryProductDefs.span a b acc ^ 2` cost. -/
theorem loop_exec (a b acc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (io : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some .loop, (default, io), state a b acc [] [] [] [] []⟩
      ⟨none, default, state [] [] [] [] [] [] [] (BinaryProductDefs.loop a b acc).reverse⟩
      (1000 * (b.length + 1) * BinaryProductDefs.span a b acc ^ 2) := by
  induction b generalizing a acc io with
  | nil =>
    have e0 := one _ _ _ (loop_stop a acc (default, io)) (loop_stop_clock a acc (default, io))
    have e1 := clear_call a acc (default, none)
    have e2 := finish_call acc (default, none)
    have e3 : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
        ⟨some .done, (default, none), state [] [] [] [] [] [] [] acc.reverse⟩
        ⟨none, default, state [] [] [] [] [] [] [] acc.reverse⟩ 1 := ⟨1, rfl, le_rfl⟩
    apply (((e0.trans e1).trans e2).trans e3).mono
    simp only [List.length_nil, zero_add, mul_one]
    have h := BinaryProductDefs.current_lengths a [] acc
    exact base_budget a.length acc.length _ (BinaryProductDefs.span_pos a [] acc) h.1 h.2
  | cons bit bs ih =>
    obtain ⟨last, e0⟩ := step_exec a bs acc bit io
    have e1 := ih (false :: a) (if bit then PaidBinaryAddition.output acc a else acc) last
    apply (e0.trans e1).mono
    have hs := BinaryProductDefs.step_span a bs acc bit
    have hh := Nat.mul_le_mul_left (1000 * (bs.length + 1)) (Nat.pow_le_pow_left hs 2)
    simp only [List.length_cons]
    exact (Nat.add_le_add_left hh _).trans_eq (by ring)

/-- The initialized stack machine computes a word of value `binaryValue a * binaryValue b` with
cost at most `4000 * (a.length + b.length + 1) ^ 3`. Its length is at most `a.length + 2 *
b.length`, and all other stacks are empty at termination. -/
theorem source_multiplier (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    ∃ (result : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (ticks : ℕ),
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program ticks
        ⟨some .loop, default, state a b [] [] [] [] [] []⟩ =
        some ⟨none, default, state [] [] [] [] [] [] [] result.reverse⟩ ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks
        ⟨some .loop, default, state a b [] [] [] [] [] []⟩ ≤
        4000 * (a.length + b.length + 1) ^ 3 ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue result = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b ∧
      result.length ≤ a.length + 2 * b.length := by
  obtain ⟨ticks, hr, hc⟩ := loop_exec a b [] none
  refine ⟨BinaryProductDefs.loop a b [], ticks, hr, hc.trans ?_, ?_, ?_⟩
  · rw [BinaryProductDefs.initial_span]
    have hs : a.length + 2 * b.length + 1 ≤ 2 * (a.length + b.length + 1) := by omega
    have hb : b.length + 1 ≤ a.length + b.length + 1 := by omega
    calc
      1000 * (b.length + 1) * (a.length + 2 * b.length + 1) ^ 2 ≤
          1000 * (a.length + b.length + 1) * (2 * (a.length + b.length + 1)) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hb) (Nat.pow_le_pow_left hs 2)
      _ = 4000 * (a.length + b.length + 1) ^ 3 := by ring
  · simpa only [List.length_nil, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue,
      List.foldr_nil, zero_add] using! BinaryProductDefs.value a b []
  · have h := BinaryProductDefs.length a b []
    rw [BinaryProductDefs.initial_span] at h
    omega

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidBinaryMultiplication
