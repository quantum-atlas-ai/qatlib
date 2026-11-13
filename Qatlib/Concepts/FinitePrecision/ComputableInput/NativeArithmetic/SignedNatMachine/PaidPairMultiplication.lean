/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.PaidSumProducts

/-!
# Multiplication of redundant signed pairs

`program` transforms four canonical natural-number fields into the two fields `a * c + b * d`
and `a * d + b * c`. These are the positive and negative components of the product of
differences `a - b` and `c - d`.

The machine calls the sum-of-products program twice using the field permutations defined by
`route`. `source_exec` and `raw_product` establish this encoded transformation with cubic
bounds, while `pair_output_length` controls the output size.

## Main statements

* `emit_four`: prepare the routed input for each sum-of-products call.
* `pair_output_length`: a linear bound on the two-field output size.
* `raw_product`: a tape implementation with cubic resource bounds.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidPairMultiplication

/-- The four argument slots, the embedded sum-of-products workspace, and a separate final output
slot. -/
inductive Slot where | arg (i : Fin 4) | work (k : PaidSumProducts.Slot) | output
  deriving DecidableEq, Fintype
/-- Control labels for parsing, routed emission, two sum-of-products computations, output
transfers, and argument cleanup. -/
inductive Label where
  | start (l : Fin 1) | read (i : Fin 4) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Label) | discard (l : Fin 1)
  | emit (negative : Bool) (i : Fin 4) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.Label) | reset (negative : Bool)
  | core (negative : Bool) (l : PaidSumProducts.Label)
  | copy1 (negative : Bool) (l : Fin 1) | copy2 (negative : Bool) (l : Fin 1)
  | drain (i : Fin 4) (l : Fin 1) | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.start 0⟩
/-- The local state of the sum-of-products subroutine, reused by the pair multiplier. -/
abbrev Local := PaidSumProducts.Local
/-- Configurations of the redundant-pair multiplication stack machine. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

/-- Arrange four bit words as an indexed family over `Fin 4`, in the given order. -/
def operands (a b c d : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Fin 4 →
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits | 0 => a | 1 => b | 2 => c | _ => d

/-- Construct the four argument stacks, selected sum-of-products input and output stacks, and
final output, leaving the other workspace empty. -/
def state (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (raw reader encoded out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .arg i => args i | .work .raw => raw | .work .reader => reader
  | .work .output => encoded | .work _ => [] | .output => out

/-- Extract the natural-number reader component of the local state. -/
def getRead (v : Local) := v.1
/-- Replace the natural-number reader component of the local state while preserving its other
component. -/
def putRead (v : Local)
    (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local) : Local := (x, v.2)
/-- Extract the optional Boolean symbol used by the input and output subroutines. -/
def getIO (v : Local) := v.2.2
/-- Replace the optional Boolean symbol used by the input and output subroutines while
preserving the remaining local data. -/
def putIO (v : Local) (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    (v.1, v.2.1, x)

/-- Permute four argument indices to prepare the positive or negative component of the product
of two differences. -/
def route (negative : Bool) : Fin 4 → Fin 4
  | 0 => 0 | 1 => if negative then 3 else 2 | 2 => 1 | _ => if negative then 2 else 3

/-- Embed the initial transfer from the raw-input workspace slot to its reader slot. -/
def startCode : Fin 2 → Slot | 0 => .work .raw | _ => .work .reader
/-- Embed the natural-number reader with its decoded value directed to argument slot `i`. -/
def readCode (i : Fin 4) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Slot → Slot
  | .reader => .work .reader | .markers => .work .markers | .payload => .work .payload
  | .value => .arg i | .temporary => .work .temp | .output => .work .output

/-- Embed the natural-number emitter for the routed argument, using the shared temporary slot
and writing to the raw workspace. -/
def emitCode (negative : Bool) (i : Fin 4) : Fin 3 → Slot
  | 0 => .arg (route negative i) | 1 => .work .temp | _ => .work .raw

/-- Embed the transfer from the core output slot to the raw workspace slot. -/
def copy1Code : Fin 2 → Slot | 0 => .work .output | _ => .work .raw
/-- Embed the transfer from the raw workspace slot to the final output slot. -/
def copy2Code : Fin 2 → Slot | 0 => .work .raw | _ => .output

/-- Continue to the next argument field, or discard the parsing output after reading the fourth
field. -/
def afterRead (i : Fin 4) : Label :=
    if h : i.val + 1 < 4 then .read ⟨i.val + 1, h⟩ (.read .unary) else .discard 0
/-- Emit the next routed argument, or reset the core local state after the fourth argument. -/
def afterEmit (negative : Bool) (i : Fin 4) : Label :=
  if h : i.val + 1 < 4 then .emit negative ⟨i.val + 1, h⟩ .count else .reset negative
/-- After copying the positive component, prepare the negative component; after copying the
negative component, begin argument cleanup. -/
def afterCopy (negative : Bool) : Label := if negative then .drain 0 0 else .emit true 0 .count
/-- Continue clearing argument slots in index order, or reach the final label after the fourth
slot. -/
def afterDrain (i : Fin 4) : Label := if h : i.val + 1 < 4 then .drain ⟨i.val + 1, h⟩ 0 else .done

/-- The stack program that computes the two components of a redundant signed-pair product
through two routed sum-of-products calls. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .start l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt startCode Label.start (.read 0 (.read .unary)) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .read i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (readCode i) (Label.read i) (afterRead i) getRead putRead (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program l)
  | .discard l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (fun _ : Fin 1 => .work .output) Label.discard (.emit false 0 .count) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .emit negative i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (emitCode negative i) (Label.emit negative i) (afterEmit negative i) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program l)
  | .reset negative => .load (fun _ => default) (.goto (fun _ => .core negative (.start 0)))
  | .core negative l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt Slot.work (Label.core negative) (.copy1 negative 0) id (fun _ x => x) (PaidSumProducts.program l)
  | .copy1 negative l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt copy1Code (Label.copy1 negative) (.copy2 negative 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .copy2 negative l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt copy2Code (Label.copy2 negative) (afterCopy negative) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .drain i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (fun _ : Fin 1 => .arg i) (Label.drain i) (afterDrain i) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
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

/-- `startCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem startCode_inj  : Function.Injective (startCode) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [startCode]

/-- `readCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem readCode_inj (i : Fin 4) : Function.Injective (readCode i) := by
  intro x y h
  cases x <;> cases y <;> simp_all [readCode]

/-- `emitCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem emitCode_inj (negative : Bool) (i : Fin 4) : Function.Injective (emitCode negative i) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [emitCode]

/-- `copy1Code` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem copy1Code_inj  : Function.Injective (copy1Code) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [copy1Code]

/-- `copy2Code` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem copy2Code_inj  : Function.Injective (copy2Code) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [copy2Code]

/-- The four-field canonical input encoding used by the sum-of-products machine. -/
def input (a b c d : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    PaidSumProducts.input a b c d
/-- The concatenated canonical encodings of the positive component `a * c + b * d` and negative
component `a * d + b * c`. -/
def output (a b c d : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits
    (a * c + b * d) ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * d + b * c)
/-- The final local state of the natural-number reader after reading the canonical encoding of
`n`. -/
def readLast (n : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local :=
    ((true, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat.lastField n.bits none),
    none)

/-- Transfer the reversed raw input into the reader stack and enter the first parsing phase
within `20 * (1 + bits.length) ^ 2` cost. -/
theorem start_call (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.start 0), v, state (operands [] [] [] []) bits.reverse [] [] []⟩
      ⟨some (.read 0 (.read .unary)), putIO v none, state (operands [] [] [] []) [] bits [] []⟩
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
    cases j with
    | arg i => rfl
    | output => rfl
    | work k => cases k <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

/-- Read a canonical field into an empty argument slot and prepend its reversed encoding to the
core parsing output, preserving the final output and other arguments, with the displayed
quadratic bound. -/
theorem read_call (i : Fin 4) (n : ℕ) (tail encoded : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (harg : args i = []) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.read i (.read .unary)), v, state args [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail) encoded []⟩
      ⟨some (afterRead i), putRead v (readLast n),
        state (Function.update args i n.bits) [] tail ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ encoded) []⟩
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
    | output => rfl
    | work k => cases k <;> first
      | rfl
      | exact (hj .reader rfl).elim
      | exact (hj .markers rfl).elim
      | exact (hj .payload rfl).elim
      | exact (hj .temporary rfl).elim
      | exact (hj .output rfl).elim

/-- Clear the core parsing output while preserving all arguments and the final output, then
begin emission for the positive component. -/
theorem discard_call (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (encoded : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.discard 0), v, state args [] [] encoded []⟩
      ⟨some (.emit false 0 .count), putIO v none, state args [] [] [] []⟩
      (encoded.length ^ 2 + 3 * encoded.length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run encoded (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock encoded
      (getIO v)
  refine lift (fun _ : Fin 1 => .work .output) (fun _ _ _ => Subsingleton.elim _ _) Label.discard (.emit false 0 .count)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨encoded.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro j hj
    cases j with
    | arg i => rfl
    | output => rfl
    | work k => cases k <;> first | rfl | exact (hj 0 rfl).elim

/-- Emit a routed argument into the raw workspace, prepending its reversed canonical encoding
and preserving the final output, with the stated quadratic bound. -/
theorem emit_call (negative : Bool) (i : Fin 4) (n : ℕ) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (raw out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (harg : args (route negative i) = n.bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.emit negative i .count), v, state args raw [] [] out⟩
      ⟨some (afterEmit negative i), putIO v none, state args ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ raw) [] [] out⟩
      (100 * (1 + n.bits.length + raw.length) ^ 2) := by
  have hr :=
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.complete n raw (getIO v)).1
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.clock_bound n raw (getIO v)
  refine lift (emitCode negative i) (emitCode_inj negative i) (Label.emit negative i) (afterEmit negative i)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨4 * n.bits.length + 5, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> simp [emitCode, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing.triple, harg]
  · intro k; fin_cases k <;> simp [emitCode, state,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing.triple, harg]
  · intro j hj
    cases j with
    | arg j => rfl
    | output => rfl
    | work k => cases k <;> first | rfl | exact (hj 1 rfl).elim | exact (hj 2 rfl).elim

/-- Reset the local state and enter the selected core sum-of-products computation at execution
cost one. -/
theorem reset_call (negative : Bool) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (raw out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (.reset negative), v, state args raw [] [] out⟩
      ⟨some (.core negative (.start 0)), default, state args raw [] [] out⟩ 1 := ⟨1, rfl, le_rfl⟩

/-- Run the embedded sum-of-products machine on four canonical fields, preserving the outer
arguments and output, and produce the reversed encoding of `a * b + c * d` within the
displayed cubic bound. -/
theorem core_call (negative : Bool) (a b c d : ℕ) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.core negative (.start 0)), default, state args (PaidSumProducts.input a b c d).reverse [] [] out⟩
      ⟨some (.copy1 negative 0), default, state args [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + c * d)).reverse out⟩
      (200000 * (1 + (PaidSumProducts.input a b c d).length) ^ 3) := by
  have e := PaidSumProducts.source_exec a b c d
  have he : (TM2.init PaidSumProducts.Slot.raw (PaidSumProducts.input a b c d).reverse : PaidSumProducts.Config) =
      ⟨some (.start 0), default, PaidSumProducts.state (PaidSumProducts.input a b c d).reverse [] (PaidSumProducts.operands [] [] [] []) [] [] [] [] [] []⟩ := by
    have hs : Function.update (fun _ => []) PaidSumProducts.Slot.raw (PaidSumProducts.input a b c d).reverse =
        PaidSumProducts.state (PaidSumProducts.input a b c d).reverse [] (PaidSumProducts.operands [] [] [] []) [] [] [] [] [] [] := by
      funext j
      cases j <;> simp [PaidSumProducts.state, PaidSumProducts.operands]
    change (⟨some (.start 0), default, Function.update (fun _ => []) PaidSumProducts.Slot.raw (PaidSumProducts.input a b c d).reverse⟩ : PaidSumProducts.Config) = _
    rw [hs]
  rw [he] at e
  refine lift Slot.work (fun _ _ h => Slot.work.inj h) (Label.core negative) (.copy1 negative 0)
    id (fun _ x => x) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    PaidSumProducts.program (fun _ => rfl) default _ _ _ _ _ _ _ e ?_ ?_ ?_
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro j hj
    cases j with
    | arg i => rfl
    | output => rfl
    | work k => exact (hj k rfl).elim

/-- Transfer the reversed core result to the raw workspace in forward order, preserving the
final output, with the stated cost bound. -/
theorem copy1_call (negative : Bool) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bits out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.copy1 negative 0), v, state args [] [] bits.reverse out⟩
      ⟨some (.copy2 negative 0), putIO v none, state args bits [] [] out⟩
      (bits.length * (2 * bits.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run bits.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock bits.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift copy1Code copy1Code_inj (Label.copy1 negative) (.copy2 negative 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨bits.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j with
    | arg i => rfl
    | output => rfl
    | work k => cases k <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

/-- Transfer the raw workspace word to the final output in reversed order and continue to the
next component or cleanup, with the stated cost bound. -/
theorem copy2_call (negative : Bool) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (bits out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.copy2 negative 0), v, state args bits [] [] out⟩
      ⟨some (afterCopy negative), putIO v none, state args [] [] [] (bits.reverse ++ out)⟩
      (bits.length * (2 * (bits.length + out.length) + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run bits out (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock bits out (getIO v)
  refine lift copy2Code copy2Code_inj (Label.copy2 negative) (afterCopy negative)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨bits.length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j with
    | arg i => rfl
    | output => first | rfl | exact (hj 1 rfl).elim
    | work k => cases k <;> first | rfl | exact (hj 0 rfl).elim

/-- Clear argument slot `i`, preserve the final output, and continue at `afterDrain i` within
the displayed quadratic bound. -/
theorem drain_call (i : Fin 4) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.drain i 0), v, state args [] [] [] out⟩
      ⟨some (afterDrain i), putIO v none, state (Function.update args i []) [] [] [] out⟩
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
    | output => rfl
    | work k => cases k <;> rfl

/-- If `m ≤ L`, the square of `1 + m` is bounded by the cube of `1 + L`. -/
private theorem sq_cube {m L : ℕ} (h : m ≤ L) : (1 + m) ^ 2 ≤ (1 + L) ^ 3 :=
  (Nat.pow_le_pow_left (Nat.add_le_add_left h 1) 2).trans
    (Nat.pow_le_pow_right (by omega : 0 < 1 + L) (by decide : 2 ≤ 3))

/-- If `r + t ≤ L`, a quadratic fee in their combined length is bounded by `c * (1 + L) ^ 3`. -/
private theorem sq_fee (c r t L : ℕ) (h : r + t ≤ L) :
    c * (1 + r + t) ^ 2 ≤ c * (1 + L) ^ 3 := by
  simpa only [Nat.add_assoc] using! Nat.mul_le_mul_left c (sq_cube h)

/-- If `r + t ≤ 2 * L`, a quadratic fee in their combined length is bounded by `4 * c * (1 + L)
^ 3`. -/
private theorem double_fee (c r t L : ℕ) (h : r + t ≤ 2 * L) :
    c * (1 + r + t) ^ 2 ≤ (4 * c) * (1 + L) ^ 3 := by
  have h1 := Nat.pow_le_pow_left (show 1 + r + t ≤ 2 * (1 + L) by omega) 2
  have hs := sq_cube (le_refl L)
  have hh : (1 + r + t) ^ 2 ≤ 4 * (1 + L) ^ 3 := by nlinarith only [h1, hs]
  exact (Nat.mul_le_mul_left c hh).trans_eq (by ring)

/-- A drain cost for a word of length at most `L` is bounded by `10 * (1 + L) ^ 3`. -/
private theorem drain_fee {m L : ℕ} (h : m ≤ L) :
    m ^ 2 + 3 * m + 3 ≤ 10 * (1 + L) ^ 3 := by
  have hs := sq_cube h
  have hp : 0 < (1 + L) ^ 3 := by positivity
  nlinarith only [hs, hp]

/-- Under the combined length bound `m + t ≤ 4 * (1 + L)`, the transfer cost is at most `100 *
(1 + L) ^ 3`. -/
private theorem transfer_fee {m t L : ℕ} (h : m + t ≤ 4 * (1 + L)) :
    m * (2 * (m + t) + 5) + 3 ≤ 100 * (1 + L) ^ 3 := by
  have hm : m ≤ 4 * (1 + L) := by omega
  have ht : 2 * (m + t) + 5 ≤ 13 * (1 + L) := by omega
  have hh := Nat.mul_le_mul hm ht
  have hs := sq_cube (le_refl L)
  have hp : 0 < (1 + L) ^ 3 := by positivity
  nlinarith only [hh, hs, hp]

/-- Concatenate the four canonical natural-number fields in the order chosen by `route
negative`. -/
def stream (negative : Bool) (ns : Fin 4 → ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 0)) ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 1)) ++
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 2)) ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 3))))

/-- Emit all four routed argument fields into the raw workspace and enter the core reset phase
within `1600 * (1 + L) ^ 3` cost, under the stated digit and stream length bounds. -/
theorem emit_four (negative : Bool) (ns : Fin 4 → ℕ) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (hargs : ∀ i, args i = (ns i).bits) (L : ℕ)
    (hn : ∀ i, (ns i).bits.length ≤ L) (hl : (stream negative ns).length ≤ L) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.emit negative 0 .count), v, state args [] [] [] out⟩
      ⟨some (.reset negative), putIO v none, state args (stream negative ns).reverse [] [] out⟩
      (1600 * (1 + L) ^ 3) := by
  let u0 := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 0))
  let u1 := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 1))
  let u2 := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (ns (route negative 2))
  have hp1 : (u0.reverse).length ≤ L := by
    simp only [stream, List.length_append] at hl; simp only [u0, List.length_reverse]; omega
  have hp2 : (u0 ++ u1).reverse.length ≤ L := by
    simp only [stream, List.length_append] at hl; simp only [u0, u1, List.length_reverse,
      List.length_append]; omega
  have hp3 : (u0 ++ (u1 ++ u2)).reverse.length ≤ L := by
    simp only [stream, List.length_append] at hl; simp only [u0, u1, u2, List.length_reverse,
      List.length_append]; omega
  have e0 := (emit_call negative 0 (ns (route negative 0)) args [] out v (hargs _)).mono
    (double_fee 100 _ _ L (by simp only [List.length_nil, Nat.add_zero]; have h := hn (route negative 0); omega))
  have e1 := (emit_call negative 1 (ns (route negative 1)) args u0.reverse out (putIO v none) (hargs _)).mono
    (double_fee 100 _ _ L (by have h := hn (route negative 1); omega))
  have e2 := (emit_call negative 2 (ns (route negative 2)) args (u0 ++ u1).reverse out (putIO v none) (hargs _)).mono
    (double_fee 100 _ _ L (by have h := hn (route negative 2); omega))
  have e3 := (emit_call negative 3 (ns (route negative 3)) args (u0 ++ (u1 ++ u2)).reverse out (putIO v none) (hargs _)).mono
    (double_fee 100 _ _ L (by have h := hn (route negative 3); omega))
  simp only [List.append_nil] at e0
  simp only [List.reverse_append, List.append_assoc] at e2 e3
  have e := ((e0.trans e1).trans e2).trans e3
  have he :=
      e.mono (show ((400 * (1 + L) ^ 3 + 400 * (1 + L) ^ 3) + 400 * (1 + L) ^ 3) + 400 * (1 + L) ^ 3 ≤ 1600 * (1 + L) ^ 3 by omega)
  simpa only [u0, u1, u2, stream, List.reverse_append, List.append_assoc] using! he

/-- Arrange four natural numbers as an indexed family over `Fin 4`, in the given order. -/
def naturals (a b c d : ℕ) : Fin 4 → ℕ | 0 => a | 1 => b | 2 => c | _ => d

/-- The two-field pair-product output has length at most four times the four-field input length
plus two. -/
theorem pair_output_length (a b c d : ℕ) : (output a b c d).length ≤ 4 * (input a b c d).length + 2 := by
  have hp := PaidSumProducts.output_length a c b d
  have hn := PaidSumProducts.output_length a d b c
  simp only [output, input, PaidSumProducts.input_length, List.length_append] at *
  omega

/-- The initialized stack program halts with only the reversed two-field pair product remaining,
at cost at most `1000000 * (1 + (input a b c d).length) ^ 3`. -/
theorem source_exec (a b c d : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init (.work .raw) (input a b c d).reverse)
      ⟨none, default, state (operands [] [] [] []) [] [] [] (output a b c d).reverse⟩
      (1000000 * (1 + (input a b c d).length) ^ 3) := by
  let bits := input a b c d
  let L := bits.length
  let ns := naturals a b c d
  let args := operands a.bits b.bits c.bits d.bits
  let a0 := operands [] [] [] []
  let a1 := Function.update a0 0 a.bits
  let a2 := Function.update a1 1 b.bits
  let a3 := Function.update a2 2 c.bits
  let a4 := Function.update a3 3 d.bits
  let v1 := putRead (putIO default none) (readLast a)
  let v2 := putRead v1 (readLast b)
  let v3 := putRead v2 (readLast c)
  let v4 := putRead v3 (readLast d)
  have hlen := PaidSumProducts.input_length a b c d
  change L = _ at hlen
  have hns : ∀ i, (ns i).bits.length ≤ L := by
    intro i
    fin_cases i
    · change a.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
    · change b.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
    · change c.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
    · change d.bits.length ≤ L; simp only
        [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
  have hs0 : (stream false ns).length = L := by simp [stream, route, ns, naturals]; omega
  have hs1 : (stream true ns).length = L := by simp [stream, route, ns, naturals]; omega
  have hpL : (PaidSumProducts.input a c b d).length = L := hs0
  have hnL : (PaidSumProducts.input a d b c).length = L := hs1
  have e0 := (start_call bits default).mono (Nat.mul_le_mul_left 20 (sq_cube (le_refl L)))
  have e1 := (read_call 0 a (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d)) [] a0 (putIO default none) (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_nil]; omega))
  have e2 := (read_call 1 b (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).reverse a1 v1 (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_reverse]; omega))
  have e3 := (read_call 2 c (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse a2 v2 (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_reverse]; omega))
  have e4 := (read_call 3 d [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c)).reverse a3 v3 (by rfl)).mono
    (sq_fee 500 _ _ L (by simp only [List.length_append, List.length_reverse, List.length_nil]; omega))
  simp only [List.append_nil] at e1 e4
  simp only [List.reverse_append, List.append_assoc] at e3 e4
  have er := ((e0.trans e1).trans e2).trans e3
  have er4 := er.trans e4
  have ha4 : a4 = args := by funext i; fin_cases i <;> rfl
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program _ ⟨some (.discard 0), v4, state a4 [] [] _ []⟩ _ at er4
  rw [ha4] at er4
  simp only [← List.reverse_append] at er4
  simp only [List.append_assoc] at er4
  have ed :=
      (discard_call args bits.reverse v4).mono
      (drain_fee (show bits.reverse.length ≤ L by simp only [List.length_reverse]; exact le_refl _))
  have ee0 := emit_four false ns args [] v4 (by intro i; fin_cases i <;> rfl) L hns (le_of_eq hs0)
  have ez0 := reset_call false args (stream false ns).reverse [] v4
  have ec0 := core_call false a c b d args []
  rw [hpL] at ec0
  let P := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * c + b * d)
  let N := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * d + b * c)
  have hout := pair_output_length a b c d
  change (P ++ N).length ≤ 4 * L + 2 at hout
  have hp : P.length ≤ 4 * (1 + L) := by simp only [List.length_append] at hout; omega
  have hn : N.length + P.reverse.length ≤ 4 * (1 + L) := by
    simp only [List.length_append] at hout; simp only [List.length_reverse]; omega
  have ej0 := (copy1_call false args P [] default).mono
    (by simpa only [Nat.add_zero] using! transfer_fee (show P.length + 0 ≤ 4 * (1 + L) by omega))
  have ej1 :=
      (copy2_call false args P [] default).mono
      (transfer_fee (show P.length + [].length ≤ 4 * (1 + L) by simpa only [List.length_nil] using! hp))
  simp only [List.append_nil] at ej1
  have ee1 :=
      emit_four true ns args P.reverse default (by intro i; fin_cases i <;> rfl) L hns
      (le_of_eq hs1)
  have ez1 := reset_call true args (stream true ns).reverse P.reverse default
  have ec1 := core_call true a d b c args P.reverse
  rw [hnL] at ec1
  have ej2 := (copy1_call true args N P.reverse default).mono
    (by simpa only [Nat.add_zero] using! transfer_fee (show N.length + 0 ≤ 4 * (1 + L) by omega))
  have ej3 := (copy2_call true args N P.reverse default).mono (transfer_fee hn)
  let d1 := Function.update args 0 []
  let d2 := Function.update d1 1 []
  let d3 := Function.update d2 2 []
  have ep0 := (drain_call 0 args (N.reverse ++ P.reverse) default).mono (drain_fee (hns 0))
  have ep1 := (drain_call 1 d1 (N.reverse ++ P.reverse) default).mono (drain_fee (hns 1))
  have ep2 := (drain_call 2 d2 (N.reverse ++ P.reverse) default).mono (drain_fee (hns 2))
  have ep3 := (drain_call 3 d3 (N.reverse ++ P.reverse) default).mono (drain_fee (hns 3))
  have hd : Function.update d3 3 [] = a0 := by funext i; fin_cases i <;> rfl
  have eclear := ((ep0.trans ep1).trans ep2).trans ep3
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program _ ⟨some .done, default, state (Function.update d3 3 []) [] [] [] (N.reverse ++ P.reverse)⟩ _ at eclear
  rw [hd] at eclear
  have efin : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some .done, default, state a0 [] [] [] (N.reverse ++ P.reverse)⟩
      ⟨none, default, state a0 [] [] [] (N.reverse ++ P.reverse)⟩ 1 := ⟨1, rfl, le_rfl⟩
  have e :=
      ((((((((((((er4.trans ed).trans ee0).trans ez0).trans ec0).trans ej0).trans ej1).trans ee1).trans ez1).trans ec1).trans ej2).trans ej3).trans eclear).trans efin
  have hi : (TM2.init (.work .raw) bits.reverse : Config) =
      ⟨some (.start 0), default, state a0 bits.reverse [] [] []⟩ := by
    have hS : Function.update (fun _ => []) (.work .raw) bits.reverse = state a0 bits.reverse [] [] [] := by
      funext j
      cases j with
      | arg i => fin_cases i <;> simp [state, a0, operands]
      | output => simp [state]
      | work k => cases k <;> simp [state]
    change (⟨some (.start 0), default, Function.update (fun _ => []) (.work .raw) bits.reverse⟩ : Config) = _
    rw [hS]
  have he := e.mono (show _ ≤ 1000000 * (1 + L) ^ 3 by
    have hp : 0 < (1 + L) ^ 3 := by positivity
    omega)
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init (.work .raw) bits.reverse)
    ⟨none, default, state a0 [] [] [] (output a b c d).reverse⟩ (1000000 * (1 + L) ^ 3)
  rw [hi]
  simpa only [output, P, N, List.reverse_append] using! he

/-- There is a finite-state tape machine mapping the four-field input to the two-field
redundant-pair product, with a uniform positive cubic bound for both resources in `Runs`. -/
theorem raw_product :
    ∃ (q c : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < c ∧ ∀ a b d e : ℕ,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input a b d e) (output a b d e)
        (c * (1 + (input a b d e).length) ^ 3)
        (c * (1 + (input a b d e).length) ^ 3) := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler program
      (.work .raw) Slot.output
  refine ⟨q, 2000000 * C, M, Nat.mul_pos (by decide) hC, ?_⟩
  intro a b d e
  obtain ⟨steps, hr, hc⟩ := source_exec a b d e
  have he (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : state (operands [] [] [] []) [] [] [] bits =
      Function.update (fun _ => []) Slot.output bits := by
    funext j
    cases j with
    | arg i => fin_cases i <;> simp [state, operands]
    | output => simp [state]
    | work k => cases k <;> simp [state]
  rw [he] at hr
  have hh := hM (input a b d e) (output a b d e) steps default hr
  have hout : 1 + (output a b d e).length ≤ 4 * (1 + (input a b d e).length) := by
    have h := pair_output_length a b d e
    omega
  have hout2 := Nat.pow_le_pow_left hout 2
  have h23 :=
      Nat.pow_le_pow_right (show 0 < 1 + (input a b d e).length by omega) (by decide : 2 ≤ 3)
  have hb : C * ((1 + (input a b d e).length) ^ 2 +
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init (.work .raw) (input a b d e).reverse) +
      (1 + (output a b d e).length) ^ 2) ≤
      2000000 * C * (1 + (input a b d e).length) ^ 3 := by
    have hm : (1 + (input a b d e).length) ^ 2 +
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init (.work .raw) (input a b d e).reverse) +
        (1 + (output a b d e).length) ^ 2 ≤
        2000000 * (1 + (input a b d e).length) ^ 3 := by
      nlinarith only [hc, hout2, h23]
    exact (Nat.mul_le_mul_left C hm).trans_eq (by ring)
  exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hh hb hb

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidPairMultiplication
