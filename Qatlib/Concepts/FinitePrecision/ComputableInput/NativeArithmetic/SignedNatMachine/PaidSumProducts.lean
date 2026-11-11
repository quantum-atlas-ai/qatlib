/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.CanonicalNatMultiplication
import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.CanonicalNatAddition
import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.RedundantRational

/-!
# Canonical sums of two products

`program` reads four canonical natural-number fields, computes two products using
`CanonicalNatMultiplication.program`, joins their encodings, and calls the canonical
natural-number adder. The result is the canonical field for `a * b + c * d`.

The call lemmas describe each phase with explicit stack-clock bounds. Intermediate length
estimates combine these costs into the cubic bound of `source_exec`, which transfers to the
tape-machine result `raw_sum_products`.

## Main statements

* `intermediate_length` and `output_length`: bounds on intermediate and final encodings.
* `source_exec`: the stack computation of a sum of products.
* `raw_sum_products`: a tape machine with cubic resource bounds.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidSumProducts

/-- The Boolean-stack slots for four arguments, two encoded operand pairs, multiplication and
addition workspace, and final output. -/
inductive Slot where
  | raw | reader | markers | payload | first | second | third | fourth
  | temp | pairA | pairB | product | result | joint | output
  deriving DecidableEq, Fintype
/-- Control labels for reading and clearing arguments, computing two products, joining their
encodings, adding, and halting. -/
inductive Label where
  | start (l : Fin 1) | read (i : Fin 4) (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Label)
  | drain (i : Fin 4) (l : Fin 1) | multiply (which : Bool) (l : CanonicalNatMultiplication.Label)
  | resetMul (which : Bool) | join1 (l : Fin 1) | join2 (l : Fin 1) | add (l : CanonicalNatAddition.Label) | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.start 0⟩
/-- The canonical natural-number multiplier local state, also reused for the reader and adder
calls. -/
abbrev Local := CanonicalNatMultiplication.Local
/-- Configurations of the sum-of-products stack machine. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

/-- Assign the four argument indices to the first, second, third, and fourth operand slots. -/
def argBank : Fin 4 → Slot | 0 => .first | 1 => .second | 2 => .third | _ => .fourth
/-- Arrange four bit words as an indexed family over `Fin 4`, in the given order. -/
def operands (a b c d : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Fin 4 →
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits | 0 => a | 1 => b | 2 => c | _ => d

/-- Construct the raw input, reader, four operands, intermediate words, and output, leaving the
marker, payload, and temporary slots empty. -/
def state (raw reader : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (pairA pairB product result joint output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .raw => raw | .reader => reader | .markers => [] | .payload => []
  | .first => args 0 | .second => args 1 | .third => args 2 | .fourth => args 3 | .temp => []
  | .pairA => pairA | .pairB => pairB | .product => product | .result => result | .joint => joint | .output => output

/-- Extract the natural-number reader component of the local state. -/
def getRead (v : Local) := v.1
/-- Replace the natural-number reader component of the local state while preserving its other
component. -/
def putRead (v : Local)
    (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local) : Local := (x, v.2)
/-- Use the entire local state as the canonical natural-number multiplier state. -/
def getMul (v : Local) := v
/-- Replace the entire local state with the canonical natural-number multiplier state. -/
def putMul (_v : Local) (x : CanonicalNatMultiplication.Local) : Local := x
/-- Use the entire local state as the canonical natural-number adder state. -/
def getAdd (v : Local) : CanonicalNatAddition.Local := v
/-- Replace the entire local state with the canonical natural-number adder state. -/
def putAdd (_v : Local) (x : CanonicalNatAddition.Local) : Local := x
/-- Extract the optional Boolean symbol used by the input and output subroutines. -/
def getIO (v : Local) := v.2.2
/-- Replace the optional Boolean symbol used by the input and output subroutines while
preserving the remaining local data. -/
def putIO (v : Local) (x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    (v.1, v.2.1, x)

/-- Embed the initial transfer from the raw-input slot to the reader slot. -/
def startCode : Fin 2 → Slot | 0 => .raw | _ => .reader
/-- Embed the reader with the decoded value at `argBank i` and the copied encoding in the first
or second operand-pair slot. -/
def readCode (i : Fin 4) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Slot → Slot
  | .reader => .reader | .markers => .markers | .payload => .payload
  | .value => argBank i | .temporary => .temp | .output => if i.val < 2 then .pairA else .pairB

/-- Embed the canonical multiplier for the selected operand pair, directing its output to the
corresponding saved-product slot. -/
def mulCode (which : Bool) : CanonicalNatMultiplication.Slot → Slot
  | .raw => if which then .pairB else .pairA | .reader => .reader | .markers => .markers
  | .payload => .payload | .first => .first | .second => .second | .result => .result
  | .temp => .temp | .output => if which then .product else .joint

/-- Embed the transfer from the second product slot to the result workspace. -/
def join1Code : Fin 2 → Slot | 0 => .product | _ => .result
/-- Embed the transfer from the result workspace to the joint encoded-input slot. -/
def join2Code : Fin 2 → Slot | 0 => .result | _ => .joint
/-- Embed the canonical adder with the joint word as input and the final output slot as
destination. -/
def addCode : CanonicalNatAddition.Slot → Slot
  | .raw => .joint | .reader => .reader | .markers => .markers | .payload => .payload
  | .first => .first | .second => .second | .result => .result | .temp => .temp | .output => .output

/-- Continue with the next argument field, or begin clearing argument slots after the fourth
field. -/
def afterRead (i : Fin 4) : Label :=
    if h : i.val + 1 < 4 then .read ⟨i.val + 1, h⟩ (.read .unary) else .drain 0 0
/-- Continue clearing argument slots, or reset the first multiplier call after the fourth slot. -/
def afterDrain (i : Fin 4) : Label :=
    if h : i.val + 1 < 4 then .drain ⟨i.val + 1, h⟩ 0 else .resetMul false
/-- Reset the second multiplier after the first product, or begin joining encodings after the
second product. -/
def afterMul (which : Bool) : Label := if which then .join1 0 else .resetMul true

/-- The stack program computing a canonical sum of two products by parsing, two multiplier
calls, encoded-input transfers, and an adder call. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .start l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt startCode Label.start (.read 0 (.read .unary)) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .read i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (readCode i) (Label.read i) (afterRead i) getRead putRead (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program l)
  | .drain i l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (fun _ : Fin 1 => argBank i) (Label.drain i) (afterDrain i) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .multiply which l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (mulCode which) (Label.multiply which) (afterMul which) getMul putMul (CanonicalNatMultiplication.program l)
  | .resetMul which => .load (fun v => putMul v default) (.goto (fun _ => .multiply which (.start 0)))
  | .join1 l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt join1Code Label.join1 (.join2 0) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .join2 l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt join2Code Label.join2 (.add (.start 0)) getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .add l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt addCode Label.add .done getAdd putAdd (CanonicalNatAddition.program l)
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
  fin_cases i <;> cases x <;> cases y <;> simp_all [readCode, argBank]

/-- `mulCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem mulCode_inj (which : Bool) : Function.Injective (mulCode which) := by
  intro x y h
  cases which <;> cases x <;> cases y <;> simp_all [mulCode]

/-- `join1Code` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem join1Code_inj  : Function.Injective (join1Code) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [join1Code]

/-- `join2Code` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem join2Code_inj  : Function.Injective (join2Code) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [join2Code]

/-- `addCode` is injective, so distinct subroutine stacks occupy distinct machine slots. -/
private theorem addCode_inj  : Function.Injective (addCode) := by
  intro x y h
  cases x <;> cases y <;> simp_all [addCode]

/-- Concatenate the canonical natural-number encodings of `a`, `b`, `c`, and `d`. -/
def input (a b c d : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d))
/-- The final local state of the natural-number reader after reading the canonical encoding of
`n`. -/
def readLast (n : ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.Local :=
    ((true, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat.lastField n.bits none),
    none)

/-- Transfer the reversed raw input to the reader stack and enter the first parsing phase within
`20 * (1 + bits.length) ^ 2` cost. -/
theorem start_call (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.start 0), v, state bits.reverse [] (operands [] [] [] []) [] [] [] [] [] []⟩
      ⟨some (.read 0 (.read .unary)), putIO v none, state [] bits (operands [] [] [] []) [] [] [] [] [] []⟩
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

/-- Read a canonical field into an empty argument slot and copy its reversed encoding into the
selected operand-pair slot, preserving the other pair. The execution satisfies the displayed
quadratic bound. -/
theorem read_call (i : Fin 4) (n : ℕ) (tail : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (harg : args i = []) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.read i (.read .unary)), v, state [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail) args a b [] [] [] []⟩
      ⟨some (afterRead i), putRead v (readLast n),
        state [] tail (Function.update args i n.bits)
          (if i.val < 2 then (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ a else a)
          (if i.val < 2 then b else (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse ++ b) [] [] [] []⟩
      (500 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail).length + a.length + b.length) ^ 2) := by
  obtain ⟨ticks, hr, hc⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.complete n tail
      (if i.val < 2 then a else b) (getRead v)
  have hl : (if i.val < 2 then a else b).length ≤ a.length + b.length := by split_ifs <;> omega
  have hb :=
      Nat.mul_le_mul_left 500
      (Nat.pow_le_pow_left (Nat.add_le_add_left hl (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ tail).length)) 2)
  refine lift (readCode i) (readCode_inj i) (Label.read i) (afterRead i)
    getRead putRead (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.program (fun _ => rfl) v _ _ _ _ _ _ _ ⟨ticks, hr, hc.trans (by simpa only [Nat.add_assoc] using! hb)⟩ ?_ ?_ ?_
  · intro k; fin_cases i <;> cases k <;> simp [readCode, state, argBank,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.store, harg] at *
  · intro k; fin_cases i <;> cases k <;> simp [readCode, state, argBank,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit.store]
  · intro j hj
    fin_cases i <;> cases j <;> first
    | rfl
    | exact (hj .reader rfl).elim
    | exact (hj .markers rfl).elim
    | exact (hj .payload rfl).elim
    | exact (hj .value rfl).elim
    | exact (hj .temporary rfl).elim
    | exact (hj .output rfl).elim

/-- Clear the selected decoded argument while preserving both encoded operand pairs and
continuing at `afterDrain i`, with the stated cost bound. -/
theorem drain_call (i : Fin 4) (args : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.drain i 0), v, state [] [] args a b [] [] [] []⟩
      ⟨some (afterDrain i), putIO v none, state [] [] (Function.update args i []) a b [] [] [] []⟩
      ((args i).length ^ 2 + 3 * (args i).length + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run (args i)
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock (args i)
      (getIO v)
  refine lift (fun _ : Fin 1 => argBank i) (fun _ _ _ => Subsingleton.elim _ _) (Label.drain i) (afterDrain i)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨(args i).length + 1, hr, hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; fin_cases i <;> rfl
  · intro k; fin_cases k; fin_cases i <;> simp [state, argBank]
  · intro j hj
    fin_cases i <;> cases j <;> first | rfl | exact (hj 0 rfl).elim

/-- Construct the workspace for the selected product call, including its raw input, the other
operand pair, its output, and any previously saved product. -/
def multiplyState (which : Bool) (raw other out saved : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  if which then state [] [] (operands [] [] [] []) other raw out [] saved []
  else state [] [] (operands [] [] [] []) raw other [] [] out []

/-- Reset the multiplier local state and enter the selected multiplication phase at execution
cost one. -/
theorem reset_call (which : Bool) (S : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (.resetMul which), v, S⟩
      ⟨some (.multiply which (.start 0)), putMul v default, S⟩ 1 := ⟨1, rfl, le_rfl⟩

/-- With the multiplier initialized, replace an encoded operand pair by the reversed canonical
product field while preserving the other pair and saved product, within the displayed cubic
bound. -/
theorem multiply_call (which : Bool) (a b : ℕ) (other saved : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) (hv : getMul v = default) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.multiply which (.start 0)), v, multiplyState which (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse other [] saved⟩
      ⟨some (afterMul which), putMul v default, multiplyState which [] other (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).reverse saved⟩
      (20000 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 3) := by
  have e := CanonicalNatMultiplication.source_exec a b
  have he : (TM2.init CanonicalNatMultiplication.Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse : CanonicalNatMultiplication.Config) =
      ⟨some (.start 0), default, CanonicalNatMultiplication.state (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse [] [] [] [] [] [] [] []⟩ := by
    have hs : Function.update (fun _ => []) CanonicalNatMultiplication.Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse =
        CanonicalNatMultiplication.state (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse [] [] [] [] [] [] [] [] := by
      funext j
      cases j <;> simp [CanonicalNatMultiplication.state]
    change (⟨some (.start 0), default, Function.update (fun _ => []) CanonicalNatMultiplication.Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse⟩ : CanonicalNatMultiplication.Config) = _
    rw [hs]
  rw [he, ← hv] at e
  rw [← hv]
  refine lift (mulCode which) (mulCode_inj which) (Label.multiply which) (afterMul which)
    getMul putMul (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    CanonicalNatMultiplication.program (fun _ => rfl) v _ _ _ _ _ _ _ e ?_ ?_ ?_
  · intro k; cases which <;> cases k <;> rfl
  · intro k; cases which <;> cases k <;> rfl
  · intro j hj
    cases which <;> cases j <;> first
    | rfl
    | exact (hj .raw rfl).elim
    | exact (hj .reader rfl).elim
    | exact (hj .markers rfl).elim
    | exact (hj .payload rfl).elim
    | exact (hj .first rfl).elim
    | exact (hj .second rfl).elim
    | exact (hj .result rfl).elim
    | exact (hj .temp rfl).elim
    | exact (hj .output rfl).elim

/-- Transfer the reversed second product into the result workspace in forward order while
preserving the first product, with the stated cost bound. -/
theorem join1_call (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.join1 0), v, state [] [] (operands [] [] [] []) [] [] b.reverse [] a.reverse []⟩
      ⟨some (.join2 0), putIO v none, state [] [] (operands [] [] [] []) [] [] [] b a.reverse []⟩
      (b.length * (2 * b.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run b.reverse []
      (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock b.reverse []
      (getIO v)
  simp only [List.length_reverse, List.length_nil, Nat.add_zero, List.reverse_reverse,
      List.append_nil] at hr hc
  refine lift join1Code join1Code_inj Label.join1 (.join2 0)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨b.length + 1, hr, (by nlinarith [hc])⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

/-- Transfer the second word onto the reversed first word to form the reversed concatenation `a
++ b`, then enter the adder within the stated cost bound. -/
theorem join2_call (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.join2 0), v, state [] [] (operands [] [] [] []) [] [] [] b a.reverse []⟩
      ⟨some (.add (.start 0)), putIO v none, state [] [] (operands [] [] [] []) [] [] [] [] (a ++ b).reverse []⟩
      (b.length * (2 * b.length + 2 * a.length + 5) + 3) := by
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run b a.reverse (getIO v)
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock b a.reverse
      (getIO v)
  simp only [List.length_reverse] at hc
  simp only [← List.reverse_append] at hr
  refine lift join2Code join2Code_inj Label.join2 (.add (.start 0))
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) v _ _ _ _ _ _ _ ⟨b.length + 1, hr, (by nlinarith [hc])⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

/-- With the adder initialized, consume two canonical fields and produce the reversed canonical
sum field within `10000 * (1 + (natBits a ++ natBits b).length) ^ 2` cost. -/
theorem add_call (a b : ℕ) (v : Local) (hv : getAdd v = default) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.add (.start 0)), v, state [] [] (operands [] [] [] []) [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse []⟩
      ⟨some .done, putAdd v default, state [] [] (operands [] [] [] []) [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a + b)).reverse⟩
      (10000 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) ^ 2) := by
  have e := CanonicalNatAddition.source_exec a b
  have he : (TM2.init CanonicalNatAddition.Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse : CanonicalNatAddition.Config) =
      ⟨some (.start 0), default, CanonicalNatAddition.state (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse [] [] [] [] [] [] [] []⟩ := by
    have hs : Function.update (fun _ => []) CanonicalNatAddition.Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse =
        CanonicalNatAddition.state (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse [] [] [] [] [] [] [] [] := by
      funext j
      cases j <;> simp [CanonicalNatAddition.state]
    change (⟨some (.start 0), default, Function.update (fun _ => []) CanonicalNatAddition.Slot.raw (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).reverse⟩ : CanonicalNatAddition.Config) = _
    rw [hs]
  rw [he, ← hv] at e
  rw [← hv]
  refine lift addCode addCode_inj Label.add .done
    getAdd putAdd (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    CanonicalNatAddition.program (fun _ => rfl) v _ _ _ _ _ _ _ e ?_ ?_ ?_
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro j hj
    cases j <;> first
    | rfl
    | exact (hj .raw rfl).elim
    | exact (hj .reader rfl).elim
    | exact (hj .markers rfl).elim
    | exact (hj .payload rfl).elim
    | exact (hj .first rfl).elim
    | exact (hj .second rfl).elim
    | exact (hj .result rfl).elim
    | exact (hj .temp rfl).elim
    | exact (hj .output rfl).elim

/-- The length of the four-field input is the sum of the lengths of its canonical natural-number
encodings. -/
theorem input_length (a b c d : ℕ) :
    (input a b c d).length = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d).length := by
  simp only [input, List.length_append]
  omega

/-- The canonical encoding of a product has length at most twice the combined lengths of its
operand encodings. -/
theorem product_field_length (a b : ℕ) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).length ≤ 2 * ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b).length) := by
  have h := CanonicalNatMultiplication.product_bits_length a b
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length]
  omega

/-- The concatenated encodings of the two products have length at most twice the four-field
input length. -/
theorem intermediate_length (a b c d : ℕ) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b) ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (c * d)).length ≤ 2 * (input a b c d).length := by
  have h := product_field_length a b
  have g := product_field_length c d
  rw [List.length_append, input_length]
  omega

/-- The canonical sum-of-products field has length at most twice the input length plus one. -/
theorem output_length (a b c d : ℕ) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + c * d)).length ≤ 2 * (input a b c d).length + 1 := by
  have h := CanonicalNatAddition.sum_bits_length (a * b) (c * d)
  have g := intermediate_length a b c d
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length,
      List.length_append] at *
  omega

/-- If `m ≤ L`, the square of `1 + m` is bounded by the cube of `1 + L`. -/
private theorem sq_cube {m L : ℕ} (h : m ≤ L) : (1 + m) ^ 2 ≤ (1 + L) ^ 3 := by
  exact (Nat.pow_le_pow_left (Nat.add_le_add_left h 1) 2).trans
    (Nat.pow_le_pow_right (by omega : 0 < 1 + L) (by decide : 2 ≤ 3))

/-- A drain cost for a word of length at most `L` is bounded by `10 * (1 + L) ^ 3`. -/
private theorem drain_cube {m L : ℕ} (h : m ≤ L) : m ^ 2 + 3 * m + 3 ≤ 10 * (1 + L) ^ 3 := by
  have hb := sq_cube h
  have hp : 0 < (1 + L) ^ 3 := by positivity
  nlinarith only [hb, hp]

/-- If `a + b ≤ 2 * L`, the two transfer costs used to join the product encodings sum to at most
`100 * (1 + L) ^ 3`. -/
private theorem join_cube {a b L : ℕ} (h : a + b ≤ 2 * L) :
    b * (2 * b + 5) + 3 + (b * (2 * b + 2 * a + 5) + 3) ≤ 100 * (1 + L) ^ 3 := by
  have hb : b ≤ 2 * L := by omega
  have h1 := Nat.mul_le_mul hb (show 2 * b + 5 ≤ 4 * L + 5 by omega)
  have h2 := Nat.mul_le_mul hb (show 2 * b + 2 * a + 5 ≤ 4 * L + 5 by omega)
  have hs := sq_cube (le_refl L)
  nlinarith only [h1, h2, hs]

/-- If `m ≤ 2 * L`, the square of `1 + m` is bounded by `4 * (1 + L) ^ 3`. -/
private theorem double_sq_cube {m L : ℕ} (h : m ≤ 2 * L) : (1 + m) ^ 2 ≤ 4 * (1 + L) ^ 3 := by
  have h1 := Nat.pow_le_pow_left (show 1 + m ≤ 2 * (1 + L) by omega) 2
  have hs := sq_cube (le_refl L)
  nlinarith only [h1, hs]

/-- The initialized stack program halts with only the reversed canonical encoding of `a * b + c
* d`, at cost at most `200000 * (1 + (input a b c d).length) ^ 3`. -/
theorem source_exec (a b c d : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      (TM2.init Slot.raw (input a b c d).reverse)
      ⟨none, default, state [] [] (operands [] [] [] []) [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + c * d)).reverse⟩
      (200000 * (1 + (input a b c d).length) ^ 3) := by
  let bits := input a b c d
  let L := bits.length
  let A :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b
  let B :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d
  let a0 := operands [] [] [] []
  let a1 := Function.update a0 0 a.bits
  let a2 := Function.update a1 1 b.bits
  let a3 := Function.update a2 2 c.bits
  let a4 := Function.update a3 3 d.bits
  let args := operands a.bits b.bits c.bits d.bits
  let v1 := putRead (putIO default none) (readLast a)
  let v2 := putRead v1 (readLast b)
  let v3 := putRead v2 (readLast c)
  let v4 := putRead v3 (readLast d)
  have e0 := start_call bits default
  have e1 :=
      read_call 0 a
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d)) a0 [] [] (putIO default none) (by rfl)
  have e2 :=
      read_call 1 b
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d) a1 (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).reverse [] v1 (by rfl)
  have e3 :=
      read_call 2 c (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d) a2 A.reverse
      [] v2 (by rfl)
  have e4 :=
      read_call 3 d [] a3 A.reverse
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c).reverse v3 (by rfl)
  simp only [List.append_nil] at e1 e2 e3 e4
  simp only [A, List.reverse_append] at e3 e4
  have e01 := e0.trans e1
  have e02 := e01.trans e2
  have e03 := e02.trans e3
  have e04 := e03.trans (by simpa only [List.append_nil] using! e4)
  have ha4 : a4 = args := by funext j; fin_cases j <;> rfl
  have hd : Function.update (Function.update (Function.update (Function.update args 0 []) 1 []) 2 []) 3 [] = a0 := by
    funext j; fin_cases j <;> rfl
  let d1 := Function.update args 0 []
  let d2 := Function.update d1 1 []
  let d3 := Function.update d2 2 []
  have ep0 := drain_call 0 args A.reverse B.reverse v4
  have ep1 := drain_call 1 d1 A.reverse B.reverse v4
  have ep2 := drain_call 2 d2 A.reverse B.reverse v4
  have ep3 := drain_call 3 d3 A.reverse B.reverse v4
  have eclear := ((ep0.trans ep1).trans ep2).trans ep3
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program _ ⟨some (.resetMul false), v4, state [] [] _ A.reverse B.reverse [] [] [] []⟩ _ at eclear
  rw [hd] at eclear
  have eread := e04
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program _ ⟨some (.drain 0 0), v4, state [] [] a4 _ _ [] [] [] []⟩ _ at eread
  rw [ha4] at eread
  have er := eread
  simp only [← List.reverse_append] at er
  have e05 := er.trans eclear
  have ez0 := reset_call false (state [] [] a0 A.reverse B.reverse [] [] [] []) v4
  have em0 := multiply_call false a b B.reverse [] default (by rfl)
  have ez1 :=
      reset_call true
      (multiplyState false [] B.reverse (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).reverse []) default
  have em1 :=
      multiply_call true c d []
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).reverse default (by rfl)
  have ej1 :=
      join1_call (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b))
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (c * d)) default
  have ej2 :=
      join2_call (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b))
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (c * d)) default
  have eadd := add_call (a * b) (c * d) default (by rfl)
  have efin : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some .done, default, state [] [] a0 [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + c * d)).reverse⟩
      ⟨none, default, state [] [] a0 [] [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + c * d)).reverse⟩ 1 := ⟨1, rfl, le_rfl⟩
  have e :=
      (((((((e05.trans ez0).trans em0).trans ez1).trans em1).trans ej1).trans ej2).trans eadd).trans efin
  have hi : (TM2.init Slot.raw bits.reverse : Config) =
      ⟨some (.start 0), default, state bits.reverse [] a0 [] [] [] [] [] []⟩ := by
    have hs : Function.update (fun _ => []) Slot.raw bits.reverse = state bits.reverse [] a0 [] [] [] [] [] [] := by
      funext j
      cases j <;> simp [state, a0, operands]
    change (⟨some (.start 0), default, Function.update (fun _ => []) Slot.raw bits.reverse⟩ : Config) = _
    rw [hs]
  rw [hi]
  apply e.mono
  have hlen := input_length a b c d
  have ha : a.bits.length ≤ L := by
    dsimp only [L,
      bits]; simp only
      [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
  have hb : b.bits.length ≤ L := by
    dsimp only [L,
      bits]; simp only
      [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
  have hc : c.bits.length ≤ L := by
    dsimp only [L,
      bits]; simp only
      [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
  have hd' : d.bits.length ≤ L := by
    dsimp only [L,
      bits]; simp only
      [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length] at hlen; omega
  have h0 := sq_cube (le_refl L)
  have h1 :=
      sq_cube (show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d))).length + 0 + 0 ≤ L by simp only [Nat.add_zero]; exact le_refl _)
  have h2 :=
      sq_cube (show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d)).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a).reverse.length + 0 ≤ L by simp only [List.length_append, List.length_reverse]; dsimp only [L, bits]; omega)
  have h3 :=
      sq_cube (show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d).length + A.reverse.length + 0 ≤ L by simp only [A, List.length_append, List.length_reverse]; dsimp only [L, bits]; omega)
  have h4 :=
      sq_cube (show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d ++ []).length + A.reverse.length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c).reverse.length ≤ L by simp only [A, List.length_append, List.length_reverse, List.length_nil]; dsimp only [L, bits]; omega)
  have hp0 := drain_cube ha
  have hp1 := drain_cube hb
  have hp2 := drain_cube hc
  have hp3 := drain_cube hd'
  have hm0 :=
      Nat.pow_le_pow_left
      (show 1 + A.length ≤ 1 + L by simp only [A, List.length_append]; dsimp only [L, bits]; omega) 3
  have hm1 :=
      Nat.pow_le_pow_left
      (show 1 + B.length ≤ 1 + L by simp only [B, List.length_append]; dsimp only [L, bits]; omega) 3
  have hl := intermediate_length a b c d
  simp only [List.length_append] at hl
  change (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b)).length +
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (c * d)).length ≤ 2 * L at hl
  have hj := join_cube hl
  have hadd :=
      double_sq_cube
      (show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b) ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (c * d)).length ≤ 2 * L by simpa only [List.length_append] using! hl)
  have hpos : 0 < (1 + L) ^ 3 := by positivity
  simp [args, operands, d1, d2, d3]
  simp only [List.length_append, List.length_reverse, Nat.add_zero] at h1 h2 h3 h4 hm0 hm1 hadd
  dsimp only [L, bits, A, B] at h0 h1 h2 h3 h4 hp0 hp1 hp2 hp3 hm0 hm1 hj hadd hpos ⊢
  simp only [List.length_append] at hm0 hm1
  nlinarith only [h0, h1, h2, h3, h4, hp0, hp1, hp2, hp3, hm0, hm1, hj, hadd, hpos]

/-- There is a finite-state tape machine computing the canonical sum of two products from four
canonical input fields, with a uniform positive cubic bound for both resources in `Runs`. -/
theorem raw_sum_products :
    ∃ (q c : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < c ∧ ∀ a b d e : ℕ,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input a b d e) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + d * e))
        (c * (1 + (input a b d e).length) ^ 3)
        (c * (1 + (input a b d e).length) ^ 3) := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler program Slot.raw Slot.output
  refine ⟨q, 300000 * C, M, Nat.mul_pos (by decide) hC, ?_⟩
  intro a b d e
  obtain ⟨steps, hr, hc⟩ := source_exec a b d e
  have he (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : state [] [] (operands [] [] [] []) [] [] [] [] [] bits =
      Function.update (fun _ => []) Slot.output bits := by
    funext j
    cases j <;> simp [state, operands]
  rw [he] at hr
  have hh :=
      hM (input a b d e)
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + d * e)) steps default hr
  have hout : 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + d * e)).length ≤ 2 * (1 + (input a b d e).length) := by
    have h := output_length a b d e
    omega
  have hout2 := Nat.pow_le_pow_left hout 2
  have h23 :=
      Nat.pow_le_pow_right (show 0 < 1 + (input a b d e).length by omega) (by decide : 2 ≤ 3)
  have hb : C * ((1 + (input a b d e).length) ^ 2 +
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init Slot.raw (input a b d e).reverse) +
      (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + d * e)).length) ^ 2) ≤
      300000 * C * (1 + (input a b d e).length) ^ 3 := by
    have hm : (1 + (input a b d e).length) ^ 2 +
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init Slot.raw (input a b d e).reverse) +
        (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (a * b + d * e)).length) ^ 2 ≤
        300000 * (1 + (input a b d e).length) ^ 3 := by
      nlinarith only [hc, hout2, h23]
    exact (Nat.mul_le_mul_left C hm).trans_eq (by ring)
  exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hh hb hb

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidSumProducts
