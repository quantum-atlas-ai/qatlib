/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

/-!
# Clocked calls to raw binary machines

`program` wraps a binary `TM0` machine in a stack-machine call. It reverses the raw input into a
reader stack, prepares the simulated tape, runs the machine, and returns reversed output with
clean workspace.

The phase lemmas culminate in `source_exec`, whose explicit budget is quadratic in input length
and the supplied raw-machine time bound.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `start_call` and `prepare_call`: establish the input-preparation phases.
* `source_exec`: completes the simulated call with blank auxiliary stacks.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawCall

/-- Stack slots for raw input, reader data, temporary storage, simulated tape halves, and
output. -/
inductive Slot where
  | raw | reader | temp | left | right | output
  deriving DecidableEq, Fintype
/-- Control labels for input transfer, tape preparation, simulated execution, and completion. -/
inductive Label (q : ℕ) where
  | start (l : Fin 1) | prepare (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Preparation.Label)
  | call (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Subroutine.Label (Fin (q + 1))) | done
  deriving DecidableEq, Fintype
instance (q : ℕ) : Inhabited (Label q) := ⟨.start 0⟩
/-- The preparation routine's local state, containing simulated head and I/O symbols. -/
abbrev Local := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Preparation.Local
/-- Configurations of the raw-machine call wrapper. -/
abbrev Config (q : ℕ) := TM2.Cfg (fun _ : Slot => Bool) (Label q) Local
/-- The distinguished raw-input stack slot. -/
abbrev rawSlot : Slot := .raw
/-- The distinguished output stack slot. -/
abbrev outputSlot : Slot := .output
/-- Assigns bit strings to the wrapper's six stacks. -/
def state (raw reader temp left right output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .raw => raw | .reader => reader | .temp => temp | .left => left | .right => right | .output => output
/-- Initializes the wrapper with reversed input on the raw-input stack. -/
def initial {q : ℕ} (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Config q :=
    TM2.init rawSlot input.reverse
/-- Extracts the I/O symbol from the local state. -/
def getIO (v : Local) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol := v.2
/-- Replaces the local I/O symbol while preserving the simulated head symbol. -/
def putIO (v : Local) (w : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    (v.1, w)
/-- Extracts the simulated head symbol from the local state. -/
def getHead (v : Local) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol := v.1
/-- Replaces the simulated head symbol while preserving the I/O symbol. -/
def putHead (v : Local) (w : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) :
    Local := (w, v.2)
/-- Maps the initial transfer subroutine to the raw-input and reader stacks. -/
def startCode : Fin 2 → Slot | 0 => .raw | _ => .reader
/-- Maps the preparation subroutine to reader, temporary, left, and right stacks. -/
def prepCode : Fin 4 → Slot | 0 => .reader | 1 => .temp | 2 => .left | _ => .right
/-- Maps the simulated subroutine to the left, right, and output stacks. -/
def subCode : Fin 3 → Slot | 0 => .left | 1 => .right | _ => .output

/-- The stack-machine wrapper that transfers input, prepares a simulated tape, calls `M`, and
halts with cleared local data. -/
def program {q : ℕ} (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))) :
    Label q → TM2.Stmt (fun _ : Slot => Bool) (Label q) Local
  | .start l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt startCode Label.start (.prepare .head)
      getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .prepare l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt prepCode Label.prepare (.call (.simulate 0))
      id (fun _ w => w) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Preparation.program l)
  | .call l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt subCode Label.call .done getHead putHead (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Subroutine.program M l)
  | .done => .load (fun _ => default) .halt

/-- A stack-call frame equals a proposed store when selected stack contents agree and unselected
stacks are preserved. -/
private theorem frame_eq {K : Type} [DecidableEq K] (code : K → Slot)
    (hinj : Function.Injective code) (S T : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (data : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits)
    (hi : ∀ k, T (code k) = data k)
    (ho : ∀ j, (∀ k, code k ≠ j) → T j = S j) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code S data = T := by
  classical
  funext j
  by_cases hj : ∃ k, code k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code S data hinj k,
        hi]
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator.frame_outside code S data j (by simpa using hj)]
    exact (ho j (by simpa using hj)).symm

/-- Lifts a subroutine execution into the raw-machine wrapper with the same budget under
compatible stack and local-state assignments. -/
private theorem lift {q : ℕ} {K Λ σ : Type} [DecidableEq K]
    (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1)))
    (code : K → Slot) (hinj : Function.Injective code) (labels : Λ → Label q) (ret : Label q)
    (get : Local → σ) (put : Local → σ → Local)
    (hg : ∀ v x, get (put v x) = x) (hp : ∀ v x y, put (put v x) y = put v y)
    (hs : ∀ v, put v (get v) = v)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (hcode : ∀ l, program M (labels l) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt code labels ret get put (P l))
    (v : Local) (S T : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (s t : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (l : Λ) (last : σ) (B : ℕ)
    (e : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution P ⟨some l, get v, s⟩ ⟨none, last, t⟩ B)
    (hS : ∀ k, S (code k) = s k) (hT : ∀ k, T (code k) = t k)
    (hout : ∀ j, (∀ k, code k ≠ j) → T j = S j) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution (program M) ⟨some (labels l), v, S⟩
      ⟨some ret, put v last, T⟩ B := by
  obtain ⟨ticks, hr, hc⟩ := e
  obtain ⟨hn, hnc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution code labels ret get put
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code S data hinj k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update code S data hinj k bits)
    hg hp P (program M) hcode v ticks _ _ hr
  have hi :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same code S s hinj hS
  have hf := frame_eq code hinj S T t hT hout
  refine ⟨ticks, ?_, ?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none, hs, hi, hf] using hn
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,
      Option.map_some, Option.getD_some, hs, hi] using hnc.trans_le hc

/-- The initial transfer's stack assignment is injective. -/
private theorem startCode_inj : Function.Injective startCode := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [startCode]

/-- The preparation subroutine's stack assignment is injective. -/
private theorem prepCode_inj : Function.Injective prepCode := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [prepCode]

/-- The simulated subroutine's stack assignment is injective. -/
private theorem subCode_inj : Function.Injective subCode := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [subCode]

/-- The initial transfer moves the reversed raw input into the reader stack in forward order
within a quadratic clock bound. -/
theorem start_call {q : ℕ} (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))) (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution (program M) (initial input)
      ⟨some (.prepare .head), default, state [] input [] [] [] []⟩
      (20 * (1 + input.length) ^ 2) := by
  have hi : initial (q := q) input =
      ⟨some (.start 0), default, state input.reverse [] [] [] [] []⟩ := by
    unfold initial TM2.init
    congr 1
    funext k
    cases k <;> simp [state]
  rw [hi]
  have hr :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run input.reverse [] none
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock input.reverse
      [] none
  simp only [List.length_reverse, List.reverse_reverse, List.length_nil, Nat.add_zero,
    List.append_nil] at hr hc
  refine lift M startCode startCode_inj Label.start (.prepare .head)
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram (fun _ => rfl) default _ _ _ _ _ _ _
    ⟨input.length + 1, hr, hc.le.trans (by nlinarith)⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

/-- The preparation phase sets the head symbol and packs the input tail onto the right stack
within a quadratic clock bound. -/
theorem prepare_call {q : ℕ} (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))) (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution (program M)
      ⟨some (.prepare .head), default, state [] input [] [] [] []⟩
      ⟨some (.call (.simulate 0)), (input.head?, none),
        state [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack (input.tail.map some)) []⟩
      (10 * (1 + input.length) ^ 2) := by
  have hr :=
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Preparation.complete input [] [] default).1
  have hc :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Preparation.clock_bound input []
      [] default
  simp only [List.append_nil] at hr
  simp only [List.length_nil, Nat.add_zero] at hc
  refine lift M prepCode prepCode_inj Label.prepare (.call (.simulate 0))
    id (fun _ w => w) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Preparation.program (fun _ => rfl) default _ _ _ _ _ _ _
    ⟨2 * input.tail.length + 3, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim |
      exact (hj 2 rfl).elim | exact (hj 3 rfl).elim

/-- The first symbol of an input mapped to optional bits is its optional head. -/
private theorem mapped_head (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (input.map some).headI = input.head? := by
  cases input <;> rfl

/-- Taking the tail commutes with mapping input bits to optional symbols. -/
private theorem mapped_tail (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (input.map some).tail = input.tail.map some := by
  cases input <;> rfl

/-- A clean bounded run of `M` yields a wrapper call ending with reversed output and blank
simulation stacks within a quadratic time-derived clock bound. -/
theorem call_call {q : ℕ} (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1)))
    (input output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (time space : ℕ) (h : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M input output time space) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution (program M)
      ⟨some (.call (.simulate 0)), (input.head?, none),
        state [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack (input.tail.map some)) []⟩
      ⟨some .done, default, state [] [] [] [] [] output.reverse⟩
      (10000 * (1 + input.length + time) ^ 2) := by
  obtain ⟨ticks, hr, hc, _⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Subroutine.of_runs M input output time space h
  rw [mapped_head, mapped_tail] at hr hc
  refine lift M subCode subCode_inj Label.call .done getHead putHead
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Subroutine.program M) (fun _ => rfl) (input.head?, none) _ _ _ _ _ _ _
    ⟨ticks, hr, hc⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim | exact (hj 2 rfl).elim

/-- The raw-call budget, equal to `10050 * (1 + inputLength + time)²`. -/
def budget (inputLength time : ℕ) : ℕ := 10050 * (1 + inputLength + time) ^ 2

/-- A clean bounded run of `M` yields a halting wrapper execution with only reversed output
remaining, within the specified raw-call budget. -/
theorem source_exec {q : ℕ} (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1)))
    (input output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (time space : ℕ) (h : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M input output time space) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution (program M) (initial input)
      ⟨none, default, Function.update (fun _ => []) outputSlot output.reverse⟩
      (budget input.length time) := by
  have e0 := start_call M input
  have e1 := prepare_call M input
  have e2 := call_call M input output time space h
  have e3 : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution (program M)
      ⟨some .done, default, state [] [] [] [] [] output.reverse⟩
      ⟨none, default, state [] [] [] [] [] output.reverse⟩ 1 := ⟨1, rfl, le_rfl⟩
  have ee := ((e0.trans e1).trans e2).trans e3
  have hf (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : state [] [] [] [] [] bits = Function.update (fun _ => []) outputSlot bits := by
    funext k
    cases k <;> simp [state]
  rw [hf] at ee
  apply ee.mono
  have hb := Nat.pow_le_pow_left (show 1 + input.length ≤ 1 + input.length + time by omega) 2
  have h1 : 1 ≤ (1 + input.length + time) ^ 2 := Nat.one_le_pow 2 _ (by omega)
  unfold budget
  omega

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawCall
