/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.PendingFeedback

/-!
# Raw feedback request transactions

`program` reads an activation bit, feedback value, framed index, and encoded bank, then invokes
the feedback writer and emits a flagged response. Its explicit stack assignments isolate
parsing, transfers, and bank updates.

`transaction_execution` proves the successful update path. Inactive inputs and inputs missing
the initial request data are drained and produce a false response.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `transaction_execution`: realizes a valid indexed bank update with an explicit clock bound.
* `inactive_execution` and `missing_execution`: give clean rejection executions for the stated
  input forms.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawFeedback
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open scoped Classical

/-- Stack slots for request parsing, the feedback bank and index, response output, and parser
workspace. -/
inductive Slot where
  | reader | bank | index | output | saved | indexTemp
  | markers | payload | count | temporary | header
  deriving DecidableEq, Fintype
/-- Transfer jobs for loading the bank and emitting its contents. -/
inductive Move where | loadBank | emit deriving DecidableEq, Fintype
/-- Control labels for reading a request, parsing an index, moving data, writing feedback,
emitting flags, and rejecting. -/
inductive Label where
  | request | bit | read (l : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.Label) | move (job : Move) (l : Fin 1)
  | feedback (l : ControllerFeedback.Label) | flag | stop | drain (l : Fin 1) | reject
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.request⟩
/-- Local data combining framed-reader state, feedback-writer state, and an optional I/O symbol. -/
abbrev Local :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.Local × ControllerFeedback.Local × Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol

/-- Extracts the framed-reader component of local data. -/
def getRead (v : Local) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.Local :=
    v.1
/-- Replaces the framed-reader component while preserving feedback and I/O data. -/
def putRead (v : Local)
    (s : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.Local) : Local := (s,v.2)
/-- Extracts the feedback-writer component of local data. -/
def getFeedback (v : Local) : ControllerFeedback.Local := v.2.1
/-- Replaces the feedback-writer component while preserving reader and I/O data. -/
def putFeedback (v : Local) (s : ControllerFeedback.Local) : Local := (v.1,s,v.2.2)
/-- Extracts the optional I/O symbol. -/
def getIO (v : Local) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol := v.2.2
/-- Replaces the optional I/O symbol while preserving reader and feedback data. -/
def putIO (v : Local) (s : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) : Local :=
    (v.1,v.2.1,s)
/-- Records an incoming optional symbol as I/O and as the feedback value, using false for an
absent symbol. -/
def receive (v : Local) (s : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol) :
    Local := (v.1,(s.getD false,v.2.1.2),s)

/-- Replacing the reader component by its current value leaves local data unchanged. -/
@[simp] private theorem putRead_get (v : Local) : putRead v (getRead v)=v := rfl

/-- Replacing the feedback component by its current value leaves local data unchanged. -/
@[simp] private theorem putFeedback_get (v : Local) : putFeedback v (getFeedback v)=v := rfl

/-- Replacing the I/O component by its current value leaves local data unchanged. -/
@[simp] private theorem putIO_get (v : Local) : putIO v (getIO v)=v := rfl

/-- Assigns the framed-reader stacks to parser workspace, using the index stack for its output. -/
def readCode : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.Slot → Slot
  | .reader => .reader | .markers => .markers | .payload => .payload
  | .count => .count | .temporary => .temporary | .header => .header | .output => .index

/-- Assigns the feedback-writer stacks to bank, saved prefix, index, and temporary-index
storage. -/
def feedbackCode : ControllerFeedback.Slot → Slot
  | .bank => .bank | .saved => .saved | .index => .index | .indexTemp => .indexTemp

/-- Selects the reader-to-bank or bank-to-output transfer stacks. -/
def moveCode : Move → Fin 2 → Slot
  | .loadBank,0 => .reader | .loadBank,_ => .bank
  | .emit,0 => .bank | .emit,_ => .output

/-- Chooses the feedback entry label after loading and the stop label after emitting. -/
def moveReturn : Move → Label
  | .loadBank => .feedback (.counter .borrow) | .emit => .stop

/-- Selects the reader stack for the rejection drain routine. -/
def drainCode (_ : Fin 1) : Slot := .reader

/-- The stack-machine transaction program that parses a request, updates its bank, emits a
success flag, or drains a rejected request. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .request => .pop .reader putIO (.branch (fun v => decide (getIO v = some true))
      (.goto (fun _ => .bit)) (.goto (fun _ => .drain 0)))
  | .bit => .pop .reader receive (.branch (fun v => (getIO v).isSome)
      (.goto (fun _ => .read (.read (.read .unary)))) (.goto (fun _ => .drain 0)))
  | .read l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt readCode Label.read (.move .loadBank 0) getRead putRead (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.program l)
  | .move job l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt (moveCode job) (Label.move job) (moveReturn job)
      getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram l)
  | .feedback l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt feedbackCode Label.feedback .flag getFeedback putFeedback (ControllerFeedback.program l)
  | .flag => .push .output (fun _ => true) (.goto (fun _ => .move .emit 0))
  | .stop => .halt
  | .drain l => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.stmt drainCode Label.drain .reject getIO putIO (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram l)
  | .reject => .push .output (fun _ => false) .halt

/-- Initializes reader, bank, index, and output stacks, leaving all other stacks empty. -/
def store (reader bank index output : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | .reader => reader | .bank => bank | .index => index | .output => output | _ => []

/-- Serializes a flagged feedback request using a reversed framed index and reversed bank
payload. -/
def request (bank index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (feedback : Bool) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  (true :: feedback :: (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed index.reverse ++ bank.reverse)).reverse

/-- Prefixes the encoded response bank with a true success bit. -/
def response (bank : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := true :: bank

/-- A stack-call frame equals a target store when selected contents agree and all unselected
stacks are preserved. -/
private theorem frame_eq {K : Type} [DecidableEq K] (code : K → Slot)
    (saved target : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (data : K → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits)
    (hinj : Function.Injective code) (hm : ∀ k,target (code k)=data k)
    (ho : ∀ j,(∀ k,code k≠j) → target j=saved j) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame code saved data=target := by
  funext j
  by_cases he : ∃ k,code k=j
  · obtain ⟨k,rfl⟩ := he
    exact (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at code saved data hinj k).trans (hm k).symm
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator.frame_outside code saved data j (fun k hk => he ⟨k,hk⟩)]
    exact (ho j (fun k hk => he ⟨k,hk⟩)).symm

/-- A single transaction-program transition gives an execution with its statement clock plus
one. -/
private theorem one (l : Label) (v : Local) (S : Slot → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits)
    (last : TM2.Cfg (fun _ : Slot => Bool) Label Local)
    (h : TM2.step program ⟨some l,v,S⟩=some last) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some l,v,S⟩ last (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock (program l) v S+1) := by
  refine ⟨1,by simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_one] using! h,?_⟩
  simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock,h,Nat.add_comm]

/-- Updating the reader stack of `store` replaces only its reader argument. -/
@[simp] private theorem store_update_reader (r b i o x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (store r b i o) Slot.reader x=store x b i o := by funext k; cases k <;> rfl

/-- Updating the output stack of `store` replaces only its output argument. -/
@[simp] private theorem store_update_output (r b i o x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (store r b i o) Slot.output x=store r b i x := by funext k; cases k <;> rfl

/-- The framed-reader stack assignment is injective. -/
private theorem read_inj : Function.Injective readCode := by
  intro a b h; cases a <;> cases b <;> simp_all [readCode]

/-- The feedback-writer stack assignment is injective. -/
private theorem feedback_inj : Function.Injective feedbackCode := by
  intro a b h; cases a <;> cases b <;> simp_all [feedbackCode]

/-- Each transfer job's stack assignment is injective. -/
private theorem move_inj (job : Move) : Function.Injective (moveCode job) := by
  cases job <;> decide

/-- The framed-reader call extracts the reversed framed index into the index stack, preserves
feedback data, and leaves the unread tail. -/
private theorem read_call (index tail bank out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    ∃ w : Local, w.2.1=v.2.1 ∧ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.read (.read (.read .unary))),v,store (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed index.reverse ++ tail) bank [] out⟩
      ⟨some (.move .loadBank 0),w,store tail bank index out⟩
      (5000*(index.length+1)*(1+(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed index.reverse ++ tail).length)^2) := by
  let S :=
      store (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed index.reverse ++ tail) bank
      [] out
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame readCode S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.store (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed index.reverse ++ tail) [] [] [])=S := by
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same _ _ _ read_inj
    intro k; cases k <;> rfl
  have hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame readCode S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.store tail [] [] index)=store tail bank index out := by
    apply frame_eq _ _ _ _ read_inj
    · intro k; cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk .reader rfl) | exact False.elim (hk .output rfl)
  obtain ⟨ticks,last,hr,hc⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.complete index.reverse tail
      [] (getRead v)
  simp only [List.reverse_reverse,List.append_nil,List.length_nil,Nat.add_zero,List.length_reverse] at hr hc
  obtain ⟨hN,hNC⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution readCode Label.read (.move .loadBank 0) getRead putRead
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame readCode S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at _ _ data read_inj k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update _ _ data read_inj k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FramedTake.program program (fun _ => rfl) v ticks _ _ hr
  refine ⟨putRead v last,rfl,ticks,?_,?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      hs,hf,S,putRead_get] using! hN
  · simpa only
      [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,hs,S,putRead_get] using! hNC.trans_le hc

/-- The bank-loading transfer reverses the reader payload into the bank stack and proceeds to
feedback within the stated transfer budget. -/
private theorem load_call (bits index out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.move .loadBank 0),v,store bits.reverse [] index out⟩
      ⟨some (.feedback (.counter .borrow)),putIO v none,store [] bits index out⟩
      (bits.length*(2*bits.length+5)+3) := by
  let S := store bits.reverse [] index out
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame (moveCode .loadBank) S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair bits.reverse [])=S := by
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same _ _ _
        (move_inj .loadBank)
    intro k; fin_cases k <;> rfl
  have hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame (moveCode .loadBank) S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] bits)=store [] bits index out := by
    apply frame_eq _ _ _ _ (move_inj .loadBank)
    · intro k; fin_cases k <;> rfl
    · intro k hk; cases k <;> simp_all [moveCode,store,S]
  obtain ⟨hr,hc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution (moveCode .loadBank) (Label.move .loadBank) (moveReturn .loadBank) getIO putIO
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame (moveCode .loadBank) S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at _ _ data (move_inj .loadBank) k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update _ _ data (move_inj .loadBank) k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram program (fun _ => rfl) v (bits.reverse.length+1) _ _
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run bits.reverse [] (getIO v))
  simp only [List.reverse_reverse,List.append_nil] at hr hc
  refine ⟨bits.reverse.length+1,?_,?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      hs,hf,S,putIO_get,moveReturn] using! hr
  · have hclock := hc.trans (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock bits.reverse [] (getIO v))
    simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,putIO_get,hs,S,
      List.length_reverse,List.length_nil,Nat.add_zero] using! hclock.le

/-- The emission transfer empties the bank into output in reversed order and proceeds to the
stop label. -/
private theorem emit_call (reader bits index out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (.move .emit 0),v,store reader bits index out⟩
      ⟨some .stop,putIO v none,store reader [] index (bits.reverse++out)⟩
      (bits.length*(2*(bits.length+out.length)+5)+3) := by
  let S := store reader bits index out
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame (moveCode .emit) S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair bits out)=S := by
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same _ _ _
        (move_inj .emit)
    intro k; fin_cases k <;> rfl
  have hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame (moveCode .emit) S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] (bits.reverse++out))=
      store reader [] index (bits.reverse++out) := by
    apply frame_eq _ _ _ _ (move_inj .emit)
    · intro k; fin_cases k <;> rfl
    · intro k hk; cases k <;> simp_all [moveCode,store,S]
  obtain ⟨hr,hc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution (moveCode .emit) (Label.move .emit) (moveReturn .emit) getIO putIO
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame (moveCode .emit) S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at _ _ data (move_inj .emit) k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update _ _ data (move_inj .emit) k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transferProgram program (fun _ => rfl) v (bits.length+1) _ _
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_run bits out (getIO v))
  refine ⟨bits.length+1,?_,?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      hs,hf,S,putIO_get,moveReturn] using! hr
  · have hclock := hc.trans (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.transfer_clock bits out (getIO v))
    simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,putIO_get,hs,S] using! hclock.le

/-- The feedback call updates the indexed bank slot, clears the index workspace, and proceeds to
the success flag within the stated budget. -/
private theorem feedback_call (front : List (Option Bool)) (old : Option Bool)
    (tail : List (Option Bool)) (index out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local)
    (hi : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue index=front.length) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      ⟨some (.feedback (.counter .borrow)),v,store [] (ControllerFeedback.bankBits (front++old::tail)) index out⟩
      ⟨some .flag,putFeedback v (ControllerFeedback.done (getFeedback v).1),
        store [] (ControllerFeedback.bankBits (front++some (getFeedback v).1::tail)) [] out⟩
      (100*(front.length+1)*(1+(ControllerFeedback.bankBits (front++old::tail)).length+index.length)^2) := by
  let S := store [] (ControllerFeedback.bankBits (front++old::tail)) index out
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame feedbackCode S (ControllerFeedback.store (ControllerFeedback.bankBits (front++old::tail)) [] index [])=S := by
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same _ _ _ feedback_inj
    intro k; cases k <;> rfl
  have hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame feedbackCode S
      (ControllerFeedback.store (ControllerFeedback.bankBits (front++some (getFeedback v).1::tail)) [] [] [])=
      store [] (ControllerFeedback.bankBits (front++some (getFeedback v).1::tail)) [] out := by
    apply frame_eq _ _ _ _ feedback_inj
    · intro k; cases k <;> rfl
    · intro k hk; cases k <;> first | rfl | exact False.elim (hk .bank rfl) | exact False.elim (hk .index rfl)
  obtain ⟨ticks,hr,hc⟩ :=
      FeedbackWrite.feedback_machine_execution front old tail [] index (getFeedback v) hi
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at hr hc
  obtain ⟨hN,hNC⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution feedbackCode Label.feedback .flag getFeedback putFeedback
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame feedbackCode S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at _ _ data feedback_inj k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update _ _ data feedback_inj k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) ControllerFeedback.program program (fun _ => rfl) v ticks _ _ hr
  refine ⟨ticks,?_,?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      hs,hf,S,putFeedback_get] using! hN
  · simpa only
      [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,hs,S,putFeedback_get] using! hNC.trans_le hc

/-- The initial request configuration is the request label with default local data and only the
reader stack populated. -/
@[simp] theorem initial_store (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    (TM2.init Slot.reader bits : TM2.Cfg (fun _ : Slot => Bool) Label Local)=
      ⟨some .request,default,store bits [] [] []⟩ := by
  unfold TM2.init
  congr 1
  funext k
  cases k <;> rfl

/-- A store containing only output equals an update of the all-empty store at the output slot. -/
@[simp] theorem terminal_store (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    store [] [] [] bits=Function.update (fun _ : Slot => []) .output bits := by
  funext k
  cases k <;> rfl

/-- A request with an index matching the bank-prefix length halts with a flagged updated-bank
response and clean workspace within the stated clock bound. -/
theorem transaction_execution (front : List (Option Bool)) (old : Option Bool)
    (tail : List (Option Bool)) (index : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (b : Bool)
    (hi : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue index=front.length) :
    ∃ last : Local, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program
      (TM2.init .reader (request (ControllerFeedback.bankBits (front++old::tail)) index b).reverse)
      ⟨none,last,Function.update (fun _ => []) .output
        (response (ControllerFeedback.bankBits (front++some b::tail))).reverse⟩
      (10000*(front.length+index.length+2)*
        (1+(request (ControllerFeedback.bankBits (front++old::tail)) index b).length)^2) := by
  let bank := ControllerFeedback.bankBits (front++old::tail)
  let updated := ControllerFeedback.bankBits (front++some b::tail)
  let rest := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed index.reverse ++ bank.reverse
  let B := 1+(request bank index b).length
  let v0 : Local := default
  let v1 := putIO v0 (some true)
  let v2 := receive v1 (some b)
  have h1 : TM2.step program ⟨some .request,v0,store (true::b::rest) [] [] []⟩=
      some ⟨some .bit,v1,store (b::rest) [] [] []⟩ := by
    simp [program,TM2.step,TM2.stepAux,store,getIO,putIO,v1]
  have h2 : TM2.step program ⟨some .bit,v1,store (b::rest) [] [] []⟩=
      some ⟨some (.read (.read (.read .unary))),v2,store rest [] [] []⟩ := by
    simp [program,TM2.step,TM2.stepAux,store,getIO,receive,v2]
  have e1 := one _ _ _ _ h1
  have e2 := one _ _ _ _ h2
  obtain ⟨v3,hv3,er⟩ := read_call index bank.reverse [] [] v2
  let v4 := putIO v3 none
  have el := load_call bank index [] v3
  have hbit : (getFeedback v4).1=b := by
    change v3.2.1.1=b
    rw [hv3]
    rfl
  have ef := feedback_call front old tail index [] v4 hi
  rw [hbit] at ef
  let v5 := putFeedback v4 (ControllerFeedback.done b)
  have hflag : TM2.step program ⟨some .flag,v5,store [] updated [] []⟩=
      some ⟨some (.move .emit 0),v5,store [] updated [] [true]⟩ := by
    simp [program,TM2.step,TM2.stepAux,store]
  have eflag := one _ _ _ _ hflag
  have ee := emit_call [] updated [] [true] v5
  have hstop : TM2.step program
      ⟨some .stop,putIO v5 none,store [] [] [] (updated.reverse++[true])⟩=
      some ⟨none,putIO v5 none,store [] [] [] (updated.reverse++[true])⟩ := rfl
  have es := one _ _ _ _ hstop
  have hB : 1≤B := by dsimp [B]; omega
  have hB2 : B≤B^2 := Nat.le_pow (by decide)
  have hrest : rest.length+3=B := by
    simp only [B,request,List.length_reverse,List.length_cons,rest]
    omega
  have hbank : bank.length≤B := by
    dsimp [rest] at hrest
    simp only [List.length_append,List.length_reverse] at hrest
    omega
  have hd : index.length≤B := by
    dsimp [rest,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed] at hrest
    simp only [List.length_append,List.length_reverse] at hrest
    omega
  have hbd : 1+bank.length+index.length≤B := by
    dsimp [rest,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed] at hrest
    simp only [List.length_append,List.length_reverse] at hrest
    omega
  have hup : updated.length=bank.length := by
    simp only [updated,bank,ControllerFeedback.bankBits_length,List.length_append,List.length_cons]
  have e1B := e1.mono (show _≤5*B^2 by
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,getIO,putIO]
    nlinarith)
  have e2B := e2.mono (show _≤5*B^2 by
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,getIO,receive]
    nlinarith)
  have erB := er.mono (show _≤5000*(index.length+1)*B^2 by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change 1+rest.length≤B
    omega)
  have elB := el.mono (show _≤10*B^2 by
    have hh := Nat.pow_le_pow_left hbank 2
    nlinarith)
  have efB := ef.mono (show _≤100*(front.length+1)*B^2 by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left hbd 2)
  have eflagB := eflag.mono (show _≤4*B^2 by
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store]
    nlinarith)
  have eeB := ee.mono (show _≤15*B^2 by
    have hh := Nat.pow_le_pow_left hbank 2
    simp only [List.length_cons,List.length_nil,hup]
    nlinarith)
  have esB := es.mono (show _≤B^2 by
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock]
    nlinarith)
  have e := ((((((e1B.trans e2B).trans erB).trans elB).trans efB).trans eflagB).trans eeB).trans esB
  have e' := e.mono (show _≤10000*(front.length+index.length+2)*B^2 by
    nlinarith only [Nat.zero_le (front.length*B^2),Nat.zero_le (index.length*B^2),Nat.zero_le (B^2)])
  refine ⟨putIO v5 none,?_⟩
  simpa only [initial_store,request,response,List.reverse_reverse,List.reverse_cons,List.reverse_append,
    List.reverse_singleton,List.cons_append,List.nil_append,List.singleton_append,
    terminal_store,bank,updated,rest,B,v0,v1,v2,v4,v5] using! e'

/-- The rejection drain empties the reader stack and reaches the reject label within its
quadratic drain budget. -/
private theorem drain_call (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (.drain 0),v,store bits [] [] []⟩
      ⟨some .reject,putIO v none,store [] [] [] []⟩
      (bits.length^2+3*bits.length+3) := by
  let S := store bits [] [] []
  have hinj : Function.Injective drainCode := fun _ _ _ => Subsingleton.elim _ _
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame drainCode S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack bits)=S := by
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_same _ _ _ hinj
    intro k; rfl
  have hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame drainCode S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.singleStack [])=store [] [] [] [] := by
    apply frame_eq _ _ _ _ hinj
    · intro k; rfl
    · intro k hk; cases k <;> first | rfl | exact False.elim (hk 0 rfl)
  obtain ⟨hr,hc⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution drainCode Label.drain .reject getIO putIO
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame drainCode S)
    (fun data k => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_at _ _ data hinj k)
    (fun data k bits => Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.frame_update _ _ data hinj k bits)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drainProgram program (fun _ => rfl) v (bits.length+1) _ _
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_run bits (getIO v))
  refine ⟨bits.length+1,?_,?_⟩
  · simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      hs,hf,S,putIO_get] using! hr
  · have hh := hc.trans (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Normalization.drain_clock bits (getIO v))
    simpa only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg,Option.map_some,Option.getD_some,hs,S,putIO_get] using! hh.le

/-- Draining and rejecting leaves only a false output bit and halts within the stated quadratic
budget. -/
private theorem reject_execution (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program ⟨some (.drain 0),v,store bits [] [] []⟩
      ⟨none,putIO v none,store [] [] [] [false]⟩ (bits.length^2+3*bits.length+7) := by
  have hs : TM2.step program ⟨some .reject,putIO v none,store [] [] [] []⟩=
      some ⟨none,putIO v none,store [] [] [] [false]⟩ := by
    simp [program,TM2.step,TM2.stepAux]
  apply ((drain_call bits v).trans (one _ _ _ _ hs)).mono
  simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock]

/-- An input whose first reader-stack bit is false is drained and rejected with a singleton
false output within a quadratic clock bound. -/
theorem inactive_execution (tail : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    ∃ last : Local, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init .reader (false::tail))
      ⟨none,last,Function.update (fun _ => []) .output [false]⟩
      (20*(1+(false::tail).length)^2) := by
  let v1 := putIO (default : Local) (some false)
  have hs : TM2.step program ⟨some .request,default,store (false::tail) [] [] []⟩=
      some ⟨some (.drain 0),v1,store tail [] [] []⟩ := by
    simp [program,TM2.step,TM2.stepAux,store,getIO,putIO,v1]
  have he := (one _ _ _ _ hs).trans (reject_execution tail v1)
  have he' := he.mono (show _≤20*(1+(false::tail).length)^2 by
    simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,getIO,putIO]
    nlinarith)
  exact ⟨putIO v1 none,by simpa only [initial_store,terminal_store] using! he'⟩

/-- An empty input or singleton true input is rejected with clean workspace and a singleton
false output within a quadratic clock bound. -/
theorem missing_execution (input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (h : input=[] ∨ input=[true]) :
    ∃ last : Local, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init .reader input)
      ⟨none,last,Function.update (fun _ => []) .output [false]⟩ (20*(1+input.length)^2) := by
  rcases h with rfl | rfl
  · let v1 := putIO (default : Local) none
    have hs : TM2.step program ⟨some .request,default,store [] [] [] []⟩=
        some ⟨some (.drain 0),v1,store [] [] [] []⟩ := by
      simp [program,TM2.step,TM2.stepAux,getIO,putIO,v1]
    have he := (one _ _ _ _ hs).trans (reject_execution [] v1)
    have he' := he.mono (show _≤20*(1+([] : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits).length)^2 by
      simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,getIO,putIO])
    exact ⟨putIO v1 none,by simpa only [initial_store,terminal_store] using! he'⟩
  · let v1 := putIO (default : Local) (some true)
    let v2 := receive v1 none
    have h1 : TM2.step program ⟨some .request,default,store [true] [] [] []⟩=
        some ⟨some .bit,v1,store [] [] [] []⟩ := by
      simp [program,TM2.step,TM2.stepAux,store,getIO,putIO,v1]
    have h2 : TM2.step program ⟨some .bit,v1,store [] [] [] []⟩=
        some ⟨some (.drain 0),v2,store [] [] [] []⟩ := by
      simp [program,TM2.step,TM2.stepAux,getIO,receive,v2]
    have he := ((one _ _ _ _ h1).trans (one _ _ _ _ h2)).trans (reject_execution [] v2)
    have he' := he.mono (show _≤20*(1+([true] : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits).length)^2 by
      simp [program,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock,store,getIO,putIO,receive])
    exact ⟨putIO v2 none,by simpa only [initial_store,terminal_store] using! he'⟩

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawFeedback
