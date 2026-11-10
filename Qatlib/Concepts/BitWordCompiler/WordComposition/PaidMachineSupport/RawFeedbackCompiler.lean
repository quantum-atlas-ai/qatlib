/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawFeedback
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawFeedback
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM

def pendingRequest {q : ℕ} (bank : ControllerFeedback.Bank q)
    (pending : ControllerFeedback.Variable q) (b : Bool) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  request (ControllerFeedback.packed bank) (ControllerFeedback.address pending).val.bits b

def pendingResponse {q : ℕ} (bank : ControllerFeedback.Bank q)
    (pending : ControllerFeedback.Variable q) (b : Bool) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  response (ControllerFeedback.packed (ControllerFeedback.supply bank pending b))

private theorem ofFn_update {V : ℕ} (bank : Fin V → Option Bool) (i : Fin V) (b : Bool) :
    List.ofFn (Function.update bank i (some b))=(List.ofFn bank).set i (some b) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn,List.getElem_set]
    split_ifs with h
    · subst j; simp
    · have hn : (⟨j,by simpa using! hj⟩ : Fin V)≠i := by
        intro he; exact h (congrArg Fin.val he).symm
      simp [Function.update_of_ne hn]

theorem pending_transaction_execution {q : ℕ} (bank : ControllerFeedback.Bank q)
    (pending : ControllerFeedback.Variable q) (b : Bool) :
    ∃ last : Local, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.Execution program (TM2.init .reader (pendingRequest bank pending b).reverse)
      ⟨none,last,Function.update (fun _ => []) .output (pendingResponse bank pending b).reverse⟩
      (10000*((ControllerFeedback.address pending).val+(ControllerFeedback.address pending).val.bits.length+2)*
        (1+(pendingRequest bank pending b).length)^2) := by
  let slots := List.ofFn bank
  let i := ControllerFeedback.address pending
  have hi : i.val<slots.length := by simpa only [slots,List.length_ofFn] using! i.isLt
  have ht : (slots.take i.val).length=i.val := by
    simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
  have hs : slots.take i.val ++ slots[i.val]::slots.drop (i.val+1)=slots := by
    rw [← List.drop_eq_getElem_cons hi]
    exact List.take_append_drop _ _
  have hu : List.ofFn (ControllerFeedback.supply bank pending b)=
      slots.take i.val ++ some b::slots.drop (i.val+1) := by
    rw [ControllerFeedback.supply,ofFn_update,List.set_eq_take_append_cons_drop,if_pos hi]
  obtain ⟨last,he⟩ := transaction_execution (slots.take i.val) slots[i.val] (slots.drop (i.val+1))
    i.val.bits b (by rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,ht])
  rw [hs,← hu,ht] at he
  exact ⟨last,by simpa only [slots,i,pendingRequest,pendingResponse,ControllerFeedback.packed] using! he⟩

theorem pendingRequest_length_bound {q : ℕ} (bank : ControllerFeedback.Bank q)
    (pending : ControllerFeedback.Variable q) (b : Bool) :
    1+(pendingRequest bank pending b).length≤6*(2*q+6) := by
  have hd :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.bits_length_le
      (ControllerFeedback.address pending).val
  have hi := (ControllerFeedback.address pending).isLt
  have hf :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Scheduler.framed_length_bound
      (ControllerFeedback.address pending).val.bits.reverse
  simp only [List.length_reverse] at hf
  simp only [pendingRequest,request,List.length_reverse,List.length_cons,List.length_append,
    ControllerFeedback.packed_length]
  omega

theorem pendingResponse_length_bound {q : ℕ} (bank : ControllerFeedback.Bank q)
    (pending : ControllerFeedback.Variable q) (b : Bool) :
    1+(pendingResponse bank pending b).length≤6*(2*q+6) := by
  simp only [pendingResponse,response,List.length_cons,ControllerFeedback.packed_length]
  omega

theorem raw_feedback_machine :
    ∃ (r : ℕ) (N : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (r+1))) (C : ℕ), 0<C ∧
      (∀ (q : ℕ) (bank : ControllerFeedback.Bank q) (pending : ControllerFeedback.Variable q) (b : Bool),
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs N (pendingRequest bank pending b) (pendingResponse bank pending b)
          (C*(2*q+6)^3) (C*(2*q+6)^3)) ∧
      (∀ tail : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs N (false::tail).reverse [false]
        (C*(1+(false::tail).length)^2) (C*(1+(false::tail).length)^2)) ∧
      (∀ input : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits, input=[] ∨ input=[true] → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs N input [false]
        (C*(1+input.length)^2) (C*(1+input.length)^2)) := by
  obtain ⟨r,N,C,hC,hcompile⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler_separate program Slot.reader Slot.output
  refine ⟨r,N,1000000*C,Nat.mul_pos (by decide) hC,?_,?_,?_⟩
  · intro q bank pending b
    obtain ⟨last,ticks,hr,hc⟩ := pending_transaction_execution bank pending b
    have hraw :=
        hcompile (pendingRequest bank pending b) (pendingResponse bank pending b) ticks last hr
    let A := 2*q+6
    have hA : 1≤A := by dsimp [A]; omega
    have hsq : A^2≤A^3 := by
      have hm := Nat.mul_le_mul_right (A^2) hA
      nlinarith
    have hi := (ControllerFeedback.address pending).isLt
    have hd :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.bits_length_le
        (ControllerFeedback.address pending).val
    have hfactor : (ControllerFeedback.address pending).val+
        (ControllerFeedback.address pending).val.bits.length+2≤2*A := by dsimp [A]; omega
    have hI := Nat.pow_le_pow_left (pendingRequest_length_bound bank pending b) 2
    have hO := Nat.pow_le_pow_left (pendingResponse_length_bound bank pending b) 2
    have hbudget : 10000*((ControllerFeedback.address pending).val+
        (ControllerFeedback.address pending).val.bits.length+2)*(1+(pendingRequest bank pending b).length)^2≤
        720000*A^3 := by
      have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 10000 hfactor) hI
      dsimp [A] at *
      nlinarith only [hm]
    have htime : (1+(pendingRequest bank pending b).length)^2+
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks (TM2.init .reader (pendingRequest bank pending b).reverse)+
        (1+(pendingResponse bank pending b).length)^2≤1000000*A^3 := by
      change _≤(6*A)^2 at hI hO
      nlinarith only [hI,hO,hc,hbudget,hsq,Nat.zero_le (A^3)]
    have hmax :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock program ticks
        (TM2.init .reader (pendingRequest bank pending b).reverse)
    have hspace : (1+(pendingRequest bank pending b).length)^2+
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunMaxClock program ticks (TM2.init .reader (pendingRequest bank pending b).reverse)+
        (1+(pendingResponse bank pending b).length)^2≤1000000*A^3 := by omega
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hraw
    · simpa only [A,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using! Nat.mul_le_mul_left C htime
    · simpa only [A,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using!
        Nat.mul_le_mul_left C hspace
  · intro tail
    obtain ⟨last,ticks,hr,hc⟩ := inactive_execution tail
    have hr' : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program ticks (TM2.init .reader (false::tail).reverse.reverse)=
        some ⟨none,last,Function.update (fun _ => []) .output ([false] : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits).reverse⟩ := by
      simpa only [List.reverse_reverse,List.reverse_singleton] using! hr
    have hraw := hcompile (false::tail).reverse [false] ticks last hr'
    have hmax :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock program ticks
        (TM2.init .reader (false::tail))
    have htime : (1+(false::tail).length)^2+
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks (TM2.init .reader (false::tail)) + 4≤
        1000000*(1+(false::tail).length)^2 := by
      have hpos : 1≤(1+(false::tail).length)^2 := Nat.one_le_pow _ _ (by omega)
      omega
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hraw
    · simpa only [List.length_reverse,List.length_cons,List.length_nil,List.reverse_reverse,
        Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using! Nat.mul_le_mul_left C htime
    · have hspace := htime.trans' (Nat.add_le_add_right (Nat.add_le_add_left hmax _) _)
      simpa only [List.length_reverse,List.length_cons,List.length_nil,List.reverse_reverse,
        Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using! Nat.mul_le_mul_left C hspace
  · intro input hi
    obtain ⟨last,ticks,hr,hc⟩ := missing_execution input hi
    have hir : input.reverse=input := by rcases hi with rfl | rfl <;> rfl
    have hr' : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program ticks (TM2.init .reader input.reverse)=
        some ⟨none,last,Function.update (fun _ => []) .output ([false] : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits).reverse⟩ := by
      simpa only [hir,List.reverse_singleton] using! hr
    have hraw := hcompile input [false] ticks last hr'
    have hmax :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock program ticks
        (TM2.init .reader input)
    have htime : (1+input.length)^2+Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program ticks (TM2.init .reader input)+4≤
        1000000*(1+input.length)^2 := by
      have hpos : 1≤(1+input.length)^2 := Nat.one_le_pow _ _ (by omega)
      omega
    apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hraw
    · simpa only [hir,List.length_cons,List.length_nil,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
        using! Nat.mul_le_mul_left C htime
    · have hspace := htime.trans' (Nat.add_le_add_right (Nat.add_le_add_left hmax _) _)
      simpa only [hir,List.length_cons,List.length_nil,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
        using! Nat.mul_le_mul_left C hspace

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.RawFeedback
