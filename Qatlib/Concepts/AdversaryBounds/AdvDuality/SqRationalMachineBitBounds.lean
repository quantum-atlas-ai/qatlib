/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineSteps
import Mathlib.Algebra.Order.BigOperators.Group.List
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM

set_option autoImplicit false
set_option maxHeartbeats 2500000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

theorem payload_le_frame (w : Bits) : w.length ≤ (framed w).length := by
  simp only [framed,List.length_append]
  omega

theorem frame_length_le (w : Bits) : (framed w).length ≤ 3*(w.length+1) := by
  have h := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Scheduler.framed_length_bound w
  omega

theorem stream_length_le (ws : List Bits) (B : ℕ) (h : ∀ w∈ws,w.length ≤ B) :
    (TableGet.stream ws).length ≤ 3*ws.length*(B+1) := by
  rw [TableGet.stream,List.length_flatMap]
  calc
    _ ≤ (ws.map (fun _ => 3*(B+1))).sum := List.sum_le_sum (by
      intro w hw
      exact (frame_length_le w).trans (Nat.mul_le_mul_left 3 (Nat.succ_le_succ (h w hw))))
    _ = 3*ws.length*(B+1) := by
      simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
      ring

theorem resultBudget_le (bits values : Bits) (H : ℕ)
    (hb : bits.length ≤ H) (hv : values.length ≤ H) :
    resultBudget bits values ≤ 100000*(H+1)^4 := by
  unfold resultBudget
  calc
    _ ≤ 1+10000*(1+H+H)^3+1+(H^2+3*H+3) := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem copyDrainBudget_le (bits values : Bits) (H : ℕ)
    (hb : bits.length ≤ H) (hv : values.length ≤ H) :
    copyDrainBudget bits values ≤ 100000*(H+1)^4 := by
  unfold copyDrainBudget
  calc
    _ ≤ 10000*(1+H+H)^3+1+(H^2+3*H+3) := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem literalBudget_le (bits tail : Bits) (stack : List Bits) (H : ℕ)
    (hc : (framed bits++tail).length ≤ H) (hv : (valueStack stack).length ≤ H) :
    literalBudget bits tail stack ≤ 10000000*(H+1)^4 := by
  have hb : bits.length ≤ H := by
    have := payload_le_frame bits; simp only [List.length_append] at hc; omega
  have hr := resultBudget_le bits (valueStack stack) H hb hv
  unfold literalBudget
  calc
    _ ≤ 6*H+18+1+5000*(H+1)*(1+H)^2+100000*(H+1)^4 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem parameterBudget_le (i : ℕ) (tail : Bits) (ps stack : List Bits) (H : ℕ)
    (hc : (framed i.bits++tail).length ≤ H) (hp : (TableGet.stream ps).length ≤ H)
    (hv : (valueStack stack).length ≤ H) (hw : (ps.getD i []).length ≤ H) :
    parameterBudget i tail ps stack ≤ 10000000*(H+1)^4 := by
  have hi : i.bits.length ≤ H := by
    have := payload_le_frame i.bits; simp only [List.length_append] at hc; omega
  have hr := copyDrainBudget_le (ps.getD i []) (valueStack stack) H hw hv
  unfold parameterBudget
  calc
    _ ≤ 6*H+18+1+5000*(H+1)*(1+H)^2+1+(H*(2*H+5)+3)+1+
        30000*(1+H)*(1+H+H)^2+100000*(H+1)^4 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem storeBudget_le (bits tail : Bits) (ps rest : List Bits) (H : ℕ)
    (ht : tail.length ≤ H) (hp : (TableGet.stream ps).length ≤ H)
    (hv : (framed bits++valueStack rest).length ≤ H) :
    storeBudget bits tail ps rest ≤ 10000000*(H+1)^4 := by
  have hf : (framed bits).length ≤ H := by simp only [List.length_append] at hv; omega
  have hb := (payload_le_frame bits).trans hf
  have hr := copyDrainBudget_le bits [] H hb (by simp)
  unfold storeBudget
  calc
    _ ≤ 6*H+18+1+5000*(H+1)*(1+H)^2+1+100000*(H+1)^4+1+
        (H*(2*(H+H)+5)+3) := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem operandBudget_le (a b tail : Bits) (rest : List Bits) (H : ℕ)
    (ht : tail.length ≤ H) (hv : (framed b++framed a++valueStack rest).length ≤ H) :
    operandBudget a b tail rest ≤ 100000*(H+1)^4 := by
  have hfa := payload_le_frame a
  have hfb := payload_le_frame b
  have ha : a.length ≤ H := by simp only [List.length_append] at hv; omega
  have hb : b.length ≤ H := by simp only [List.length_append] at hv; omega
  have hr : (framed a++valueStack rest).length ≤ H := by
    simp only [List.length_append] at hv ⊢; omega
  unfold operandBudget
  calc
    _ ≤ 6*H+18+1+5000*(H+1)*(1+H)^2+1+5000*(H+1)*(1+H)^2 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem addBudget_le (a b tail : Bits) (rest : List Bits) (H : ℕ)
    (ht : tail.length ≤ H) (hv : (framed b++framed a++valueStack rest).length ≤ H)
    (ho : (bitAdd a b).length ≤ H) :
    addBudget a b tail rest ≤ 10000000*(H+1)^4 := by
  have hfa := payload_le_frame a
  have hfb := payload_le_frame b
  have ha : a.length ≤ H := by simp only [List.length_append] at hv; omega
  have hb : b.length ≤ H := by simp only [List.length_append] at hv; omega
  have hr : (valueStack rest).length ≤ H := by simp only [List.length_append] at hv; omega
  have hop := operandBudget_le a b tail rest H ht hv
  have hc := copyDrainBudget_le (bitAdd a b) (valueStack rest) H ho hr
  have hm : max a.length b.length ≤ H := max_le ha hb
  unfold addBudget addClockBound carryAddPositions
  calc
    _ ≤ 100000*(H+1)^4+1+(H*(2*H+5)+3)+1+(H*(2*H+5)+3)+1+
        ((H+1)*(4*(H+H+H)+14))+100000*(H+1)^4 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem mulBudget_le (a b tail : Bits) (rest : List Bits) (H : ℕ)
    (ht : tail.length ≤ H) (hv : (framed b++framed a++valueStack rest).length ≤ H)
    (ho : (mulAcc a b b.length).length ≤ H) :
    mulBudget a b tail rest ≤ 10000000*(H+1)^4 := by
  have hfa := payload_le_frame a
  have hfb := payload_le_frame b
  have ha : a.length ≤ H := by simp only [List.length_append] at hv; omega
  have hb : b.length ≤ H := by simp only [List.length_append] at hv; omega
  have hr : (valueStack rest).length ≤ H := by simp only [List.length_append] at hv; omega
  have hop := operandBudget_le a b tail rest H ht hv
  have hc := resultBudget_le (mulAcc a b b.length) (valueStack rest) H ho hr
  unfold mulBudget
  calc
    _ ≤ 100000*(H+1)^4+1+1+31720*(1+H+H)^4+1+(H^2+3*H+3)+1+
        (H*(2*H+5)+3)+100000*(H+1)^4 := by gcongr
    _ ≤ _ := by ring_nf; omega

def FrameBound (H : ℕ) (s : WordState) : Prop :=
  (TableGet.stream s.parameters).length ≤ H ∧ (valueStack s.values).length ≤ H

theorem instructionBudget_le (op : Instruction) (tail : Bits) (s s' : WordState) (H : ℕ)
    (he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s=some s') (hc : (op.code++tail).length ≤ H)
    (hs : FrameBound H s) (hs' : FrameBound H s') :
    instructionBudget op tail s ≤ 10000000*(H+1)^4 := by
  rcases s with ⟨ps,vs⟩
  rcases hs with ⟨hp,hv⟩
  cases op with
  | literal w =>
    apply literalBudget_le
    · simp only [Instruction.code,List.length_append,List.length_cons,List.length_nil] at hc ⊢
      omega
    · exact hv
  | parameter i =>
    have hnext : s'=⟨ps,(ps.getD i [])::vs⟩ := by
      simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] using!
        he.symm
    subst s'
    apply parameterBudget_le
    · simp only [Instruction.code,List.length_append,List.length_cons,List.length_nil] at hc ⊢; omega
    · exact hp
    · exact hv
    · change (ps.getD i []).length ≤ H
      have h := hs'.2; have hf := payload_le_frame (ps.getD i [])
      simp only [valueStack,List.flatMap_cons,List.length_append] at h
      omega
  | add =>
    cases vs with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
    | cons b vs =>
      cases vs with
      | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
      | cons a rest =>
        have hnext : s'=⟨ps,bitAdd a b::rest⟩ := by
          simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] using!
            he.symm
        subst s'
        apply addBudget_le
        · simp only [Instruction.code,List.length_append,List.length_cons,List.length_nil] at hc; omega
        · simpa [valueStack,List.append_assoc] using! hv
        · have h := hs'.2; have hf := payload_le_frame (bitAdd a b)
          simp only [valueStack,List.flatMap_cons,List.length_append] at h
          omega
  | multiply =>
    cases vs with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
    | cons b vs =>
      cases vs with
      | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
      | cons a rest =>
        have hnext : s'=⟨ps,mulAcc a b b.length::rest⟩ := by
          simpa [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] using!
            he.symm
        subst s'
        apply mulBudget_le
        · simp only [Instruction.code,List.length_append,List.length_cons,List.length_nil] at hc; omega
        · simpa [valueStack,List.append_assoc] using! hv
        · have h := hs'.2; have hf := payload_le_frame (mulAcc a b b.length)
          simp only [valueStack,List.flatMap_cons,List.length_append] at h
          omega
  | store =>
    cases vs with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
    | cons w rest =>
      apply storeBudget_le
      · simp only [Instruction.code,List.length_append,List.length_cons,List.length_nil] at hc; omega
      · exact hp
      · simpa [valueStack] using! hv

def BoundaryBound (H : ℕ) : List Instruction → WordState → Prop
  | [],s => FrameBound H s
  | op::p,s => FrameBound H s ∧ match Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
      | none => True
      | some next => BoundaryBound H p next

def StatePayloadBound (B : ℕ) (s : WordState) : Prop :=
  (∀ w∈s.parameters,w.length ≤ B) ∧ (∀ w∈s.values,w.length ≤ B)

def PayloadBound (B : ℕ) : List Instruction → WordState → Prop
  | [],s => StatePayloadBound B s
  | op::p,s => StatePayloadBound B s ∧ match Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
      | none => True
      | some next => PayloadBound B p next

def wordCount (s : WordState) : ℕ := s.parameters.length+s.values.length

theorem execute_wordCount (op : Instruction) (s s' : WordState)
    (he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s=some s') : wordCount s' ≤ wordCount s+1 := by
  rcases s with ⟨ps,vs⟩
  cases op with
  | literal w => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at he; subst s'; simp only [wordCount,List.length_cons]; omega
  | parameter i => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at he; subst s'; simp only [wordCount,List.length_cons]; omega
  | add =>
    cases vs with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
    | cons b vs =>
      cases vs with
      | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
      | cons a rest =>
        simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at he; subst s'
        simp only [wordCount,List.length_cons]; omega
  | multiply =>
    cases vs with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
    | cons b vs =>
      cases vs with
      | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
      | cons a rest =>
        simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at he; subst s'
        simp only [wordCount,List.length_cons]; omega
  | store =>
    cases vs with
    | nil => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute] at he
    | cons a rest =>
      simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute,Option.some.injEq] at he; subst s'
      simp only [wordCount,List.length_append,List.length_cons,List.length_nil]; omega

theorem state_frame_bound (s : WordState) (B M H : ℕ)
    (hb : StatePayloadBound B s) (hm : wordCount s ≤ M) (hh : 3*M*(B+1) ≤ H) :
    FrameBound H s := by
  have hp : s.parameters.length ≤ M := by unfold wordCount at hm; omega
  have hv : s.values.length ≤ M := by unfold wordCount at hm; omega
  constructor
  · exact (stream_length_le s.parameters B hb.1).trans
      ((Nat.mul_le_mul_right (B+1) (Nat.mul_le_mul_left 3 hp)).trans hh)
  · change (TableGet.stream s.values).length ≤ H
    exact (stream_length_le s.values B hb.2).trans
      ((Nat.mul_le_mul_right (B+1) (Nat.mul_le_mul_left 3 hv)).trans hh)

theorem payload_boundary (p : List Instruction) (s : WordState) (B M H : ℕ)
    (hb : PayloadBound B p s) (hm : wordCount s+p.length ≤ M) (hh : 3*M*(B+1) ≤ H) :
    BoundaryBound H p s := by
  induction p generalizing s with
  | nil => exact state_frame_bound s B M H hb (by simpa using! hm) hh
  | cons op p ih =>
    refine ⟨state_frame_bound s B M H hb.1 (by simp only [List.length_cons] at hm; omega) hh,?_⟩
    cases he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
    | none => trivial
    | some next =>
      have hn : PayloadBound B p next := by simpa only [PayloadBound,he] using! hb.2
      have hc := execute_wordCount op s next he
      simpa only [he] using! ih next hn (by simp only [List.length_cons] at hm; omega)

theorem boundary_head (p : List Instruction) (s : WordState) (H : ℕ)
    (h : BoundaryBound H p s) : FrameBound H s := by
  cases p with
  | nil => exact h
  | cons op p => exact h.1

theorem program_polynomial (p : List Instruction) (tail : Bits) (s s' : WordState) (H : ℕ)
    (he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p s=some s') (hc : (programCode p++tail).length ≤ H)
    (hb : BoundaryBound H p s) :
    FrameBound H s' ∧ programBudget p tail s ≤ p.length*(10000000*(H+1)^4) ∧
      programPeak p tail s ≤ 10000000*(H+1)^4 := by
  induction p generalizing s with
  | nil =>
    simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,Option.some.injEq] at he; subst s'
    exact ⟨hb,by simp [programBudget],by simp [programPeak]⟩
  | cons op p ih =>
    cases hop : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
    | none => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,hop] at he
    | some next =>
      have hn : BoundaryBound H p next := by simpa only [BoundaryBound,hop] using! hb.2
      have hr :
          Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p next=some s' := by
            simpa only [Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run,hop,Option.bind_some] using! he
      have hc' : (programCode p++tail).length ≤ H := by
        simp only [programCode,List.flatMap_cons,List.length_append] at hc ⊢
        omega
      obtain ⟨hf,ht,hp⟩ := ih next hr hc' hn
      have hstep := instructionBudget_le op (programCode p++tail) s next H hop
        (by simpa only [programCode,List.flatMap_cons,List.append_assoc] using! hc)
        hb.1 (boundary_head p next H hn)
      refine ⟨hf,?_,?_⟩
      · simp only [programBudget,hop,List.length_cons]
        calc
          _ ≤ 10000000*(H+1)^4+p.length*(10000000*(H+1)^4) := Nat.add_le_add hstep ht
          _ = _ := by ring
      · simpa only [programPeak,hop] using! max_le hstep hp

theorem finishBudget_le (ps values : List Bits) (H : ℕ)
    (hp : (TableGet.stream ps).length ≤ H) (hv : (valueStack values).length ≤ H) :
    finishBudget ps values ≤ 100*(H+1)^4 := by
  unfold finishBudget
  calc
    _ ≤ 3+1+(H^2+3*H+3)+1+(H*(2*H+5)+3)+1 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem bootBudget_le (ps : List Bits) (code : Bits) (H : ℕ)
    (hi : (inputCode ps code).length ≤ H) : bootBudget ps code ≤ 10000*(H+1)^4 := by
  have ht : (TableGet.stream ps).length ≤ H := by
    have h := payload_le_frame (TableGet.stream ps)
    simp only [inputCode,List.length_reverse,List.length_append] at hi
    omega
  have hi' : (framed (TableGet.stream ps)++code).length ≤ H := by
    simpa only [inputCode,List.length_reverse] using! hi
  unfold bootBudget
  calc
    _ ≤ 1+5000*(H+1)*(1+H)^2 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem parameters_length_le_stream (ps : List Bits) : ps.length ≤ (TableGet.stream ps).length := by
  induction ps with
  | nil => simp [TableGet.stream]
  | cons w ps ih =>
    have hf : 1 ≤ (framed w).length := by
      simp only [framed,List.length_append,natBits_length]
      omega
    simpa only [TableGet.stream,List.flatMap_cons,List.length_append,List.length_cons] using!
      (show ps.length+1 ≤ (framed w).length+(TableGet.stream ps).length by omega)

theorem program_length_le_code (p : List Instruction) : p.length ≤ (programCode p).length := by
  induction p with
  | nil => simp [programCode]
  | cons op p ih =>
    have ho : 1 ≤ op.code.length := by cases op <;> simp [Instruction.code]
    simp only [programCode,List.flatMap_cons,List.length_append,List.length_cons]
    change p.length+1 ≤ op.code.length+(programCode p).length
    omega

theorem counts_le_input (p : List Instruction) (ps : List Bits) :
    ps.length+p.length ≤ (inputCode ps (programCode p)).length := by
  have hp := parameters_length_le_stream ps
  have hc := program_length_le_code p
  have hf := payload_le_frame (TableGet.stream ps)
  simp only [inputCode,List.length_reverse,List.length_append]
  omega

def pathEnvelope (p : List Instruction) (ps : List Bits) (B : ℕ) : ℕ :=
  (inputCode ps (programCode p)).length+3*(ps.length+p.length)*(B+1)

theorem pathEnvelope_bound (p : List Instruction) (ps : List Bits) (B : ℕ) :
    pathEnvelope p ps B+1 ≤ 5*(1+(inputCode ps (programCode p)).length)*(B+1) := by
  have hc := counts_le_input p ps
  let I := (inputCode ps (programCode p)).length
  have hi : I ≤ (1+I)*(B+1) := by nlinarith
  have ho : 1 ≤ (1+I)*(B+1) := by nlinarith
  have hm : 3*(ps.length+p.length)*(B+1) ≤ 3*(1+I)*(B+1) :=
    Nat.mul_le_mul_right (B+1) (Nat.mul_le_mul_left 3 (by dsimp only [I]; omega))
  unfold pathEnvelope
  change I+3*(ps.length+p.length)*(B+1)+1 ≤ 5*(1+I)*(B+1)
  calc
    _ ≤ (1+I)*(B+1)+3*(1+I)*(B+1)+(1+I)*(B+1) := Nat.add_le_add (Nat.add_le_add hi hm) ho
    _ = _ := by ring

def wordWidth : List Bits → ℕ
  | [] => 0
  | w::ws => max w.length (wordWidth ws)

theorem wordWidth_bound (ws : List Bits) : ∀ w∈ws,w.length ≤ wordWidth ws := by
  induction ws with
  | nil => simp
  | cons a ws ih =>
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · subst w; exact Nat.le_max_left _ _
    · exact (ih w h).trans (Nat.le_max_right _ _)

def stateWidth (s : WordState) : ℕ := max (wordWidth s.parameters) (wordWidth s.values)

theorem StatePayloadBound.mono (s : WordState) (B C : ℕ)
    (hb : StatePayloadBound B s) (hbc : B ≤ C) : StatePayloadBound C s :=
  ⟨fun w hw => (hb.1 w hw).trans hbc,fun w hw => (hb.2 w hw).trans hbc⟩

theorem stateWidth_bound (s : WordState) : StatePayloadBound (stateWidth s) s :=
  ⟨fun w hw => (wordWidth_bound s.parameters w hw).trans (Nat.le_max_left _ _),
   fun w hw => (wordWidth_bound s.values w hw).trans (Nat.le_max_right _ _)⟩

theorem PayloadBound.mono (p : List Instruction) (s : WordState) (B C : ℕ)
    (hb : PayloadBound B p s) (hbc : B ≤ C) : PayloadBound C p s := by
  induction p generalizing s with
  | nil => exact StatePayloadBound.mono s B C hb hbc
  | cons op p ih =>
    refine ⟨StatePayloadBound.mono s B C hb.1 hbc,?_⟩
    cases he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
    | none => trivial
    | some next => exact ih next (by simpa only [he] using! hb.2)

def runWidth : List Instruction → WordState → ℕ
  | [],s => stateWidth s
  | op::p,s => match Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
      | none => stateWidth s
      | some next => max (stateWidth s) (runWidth p next)

theorem runWidth_bound (p : List Instruction) (s : WordState) : PayloadBound (runWidth p s) p s := by
  induction p generalizing s with
  | nil => exact stateWidth_bound s
  | cons op p ih =>
    cases he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.execute op s with
    | none =>
      constructor
      · simpa only [runWidth,he] using! stateWidth_bound s
      · simp only [he]
    | some next =>
      constructor
      · simpa only [runWidth,he] using! StatePayloadBound.mono s (stateWidth s)
          (max (stateWidth s) (runWidth p next)) (stateWidth_bound s) (Nat.le_max_left _ _)
      · simpa only [runWidth,he] using! PayloadBound.mono p next (runWidth p next)
          (max (stateWidth s) (runWidth p next)) (ih next) (Nat.le_max_right _ _)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
