/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatListFind
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod (addTurns_os_length carryAddAux)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)

section Generic
variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]

omit [Fintype K] [Fintype Λ] in

theorem stepAux_length_le (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (v : σ) (S : K → List Bool) (H : ℕ) (hS : ∀ k, (S k).length ≤ H) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ H+stackNodes q := by
  induction q generalizing v S H with
  | push k f q ih =>
    have hnew : ∀ j, (Function.update S k (f v :: S k) j).length ≤ H+1 := by
      intro j
      by_cases hj : j=k
      · subst j
        simp only [Function.update_self,List.length_cons]
        exact Nat.succ_le_succ (hS k)
      · rw [Function.update_of_ne hj]
        exact (hS j).trans (Nat.le_succ H)
    intro j
    have hb := ih v (Function.update S k (f v :: S k)) (H+1) hnew j
    change ((TM2.stepAux q v (Function.update S k (f v :: S k))).stk j).length ≤ _
    simpa only [stackNodes,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using! hb
  | peek k f q ih =>
    intro j
    have hb := ih (f v (S k).head?) S H hS j
    change ((TM2.stepAux q (f v (S k).head?) S).stk j).length ≤ _
    exact hb.trans (by simp only [stackNodes]; omega)
  | pop k f q ih =>
    have hnew : ∀ j, (Function.update S k (S k).tail j).length ≤ H := by
      intro j
      by_cases hj : j=k
      · subst j
        simp only [Function.update_self]
        have ht : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
        exact ht.trans (hS k)
      · rw [Function.update_of_ne hj]
        exact hS j
    intro j
    have hb := ih (f v (S k).head?) (Function.update S k (S k).tail) H hnew j
    change ((TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk j).length ≤ _
    exact hb.trans (by simp only [stackNodes]; omega)
  | load f q ih => simpa only [TM2.stepAux,stackNodes] using! ih (f v) S H hS
  | branch p a b iha ihb =>
    intro j
    cases hp : p v
    · simp only [TM2.stepAux,hp,cond_false]
      exact (ihb v S H hS j).trans (Nat.add_le_add_left (Nat.le_max_right _ _) H)
    · simp only [TM2.stepAux,hp,cond_true]
      exact (iha v S H hS j).trans (Nat.add_le_add_left (Nat.le_max_left _ _) H)
  | goto f => simpa only [TM2.stepAux,stackNodes,Nat.add_zero] using! hS
  | halt => simpa only [TM2.stepAux,stackNodes,Nat.add_zero] using! hS

theorem step_height_le (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (first next : TM2.Cfg (fun _ : K => Bool) Λ σ) (hs : TM2.step M first=some next) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight next.stk ≤ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+programNodes M := by
  rcases first with ⟨l,v,S⟩
  cases l with
  | none => simp only [TM2.step,reduceCtorEq] at hs
  | some l =>
    have he : TM2.stepAux (M l) v S=next := Option.some.inj hs
    have hS : ∀ k, (S k).length ≤ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight S := fun k =>
      Finset.le_sup (f:=fun k => (S k).length) (Finset.mem_univ k)
    have hn : stackNodes (M l) ≤ programNodes M :=
      Finset.le_sup (f:=fun l => stackNodes (M l)) (Finset.mem_univ l)
    rw [← he]
    apply Finset.sup_le
    intro k _
    exact (stepAux_length_le (M l) v S (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight S) hS k).trans (Nat.add_le_add_left hn _)

theorem runMaxHeight_le (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (n : ℕ) (first : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    stackRunMaxHeight M n first ≤ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+n*programNodes M := by
  induction n generalizing first with
  | zero => simp only [stackRunMaxHeight,Nat.zero_mul,Nat.add_zero,le_refl]
  | succ n ih =>
    cases hs : TM2.step M first with
    | none => simp only [stackRunMaxHeight,hs]; omega
    | some next =>
      simp only [stackRunMaxHeight,hs]
      apply max_le
      · omega
      · calc
          stackRunMaxHeight M n next ≤ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight next.stk+n*programNodes M := ih next
          _ ≤ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+programNodes M)+n*programNodes M :=
            Nat.add_le_add_right (step_height_le M first next hs) _
          _ = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+(n+1)*programNodes M := by ring

theorem runClock_le (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (n : ℕ) (first : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    stackRunClock M n first ≤ n*sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+n*programNodes M+1) := by
  induction n generalizing first with
  | zero => simp only [stackRunClock,Nat.zero_mul,le_refl]
  | succ n ih =>
    cases hs : TM2.step M first with
    | none => simp only [stackRunClock,hs]; omega
    | some next =>
      rw [stackRunClock_step M n first next hs]
      have hH := step_height_le M first next hs
      have hbig : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight next.stk+n*programNodes M+1 ≤
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+(n+1)*programNodes M+1 := by
        rw [Nat.add_mul,Nat.one_mul]
        omega
      have hsmall :
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+1 ≤ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+(n+1)*programNodes M+1 := by omega
      calc
        _ ≤ sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+1)+
            n*sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight next.stk+n*programNodes M+1) :=
          add_le_add (stepClock_height M first) (ih next)
        _ ≤ sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+(n+1)*programNodes M+1)+
            n*sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+(n+1)*programNodes M+1) :=
          add_le_add (Nat.mul_le_mul_left _ hsmall) (Nat.mul_le_mul_left _ hbig)
        _ = (n+1)*sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+(n+1)*programNodes M+1) := by ring

theorem runMaxClock_le (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (n : ℕ) (first : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    stackRunMaxClock M n first ≤ sweepFactor M*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+n*programNodes M+1) :=
  (maxClock_height M n first).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (runMaxHeight_le M n first)))
end Generic

theorem mulAddBits_length (u b : Bits) : (mulAddBits u b).length=max u.length b.length+1 := by
  simp only [mulAddBits,carryAddAux,List.length_append,List.length_singleton,List.length_reverse]
  rw [addTurns_os_length]
  simp

theorem mulAcc_length (x y : Bits) (j : ℕ) : (mulAcc x y j).length ≤ x.length+2*j := by
  induction j with
  | zero => simp only [mulAcc,List.length_nil,Nat.mul_zero,Nat.add_zero]; omega
  | succ j ih =>
    rw [mulAcc]
    split
    · rw [mulAddBits_length]
      simp only [List.length_cons]
      apply (Nat.add_le_add_right (max_le
        (show (mulAcc x y j).length+1 ≤ x.length+2*j+1 by omega)
        (show x.length ≤ x.length+2*j+1 by omega)) 1).trans
      omega
    · simp only [List.length_cons]; omega

theorem mulRoundResult_length (x y : Bits) (j : ℕ) :
    (mulRoundResult x y j).length=max ((mulAcc x y j).length+1) x.length+1 := by
  simp only [mulRoundResult,mulAddFinal,mulStacks_two,List.length_cons,
    List.length_append,List.length_nil,Nat.add_zero]
  rw [addTurns_os_length]
  simp only [List.length_nil,Nat.zero_add]

theorem mulRoundTicks_le (x y : Bits) (j : ℕ) : mulRoundTicks x y j ≤ 4*x.length+4*j+8 := by
  have hlen := mulAcc_length x y j
  have hmax : max ((mulAcc x y j).length+1) x.length ≤ x.length+2*j+1 :=
      max_le (by omega) (by omega)
  unfold mulRoundTicks
  (try dsimp only)
  split
  · simp only [List.length_cons,mulRoundResult_length]; omega
  · omega

theorem mulTotalTicks_le (x y : Bits) (n : ℕ) : mulTotalTicks x y n ≤ n*(4*x.length+4*n+8) := by
  induction n with
  | zero => simp only [mulTotalTicks,Nat.zero_mul,le_refl]
  | succ n ih =>
    rw [mulTotalTicks]
    have hr := mulRoundTicks_le x y n
    calc
      _ ≤ n*(4*x.length+4*n+8)+(4*x.length+4*n+8) := add_le_add ih hr
      _ = (n+1)*(4*x.length+4*n+8) := by ring
      _ ≤ (n+1)*(4*x.length+4*(n+1)+8) := Nat.mul_le_mul_left _ (by omega)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
