/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

/-!
# Bounded binary preparation loop

The stack-machine `program` iterates the binary update `Data.next` under control of a binary
counter. The relation `Models` connects these word-level updates to numerical trial iteration,
yielding the `intBisect` result from `initialData`.

The module bounds word growth, execution steps, clock costs, and stack height. For background on
classical machine models in quantum computation, see [KitaevShenVyalyi2002].

## Main statements

* `machine_intBisect`: the loop computes the integer bisection result and clears its counter
  stacks.
* `complete_ticks`: an explicit bound on the number of loop steps.
* `complete_bounds`: bounds on total clock cost, maximum clock cost, and stack height.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatListFind
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- The five binary words carrying the square, linear, denominator, right-hand side, and
accumulated-result data of the preparation loop. -/
structure Data where
  sq4 : Bits
  lin2 : Bits
  q : Bits
  rhs : Bits
  a : Bits
  deriving DecidableEq

/-- Stores the five data words in the twelve stacks used by a trial round, with all auxiliary
stacks empty. -/
def dataStore (d : Data) : Fin 12 → Bits :=
  TrialEmit.store d.sq4 d.lin2 d.q d.rhs d.a [] [] [] [] [] [] []

/-- Updates the five data words by one trial round, including the next bit of the accumulated
result. -/
def Data.next (d : Data) : Data :=
  ⟨false::false::TrialRound.AState.emit (TrialRound.stS d.sq4 d.lin2 d.q d.rhs),
    false::TrialRound.AState.emit (TrialRound.stL d.sq4 d.lin2 d.q d.rhs),
    (TrialRound.outQA d.sq4 d.lin2 d.q d.rhs).reverse,
    (TrialRound.outR4 d.sq4 d.lin2 d.q d.rhs).reverse,
    (!(TrialRound.runState d.sq4 d.lin2 d.q d.rhs).w)::d.a⟩

/-- The comparison-local state produced by a trial round on the given data. -/
def finalCore (d : Data) : TrialCompare.Local :=
  (TrialRound.roundCfg d.sq4 d.lin2 d.q d.rhs d.a).var

/-- The stack store produced by one trial round is the canonical store of the updated data. -/
theorem next_store (d : Data) :
    (TrialRound.roundCfg d.sq4 d.lin2 d.q d.rhs d.a).stk = dataStore d.next := rfl

/-- The twelve arithmetic stacks together with the two counter stacks. -/
abbrev Slot := Fin 12 ⊕ Fin 2
/-- The pair of comparison-local and counter-local states used by the loop. -/
abbrev Local := TrialCompare.Local × Counter.Local

/-- Control labels for trial rounds, counter decrements, branching, and final cleanup. -/
inductive Label where
  | round : TrialRound.Label → Label
  | counter : Counter.Label → Label
  | branch
  | finish
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.counter .borrow⟩

/-- Replaces the comparison-local component while preserving the counter-local state. -/
def putCore (v : Local) (w : TrialCompare.Local) : Local := (w,v.2)
/-- Replaces the counter-local component while preserving the comparison-local state. -/
def putCounter (v : Local) (w : Counter.Local) : Local := (v.1,w)

/-- The stack-machine program that decrements a binary counter, performs trial rounds, and
clears the counter before halting. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .round l => StackCall.stmt Sum.inl Label.round (.counter .borrow)
      Prod.fst putCore (TrialRound.program l)
  | .counter l => StackCall.stmt Sum.inr Label.counter .branch
      Prod.snd putCounter (Counter.program l)
  | .branch => .branch (fun v => v.2.1)
      (.load (fun v => (TrialRound.resetLocal,v.2)) (.goto (fun _ => .round .init)))
      (.goto (fun _ => .finish))
  | .finish => .pop (.inr 0) (fun v b => (v.1,(v.2.1,b)))
      (.branch (fun v => v.2.2.isNone)
        (.load (fun _ => (TrialRound.resetLocal,(false,none))) .halt)
        (.goto (fun _ => .finish)))

/-- Combines the arithmetic data store with a counter word and a temporary counter word. -/
def store (counter temporary : Bits) (d : Data) : Slot → Bits :=
  Sum.elim (dataStore d) (stackPair counter temporary)

/-- The configuration at the start of a counter decrement, with the temporary counter stack
empty. -/
def loopCfg (counter : Bits) (d : Data) (v : Local) :
    TM2.Cfg (fun _ : Slot => Bool) Label Local :=
  ⟨some (.counter .borrow),v,store counter [] d⟩

/-- The configuration that branches on the counter-decrement result. -/
def branchCfg (counter : Bits) (d : Data) (v : Local) :
    TM2.Cfg (fun _ : Slot => Bool) Label Local :=
  ⟨some .branch,v,store counter [] d⟩

/-- The trial-round entry configuration with the comparison-local state reset. -/
def roundEntry (counter : Bits) (d : Data) (v : Counter.Local) :
    TM2.Cfg (fun _ : Slot => Bool) Label Local :=
  ⟨some (.round .init),(TrialRound.resetLocal,v),store counter [] d⟩

/-- The embedded trial round produces the updated data and final comparison state, with the same
clock cost as the standalone round. -/
theorem round_call (counter : Bits) (d : Data) (v : Counter.Local) :
    stackRun program (TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs) (roundEntry counter d v) =
      some (loopCfg counter d.next (finalCore d,v)) ∧
    stackRunClock program (TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs) (roundEntry counter d v) =
      stackRunClock TrialRound.program (TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs)
        (TrialRound.startCfg d.sq4 d.lin2 d.q d.rhs d.a) := by
  have h := StackCall.execution Sum.inl Label.round (.counter .borrow) Prod.fst putCore
    (StackCall.leftFrame (stackPair counter []))
    (StackCall.leftFrame_at (stackPair counter []))
    (StackCall.leftFrame_update (stackPair counter []))
    (fun _ _ => rfl) (fun _ _ _ => rfl) TrialRound.program program (fun _ => rfl)
    (TrialRound.resetLocal,v) _ _ _ (TrialRound.round_run d.sq4 d.lin2 d.q d.rhs d.a)
  exact h

/-- A positive binary counter is decremented without changing its word length, using at most
twice its length plus three steps and a quadratic clock bound. -/
theorem decrement_positive (counter : Bits) (d : Data) (v : Local)
    (hp : 0 < binaryValue counter) :
    ∃ ticks next, ticks  ≤  2*counter.length+3 ∧ next.length=counter.length ∧
      binaryValue next+1=binaryValue counter ∧
      stackRun program ticks (loopCfg counter d v) =
        some (branchCfg next d (v.1,(true,none))) ∧
      stackRunClock program ticks (loopCfg counter d v)  ≤  10*(1+counter.length)^2 := by
  obtain ⟨ticks,next,ht,hlen,hval,hr,hc⟩ := Counter.decrement_positive counter v.2 hp
  have h := StackCall.execution Sum.inr Label.counter Label.branch Prod.snd putCounter
    (StackCall.rightFrame (dataStore d)) (StackCall.rightFrame_at (dataStore d))
    (StackCall.rightFrame_update (dataStore d)) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Counter.program program (fun _ => rfl) v ticks _ _ hr
  refine ⟨ticks,next,ht,hlen,hval,?_,?_⟩
  · exact h.1
  · exact h.2.trans_le hc

/-- Decrementing a zero-valued counter produces an all-true word of the same length and a false
continuation flag, with a quadratic clock bound. -/
theorem decrement_zero (counter : Bits) (d : Data) (v : Local)
    (hz : binaryValue counter=0) :
    stackRun program (2*counter.length+2) (loopCfg counter d v) =
      some (branchCfg (List.replicate counter.length true) d (v.1,(false,none))) ∧
    stackRunClock program (2*counter.length+2) (loopCfg counter d v)  ≤  10*(1+counter.length)^2 := by
  obtain ⟨hr,hc⟩ := Counter.decrement_zero counter v.2 hz
  have h := StackCall.execution Sum.inr Label.counter Label.branch Prod.snd putCounter
    (StackCall.rightFrame (dataStore d)) (StackCall.rightFrame_at (dataStore d))
    (StackCall.rightFrame_update (dataStore d)) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Counter.program program (fun _ => rfl) v _ _ _ hr
  exact ⟨h.1,h.2.trans_le hc⟩

/-- A true continuation flag enters a fresh trial round in one step. -/
theorem branch_positive (counter : Bits) (d : Data) (v : TrialCompare.Local) :
    stackRun program 1 (branchCfg counter d (v,(true,none))) =
      some (roundEntry counter d (true,none)) := by
  simp [stackRun,TM2.step,program,branchCfg,roundEntry,TM2.stepAux]

instance : Fintype TrialCompare.Local :=
  Fintype.ofEquiv (Option Bool × Option Bool × Option Bool × Option Bool × Bool × Bool × Bool)
    { toFun := fun v => ⟨v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2.1,v.2.2.2.2.2.2⟩
      invFun := fun v => (v.oa,v.ob,v.od,v.orr,v.c0,v.c1,v.w)
      left_inv := by intro v; rcases v with ⟨a,b,c,d,e,f,g⟩; rfl
      right_inv := by intro v; cases v; rfl }

/-- The cleanup configuration that drains the remaining counter word. -/
def finishCfg (counter : Bits) (d : Data) (v : Local) :
    TM2.Cfg (fun _ : Slot => Bool) Label Local :=
  ⟨some .finish,v,store counter [] d⟩

/-- The halted configuration with the given arithmetic data, empty counter stacks, and reset
local state. -/
def haltedCfg (d : Data) : TM2.Cfg (fun _ : Slot => Bool) Label Local :=
  ⟨none,(TrialRound.resetLocal,(false,none)),store [] [] d⟩

/-- Updating the counter stack replaces the counter word in the combined store. -/
theorem store_update_counter (counter temporary : Bits) (d : Data) (bits : Bits) :
    Function.update (store counter temporary d) (.inr 0) bits = store bits temporary d := by
  change Function.update (StackCall.rightFrame (dataStore d) (stackPair counter temporary))
      (.inr 0) bits = _
  rw [← StackCall.rightFrame_update,stackPair_update_zero]
  rfl

/-- A false continuation flag enters counter cleanup in one step. -/
theorem branch_zero (counter : Bits) (d : Data) (v : TrialCompare.Local) :
    stackRun program 1 (branchCfg counter d (v,(false,none))) =
      some (finishCfg counter d (v,(false,none))) := by
  simp [stackRun,TM2.step,program,branchCfg,finishCfg,TM2.stepAux]

/-- One cleanup step pops the leading counter bit and records it in the local state. -/
theorem finish_step (b : Bool) (counter : Bits) (d : Data) (v : Local) :
    TM2.step program (finishCfg (b::counter) d v) =
      some (finishCfg counter d (v.1,(v.2.1,some b))) := by
  simp [TM2.step,program,finishCfg,TM2.stepAux,store]

/-- Cleanup of an empty counter reaches the canonical halted configuration in one step. -/
theorem finish_nil (d : Data) (v : Local) :
    stackRun program 1 (finishCfg [] d v) = some (haltedCfg d) := by
  simp [stackRun,TM2.step,program,finishCfg,haltedCfg,TM2.stepAux,store]

/-- Cleanup drains a counter word and halts in its length plus one steps. -/
theorem finish_run (counter : Bits) (d : Data) (v : Local) :
    stackRun program (counter.length+1) (finishCfg counter d v) = some (haltedCfg d) := by
  induction counter generalizing v with
  | nil => exact finish_nil d v
  | cons b counter ih =>
    rw [show (b::counter).length+1=1+(counter.length+1) by simp; omega,run_add]
    have h : stackRun program 1 (finishCfg (b::counter) d v) =
        some (finishCfg counter d (v.1,(v.2.1,some b))) := by
      simp only [stackRun,finish_step,Option.bind_some]
    rw [h,Option.bind_some]
    exact ih _

/-- A counter of value `n` causes exactly `n` data updates before the program reaches the
canonical halted configuration. -/
theorem complete (n : ℕ) (counter : Bits) (d : Data) (v : Local)
    (hnum : binaryValue counter=n) :
    ∃ ticks, stackRun program ticks (loopCfg counter d v) =
      some (haltedCfg ((Data.next^[n]) d)) := by
  induction n generalizing counter d v with
  | zero =>
    have hD := (decrement_zero counter d v hnum).1
    have hDB : stackRun program ((2*counter.length+2)+1) (loopCfg counter d v) =
        some (finishCfg (List.replicate counter.length true) d (v.1,(false,none))) := by
      rw [run_add,hD,Option.bind_some,branch_zero]
    refine ⟨((2*counter.length+2)+1)+(counter.length+1),?_⟩
    rw [run_add,hDB,Option.bind_some]
    simpa only [List.length_replicate,Function.iterate_zero_apply] using!
      finish_run (List.replicate counter.length true) d (v.1,(false,none))
  | succ n ih =>
    obtain ⟨decTicks,next,_,_,hval,hD,_⟩ := decrement_positive counter d v (by omega)
    have hDB : stackRun program (decTicks+1) (loopCfg counter d v) =
        some (roundEntry next d (true,none)) := by
      rw [run_add,hD,Option.bind_some,branch_positive]
    have hR := (round_call next d (true,none)).1
    have hDBR : stackRun program ((decTicks+1)+TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs)
        (loopCfg counter d v) = some (loopCfg next d.next (finalCore d,(true,none))) := by
      rw [run_add,hDB,Option.bind_some,hR]
    obtain ⟨iterTicks,hI⟩ := ih next d.next (finalCore d,(true,none)) (by omega)
    refine ⟨((decTicks+1)+TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs)+iterTicks,?_⟩
    rw [run_add,hDBR,Option.bind_some]
    simpa only [Function.iterate_succ_apply] using! hI

/-- Relates binary data to a numerical trial state: the square and linear words represent `4 *
s.sq` and `2 * s.lin2`, and the other words represent `Q`, `s.rhs`, and `s.a`. -/
def Models (Q : ℕ) (s : TrialEmit.MState) (d : Data) : Prop :=
  binaryValue d.sq4=4*s.sq ∧ binaryValue d.lin2=2*s.lin2 ∧ binaryValue d.q=Q ∧
  binaryValue d.rhs=s.rhs ∧ binaryValue d.a=s.a

/-- One binary data update preserves the relation to the corresponding numerical trial step. -/
theorem models_next {Q : ℕ} {s : TrialEmit.MState} {d : Data} (h : Models Q s d) :
    Models Q (TrialEmit.mStep Q s) d.next := by
  obtain ⟨hs,hl,hq,hr,ha⟩ := h
  have hc : (binaryValue d.sq4+binaryValue d.lin2+binaryValue d.q  ≤  binaryValue d.rhs) =
      (TrialEmit.mBit Q s=1) := by
    apply propext
    rw [TrialEmit.mBit_eq_one_iff,hs,hl,hq,hr]
    rfl
  have hb : (!(TrialRound.runState d.sq4 d.lin2 d.q d.rhs).w) =
      decide (TrialEmit.mBit Q s=1) := by
    rw [TrialRound.round_bit]
    simp only [hc]
  obtain ⟨h0,h1,h2,h3,h4⟩ := TrialRound.round_value d.sq4 d.lin2 d.q d.rhs d.a
  refine ⟨?_,?_,?_,?_,?_⟩
  · change binaryValue ((TrialRound.roundCfg d.sq4 d.lin2 d.q d.rhs d.a).stk 0) = _
    rw [h0,hb,hs,hl,hq,TrialEmit.mStep_sq]
    by_cases hbit : TrialEmit.mBit Q s=1 <;> simp [hbit,TrialEmit.mTrial]; ring
  · change binaryValue ((TrialRound.roundCfg d.sq4 d.lin2 d.q d.rhs d.a).stk 1) = _
    rw [h1,hb,hl,hq,TrialEmit.mStep_lin2]
    by_cases hbit : TrialEmit.mBit Q s=1 <;> simp [hbit]
  · exact h2.trans hq
  · change binaryValue ((TrialRound.roundCfg d.sq4 d.lin2 d.q d.rhs d.a).stk 3) = _
    rw [h3,hr,TrialEmit.mStep_rhs_field]
  · change binaryValue ((TrialRound.roundCfg d.sq4 d.lin2 d.q d.rhs d.a).stk 4) = _
    rw [h4,hb,ha,TrialEmit.mStep_a_field]
    by_cases hbit : TrialEmit.mBit Q s=1 <;> simp [hbit]

/-- Iterating the binary update preserves the relation to the numerical trial iteration. -/
theorem models_iterate {Q : ℕ} {s : TrialEmit.MState} {d : Data} (h : Models Q s d) (n : ℕ) :
    Models Q (TrialEmit.mIterate Q n s) ((Data.next^[n]) d) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simpa only [Function.iterate_succ_apply',TrialEmit.mIterate] using! models_next ih

/-- The initial binary data for parameters `P` and `Q`, with denominator `Q`, right-hand side `4
* P`, and the other words empty. -/
def initialData (P Q : ℕ) : Data := ⟨[],[],Nat.bits Q,Nat.bits (4*P),[]⟩

/-- The initial binary data models the initial numerical trial state. -/
theorem initial_models (P Q : ℕ) : Models Q (TrialEmit.mInit P) (initialData P Q) := by
  simp [Models,initialData,TrialEmit.mInit,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]

/-- The result word after `k` binary updates represents `intBisect P Q k`. -/
theorem iterate_intBisect (P Q k : ℕ) :
    binaryValue (((Data.next^[k]) (initialData P Q)).a) = intBisect P Q k := by
  have h := (models_iterate (initial_models P Q) k).2.2.2.2
  exact h.trans (TrialEmit.mIterate_intBisect P Q k)

/-- The loop computes `intBisect P Q k` from the standard initial data and binary counter,
halting with both counter stacks empty. -/
theorem machine_intBisect (P Q k : ℕ) :
    ∃ ticks last, stackRun program ticks
        (loopCfg (Nat.bits k) (initialData P Q) (TrialRound.resetLocal,(false,none))) = some last ∧
      last.l=none ∧ binaryValue (last.stk (.inl 4))=intBisect P Q k ∧
      last.stk (.inr 0)=[] ∧ last.stk (.inr 1)=[] := by
  obtain ⟨ticks,hr⟩ := complete k (Nat.bits k) (initialData P Q)
    (TrialRound.resetLocal,(false,none)) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits k)
  refine ⟨ticks,haltedCfg ((Data.next^[k]) (initialData P Q)),hr,rfl,?_,rfl,rfl⟩
  exact iterate_intBisect P Q k

/-- The maximum length of the five binary data words. -/
def Data.width (d : Data) : ℕ :=
  max d.sq4.length (max d.lin2.length (max d.q.length (max d.rhs.length d.a.length)))

/-- Each data-word length is bounded by the data width. -/
theorem width_fields (d : Data) :
    d.sq4.length ≤ d.width ∧ d.lin2.length ≤ d.width ∧ d.q.length ≤ d.width ∧
    d.rhs.length ≤ d.width ∧ d.a.length ≤ d.width := by
  unfold Data.width
  omega

/-- Comparison fuel is at most `m + 4` when all four comparison words have length at most `m`. -/
theorem compare_fuel_le (m : ℕ) (st : TrialCompare.CState)
    (ha : st.a.length ≤ m) (hb : st.b.length ≤ m) (hd : st.d.length ≤ m) (hr : st.r.length ≤ m) :
    TrialCompare.fuel st  ≤  m+4 := by
  induction m generalizing st with
  | zero =>
    have hf := TrialCompare.fuel_le st
    have hc : st.cval  ≤  3 := by
      cases h0 : st.c0 <;> cases h1 :
          st.c1 <;> simp [TrialCompare.CState.cval,TrialCompare.carryOf,h0,h1]
    omega
  | succ m ih =>
    by_cases hh : st.halted
    · rw [TrialCompare.fuel.eq_def,if_pos hh]
      omega
    · rw [TrialCompare.fuel.eq_def,if_neg hh]
      have hf := ih (TrialCompare.CState.step st)
        (by change st.a.tail.length ≤ m; simp only [List.length_tail]; omega)
        (by change st.b.tail.length ≤ m; simp only [List.length_tail]; omega)
        (by change st.d.tail.length ≤ m; simp only [List.length_tail]; omega)
        (by change st.r.tail.length ≤ m; simp only [List.length_tail]; omega)
      omega

/-- Addition fuel is at most `m + 4` when its three state words have length at most `m`. -/
theorem addition_fuel_le (m : ℕ) (st : TrialRound.AState)
    (hx : st.x.length ≤ m) (hy : st.y.length ≤ m) (hz : st.z.length ≤ m) :
    st.fuel  ≤  m+4 := by
  induction m generalizing st with
  | zero =>
    have hf := TrialRound.AState.fuel_le st
    have hc : st.cval  ≤  3 := by
      cases h0 : st.c0 <;> cases h1 : st.c1 <;>
        simp [TrialRound.AState.cval,TrialCompare.carryOf,h0,h1]
    omega
  | succ m ih =>
    by_cases hh : st.halted
    · rw [TrialRound.AState.fuel.eq_def,if_pos hh]
      omega
    · rw [TrialRound.AState.fuel.eq_def,if_neg hh]
      have hf := ih (TrialRound.AState.next st)
        (by change st.x.tail.length ≤ m; simp only [List.length_tail]; omega)
        (by change st.y.tail.length ≤ m; simp only [List.length_tail]; omega)
        (by change st.z.tail.length ≤ m; simp only [List.length_tail]; omega)
      omega

/-- Each word emitted by a comparison state has length at most its fuel. -/
theorem compare_emit_lengths (st : TrialCompare.CState) :
    (TrialEmit.emitS st).length ≤ TrialCompare.fuel st ∧
    (TrialEmit.emitL st).length ≤ TrialCompare.fuel st ∧
    (TrialEmit.emitQ st).length ≤ TrialCompare.fuel st ∧
    (TrialEmit.emitR st).length ≤ TrialCompare.fuel st := by
  induction st using TrialCompare.fuel.induct with
  | case1 st hh =>
    have hf : TrialCompare.fuel st=1 := by rw [TrialCompare.fuel.eq_def,if_pos hh]
    refine ⟨?_,?_,?_,?_⟩
    · rw [TrialEmit.emitS.eq_def,if_pos hh,hf]; simp
    · rw [TrialEmit.emitL.eq_def,if_pos hh,hf]; simp
    · rw [TrialEmit.emitQ.eq_def,if_pos hh,hf]; simp
    · rw [TrialEmit.emitR.eq_def,if_pos hh,hf]; simp
  | case2 st hh ih =>
    have hf : TrialCompare.fuel st=1+TrialCompare.fuel (TrialCompare.CState.step st) := by
      rw [TrialCompare.fuel.eq_def,if_neg hh]
    obtain ⟨hs,hl,hq,hr⟩ := ih
    refine ⟨?_,?_,?_,?_⟩
    · rw [TrialEmit.emitS.eq_def,if_neg hh,List.length_cons,hf]
      omega
    · rw [TrialEmit.emitL.eq_def,if_neg hh,List.length_cons,hf]
      omega
    · rw [TrialEmit.emitQ.eq_def,if_neg hh,List.length_cons,hf]
      omega
    · rw [TrialEmit.emitR.eq_def,if_neg hh,List.length_cons,hf]
      omega

/-- The word emitted by an addition state has length at most its fuel. -/
theorem addition_emit_length (st : TrialRound.AState) : st.emit.length ≤ st.fuel := by
  induction st using TrialRound.AState.fuel.induct with
  | case1 st hh =>
    rw [TrialRound.AState.fuel.eq_def,TrialRound.AState.emit.eq_def,if_pos hh]
    simp
  | case2 st hh ih =>
    rw [TrialRound.AState.fuel.eq_def,TrialRound.AState.emit.eq_def,if_neg hh,if_neg hh,List.length_cons]
    omega

/-- The seven intermediate output lengths of a trial round are bounded by the input width plus
the stated constants. -/
theorem round_out_lengths (d : Data) :
    (TrialRound.outL d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+4 ∧
    (TrialRound.outS d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+4 ∧
    (TrialRound.outB d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+4 ∧
    (TrialRound.outQ2 d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+5 ∧
    (TrialRound.outR4 d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+6 ∧
    (TrialRound.outQA d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+4 ∧
    (TrialRound.outQB d.sq4 d.lin2 d.q d.rhs).length ≤ d.width+4 := by
  obtain ⟨ha,hb,hq,hr,_⟩ := width_fields d
  have hf := compare_fuel_le d.width (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs) ha hb hq hr
  obtain ⟨hS,hL,hQ,hR⟩ := compare_emit_lengths (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)
  have hs := hS.trans hf
  have hl := hL.trans hf
  have hq := hQ.trans hf
  have hr := hR.trans hf
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change ((TrialEmit.emitL (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[]).length ≤ _
    simpa only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] using! hl
  · change ((TrialEmit.emitS (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[]).length ≤ _
    simpa only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] using! hs
  · change ((TrialEmit.emitL (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[]).length ≤ _
    simpa only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] using! hl
  · change ((TrialEmit.emitQ (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[false]).length ≤ _
    simp only [List.length_append,List.length_reverse,List.length_cons,List.length_nil]
    omega
  · change ((TrialEmit.emitR (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[false,false]).length ≤ _
    simp only [List.length_append,List.length_reverse,List.length_cons,List.length_nil]
    omega
  · change ((TrialEmit.emitQ (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[]).length ≤ _
    simpa only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] using! hq
  · change ((TrialEmit.emitQ (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs)).reverse++[]).length ≤ _
    simpa only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] using! hq

/-- A trial round uses at most `20 * (d.width + 10)` fuel and increases the data width by at
most ten. -/
theorem round_budget (d : Data) :
    TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs ≤ 20*(d.width+10) ∧
    d.next.width ≤ d.width+10 := by
  obtain ⟨hL,hS,hB,hQ2,hR4,hQA,hQB⟩ := round_out_lengths d
  obtain ⟨ha,hb,hq,hr,haa⟩ := width_fields d
  have hcmp := compare_fuel_le d.width (TrialRound.st0 d.sq4 d.lin2 d.q d.rhs) ha hb hq hr
  have hlin : (TrialRound.stL d.sq4 d.lin2 d.q d.rhs).fuel ≤ d.width+9 := by
    apply addition_fuel_le (d.width+5)
    · change (TrialRound.outL d.sq4 d.lin2 d.q d.rhs).reverse.length ≤ _
      rw [List.length_reverse]
      omega
    · change (TrialRound.outQ2 d.sq4 d.lin2 d.q d.rhs).reverse.length ≤ _
      rw [List.length_reverse]
      exact hQ2
    · change [].length ≤ d.width+5
      simp
  have hsq : (TrialRound.stS d.sq4 d.lin2 d.q d.rhs).fuel ≤ d.width+8 := by
    apply addition_fuel_le (d.width+4)
    · change (TrialRound.outS d.sq4 d.lin2 d.q d.rhs).reverse.length ≤ _
      simpa only [List.length_reverse] using! hS
    · change (TrialRound.outB d.sq4 d.lin2 d.q d.rhs).reverse.length ≤ _
      simpa only [List.length_reverse] using! hB
    · change (TrialRound.outQB d.sq4 d.lin2 d.q d.rhs).reverse.length ≤ _
      simpa only [List.length_reverse] using! hQB
  have helm := (addition_emit_length (TrialRound.stL d.sq4 d.lin2 d.q d.rhs)).trans hlin
  have hesm := (addition_emit_length (TrialRound.stS d.sq4 d.lin2 d.q d.rhs)).trans hsq
  constructor
  · unfold TrialRound.roundFuel
    simp only [List.length_reverse]
    omega
  · change max d.next.sq4.length (max d.next.lin2.length
      (max d.next.q.length (max d.next.rhs.length d.next.a.length))) ≤ d.width+10
    dsimp only [Data.next]
    simp only [List.length_cons,List.length_reverse]
    omega

/-- After `n` data updates, the width is at most the initial width plus `10 * n`. -/
theorem iterate_width (n : ℕ) (d : Data) : ((Data.next^[n]) d).width ≤ d.width+10*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := (round_budget ((Data.next^[n]) d)).2
    omega

/-- The loop halts after the prescribed number of updates with an explicit bound on the number
of stack-machine steps. -/
theorem complete_ticks (n : ℕ) (counter : Bits) (d : Data) (v : Local)
    (hnum : binaryValue counter=n) :
    ∃ ticks, stackRun program ticks (loopCfg counter d v) =
      some (haltedCfg ((Data.next^[n]) d)) ∧
      ticks ≤ 30*(n+1)*(counter.length+d.width+10*n+10) := by
  induction n generalizing counter d v with
  | zero =>
    have hD := (decrement_zero counter d v hnum).1
    have hDB : stackRun program ((2*counter.length+2)+1) (loopCfg counter d v) =
        some (finishCfg (List.replicate counter.length true) d (v.1,(false,none))) := by
      rw [run_add,hD,Option.bind_some,branch_zero]
    refine ⟨((2*counter.length+2)+1)+(counter.length+1),?_,?_⟩
    · rw [run_add,hDB,Option.bind_some]
      simpa only [List.length_replicate,Function.iterate_zero_apply] using!
        finish_run (List.replicate counter.length true) d (v.1,(false,none))
    · nlinarith
  | succ n ih =>
    obtain ⟨decTicks,next,hdec,hlen,hval,hD,_⟩ := decrement_positive counter d v (by omega)
    have hDB : stackRun program (decTicks+1) (loopCfg counter d v) =
        some (roundEntry next d (true,none)) := by
      rw [run_add,hD,Option.bind_some,branch_positive]
    have hR := (round_call next d (true,none)).1
    have hDBR : stackRun program ((decTicks+1)+TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs)
        (loopCfg counter d v) = some (loopCfg next d.next (finalCore d,(true,none))) := by
      rw [run_add,hDB,Option.bind_some,hR]
    obtain ⟨iterTicks,hI,hIt⟩ := ih next d.next (finalCore d,(true,none)) (by omega)
    refine ⟨((decTicks+1)+TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs)+iterTicks,?_,?_⟩
    · rw [run_add,hDBR,Option.bind_some]
      simpa only [Function.iterate_succ_apply] using! hI
    · have hwidth := (round_budget d).2
      have hfuel := (round_budget d).1
      have hinner : next.length+d.next.width+10*n+10 ≤ counter.length+d.width+10*(n+1)+10 := by
        omega
      have hit := hIt.trans (Nat.mul_le_mul_left (30*(n+1)) hinner)
      have hhead : decTicks+1+TrialRound.roundFuel d.sq4 d.lin2 d.q d.rhs ≤
          30*(counter.length+d.width+10*(n+1)+10) := by omega
      nlinarith

/-- Embedding a stack-machine statement as a subroutine preserves its number of statement nodes. -/
theorem call_nodes {K J Λ Λ' σ ρ : Type} [DecidableEq K] [DecidableEq J]
    (stackCode : K → J) (labelCode : Λ → Λ') (returnTo : Λ') (get : ρ → σ)
    (put : ρ → σ → ρ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    stackNodes (StackCall.stmt stackCode labelCode returnTo get put q) = stackNodes q := by
  induction q with
  | push k f q ih => simp only [StackCall.stmt,stackNodes,ih]
  | peek k f q ih => simp only [StackCall.stmt,stackNodes,ih]
  | pop k f q ih => simp only [StackCall.stmt,stackNodes,ih]
  | load f q ih => simp only [StackCall.stmt,stackNodes,ih]
  | branch p a b iha ihb => simp only [StackCall.stmt,stackNodes,iha,ihb]
  | goto f => rfl
  | halt => rfl

/-- The value `programNodes program` is at most eleven. -/
theorem program_nodes_le : programNodes program ≤ 11 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l with
  | round l => rw [program,call_nodes]; exact TrialRound.stackNodes_program l
  | counter l =>
    rw [program,call_nodes]
    cases l <;> simp [Counter.program,stackNodes]
  | branch => simp [program,stackNodes]
  | finish => simp [program,stackNodes]

/-- The sweep factor of the loop program is at most 265. -/
theorem sweep_factor_le : sweepFactor program ≤ 265 := by
  have h := program_nodes_le
  unfold sweepFactor
  nlinarith

/-- The initial stack height is bounded by the sum of the counter length and the data width. -/
theorem initial_height (counter : Bits) (d : Data) (v : Local) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (loopCfg counter d v).stk ≤ counter.length+d.width := by
  obtain ⟨ha,hb,hq,hr,haa⟩ := width_fields d
  unfold Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro slot _
  cases slot with
  | inl i => fin_cases i <;> simp [loopCfg,store,dataStore,TrialEmit.store] <;> omega
  | inr i => fin_cases i <;> simp [loopCfg,store,stackPair]

/-- The loop halts with the iterated data and satisfies the stated bounds on total clock cost,
maximum clock cost, and maximum stack height. -/
theorem complete_bounds (n : ℕ) (counter : Bits) (d : Data) (v : Local)
    (hnum : binaryValue counter=n) :
    ∃ ticks, stackRun program ticks (loopCfg counter d v) =
      some (haltedCfg ((Data.next^[n]) d)) ∧
      stackRunClock program ticks (loopCfg counter d v) ≤
        4000000*(n+1)^2*(counter.length+d.width+10*n+10)^2 ∧
      stackRunMaxClock program ticks (loopCfg counter d v) ≤
        200000*(n+1)*(counter.length+d.width+10*n+10) ∧
      stackRunMaxHeight program ticks (loopCfg counter d v) ≤
        400*(n+1)*(counter.length+d.width+10*n+10) := by
  obtain ⟨ticks,hr,ht⟩ := complete_ticks n counter d v hnum
  let L := counter.length+d.width+10*n+10
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hh := initial_height counter d v
  have hn := program_nodes_le
  have hs := sweep_factor_le
  have hheight :
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
      (loopCfg counter d v).stk ≤ L := by dsimp [L]; omega
  have hbase : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (loopCfg counter d v).stk+ticks*programNodes program+1 ≤
      400*(n+1)*L := by
    have hm := Nat.mul_le_mul ht hn
    change ticks*programNodes program ≤ (30*(n+1)*L)*11 at hm
    nlinarith
  refine ⟨ticks,hr,?_,?_,?_⟩
  · have hp := Nat.mul_le_mul (Nat.mul_le_mul ht hs) hbase
    have hb :=
        Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le program ticks (loopCfg counter d v)
    calc
      _ ≤ ticks*sweepFactor program*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (loopCfg counter d v).stk+ticks*programNodes program+1) := hb
      _ ≤ (30*(n+1)*L)*265*(400*(n+1)*L) := hp
      _ = 3180000*(n+1)^2*L^2 := by ring
      _ ≤ _ := by dsimp [L]; nlinarith [sq_nonneg ((n+1)*(counter.length+d.width+10*n+10):ℤ)]
  · have hp := Nat.mul_le_mul hs hbase
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le program ticks (loopCfg counter d v)).trans
      (hp.trans (by dsimp [L]; nlinarith))
  · have hb := Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxHeight_le program ticks (loopCfg counter d v)
    exact hb.trans (by dsimp [L] at hbase ⊢; omega)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop
