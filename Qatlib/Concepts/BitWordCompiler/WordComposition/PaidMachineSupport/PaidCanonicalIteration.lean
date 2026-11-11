/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

/-!
# Uniform iteration of encoded computations

`trajectorySum` and `trajectoryCharge` account for costs and encoding lengths along repeated
applications of a state transformation. The loop-machine correctness lemmas combine these
charges with counter and input-processing costs.

`uniform_iterates` compiles all iteration counts into one binary Turing machine, with separate
quadratic bounds derived from the supplied time and space costs.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `budgetBase`: aggregates input size, iteration count, final output size, and trajectory costs.
* `uniform_iterates`: realizes repeated encoded state transformations with a uniform machine.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing
namespace Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.CanonicalIteration

/-- Sums `cost` over the first `n` states along the trajectory of `step` from `a`. -/
def trajectorySum {α : Type} (step : α → α) (cost : α → ℕ) (n : ℕ) (a : α) : ℕ :=
  ((List.range n).map (fun j => cost ((step^[j]) a))).sum

/-- The cost of a trajectory of length `n + 1` splits into the initial cost and the length-`n`
trajectory from the next state. -/
theorem trajectorySum_succ_left {α : Type} (step : α → α) (cost : α → ℕ) (n : ℕ) (a : α) :
    trajectorySum step cost (n + 1) a = cost a + trajectorySum step cost n (step a) := by
  simp only [trajectorySum, List.range_succ_eq_map, List.map_cons, List.sum_cons,
    List.map_map, Function.iterate_zero_apply, Function.comp_def, Nat.succ_eq_add_one,
    Function.iterate_succ_apply]

/-- If each of the first `n` trajectory costs is at most `C`, their sum is at most `n * C`. -/
theorem trajectorySum_le {α : Type} (step : α → α) (cost : α → ℕ) (n : ℕ) (a : α)
    (C : ℕ) (h : ∀ j < n, cost ((step^[j]) a) ≤ C) :
    trajectorySum step cost n a ≤ n * C := by
  induction n generalizing a with
  | zero => simp [trajectorySum]
  | succ n ih =>
    rw [trajectorySum_succ_left]
    have h0 := h 0 (by omega)
    simp only [Function.iterate_zero_apply] at h0
    have ht := ih (step a) (by
      intro j hj
      have hh := h (j + 1) (by omega)
      simpa only [Function.iterate_succ_apply] using hh)
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Recursively charges encoded state transitions for their input and output lengths, supplied
cost, and constant overhead, with a final encoding-length charge. -/
def trajectoryCharge {α : Type} (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α)
    (cost : α → ℕ) : ℕ → α → ℕ
  | 0, a => 1 + (encode a).length
  | n + 1, a => trajectoryCharge encode step cost n (step a) +
      (1 + (encode a).length + (encode (step a)).length + cost a)

/-- The zero-step trajectory charge is one plus the initial encoding length. -/
theorem trajectoryCharge_zero {α : Type} (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α)
    (cost : α → ℕ) (a : α) :
    trajectoryCharge encode step cost 0 a = 1 + (encode a).length := rfl

/-- The successor trajectory charge is the remaining trajectory charge plus the initial
transition's size and cost charge. -/
theorem trajectoryCharge_succ {α : Type} (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α)
    (cost : α → ℕ) (n : ℕ) (a : α) :
    trajectoryCharge encode step cost (n + 1) a =
      trajectoryCharge encode step cost n (step a) +
        (1 + (encode a).length + (encode (step a)).length + cost a) := rfl

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore in

/-- The loop core computes the encoded `n`th iterate and clears workspace, with total and
maximum stack clocks bounded by counter costs and squared trajectory charges. -/
private theorem core_complete {α : Type} {q : ℕ}
    (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1)))
    (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α) (tf sf : α → ℕ)
    (h : ∀ a, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (encode a) (encode (step a)) (tf a) (sf a))
    (n : ℕ) (counter : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (a : α) (v : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Local)
    (hnum : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue counter = n) (hhead : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.getHead v = (encode a).head?) :
    ∃ ticks,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) ticks
        ⟨some (.counter .borrow), v,
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩ =
        some ⟨none, (none, (false, none), none),
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (encode ((step^[n]) a)).reverse []⟩ ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) ticks
        ⟨some (.counter .borrow), v,
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩ ≤
        20 * (n + 1) * (1 + counter.length) ^ 2 +
          20000 * (trajectoryCharge encode step tf n a) ^ 2 ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunMaxClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) ticks
        ⟨some (.counter .borrow), v,
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩ ≤
        20 * (n + 1) * (1 + counter.length) ^ 2 +
          20000 * (trajectoryCharge encode step sf n a) ^ 2 := by
  induction n generalizing counter a v with
  | zero =>
    obtain ⟨hD,hDC⟩ :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.decrement_zero M counter []
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] [] v hnum
    have hB :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.branch_zero M v
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store (List.replicate counter.length true) [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] [])
    obtain ⟨finishTicks,hF,hFC⟩ :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.finish_call M
        (List.replicate counter.length true) (encode a)
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.putCounter v (false,none)) hhead
    have hDB : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) ((2*counter.length+2)+1)
        ⟨some (.counter .borrow),v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩=
        some ⟨some (.normalize .emit),Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.putCounter v (false,none),
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store (List.replicate counter.length true) [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩ := by
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add,hD,Option.bind_some,hB]
    have hfull : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) (((2*counter.length+2)+1)+finishTicks)
        ⟨some (.counter .borrow),v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩=
        some ⟨none,(none,(false,none),none),Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (encode a).reverse []⟩ := by
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add,hDB,Option.bind_some]
      exact hF
    have hc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) (((2*counter.length+2)+1)+finishTicks)
        ⟨some (.counter .borrow),v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩≤
        20*(1+counter.length)^2+20000*(1+(encode a).length)^2 := by
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ _ _ _ hDB,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ 1 _ _ hD,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.branch_clock]
      simp only [List.length_replicate] at hFC
      have hw : 1≤(1+counter.length)^2 := by
        have hp : 1+counter.length≤(1+counter.length)^2 := Nat.le_pow (by decide)
        omega
      nlinarith only [hDC,hFC,hw,Nat.zero_le ((1+(encode a).length)^2)]
    refine ⟨((2*counter.length+2)+1)+finishTicks,hfull,?_,?_⟩
    · simpa only [trajectoryCharge_zero,Nat.zero_add,Nat.mul_one] using hc
    · exact (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock _ _ _).trans (by simpa only [trajectoryCharge_zero,Nat.zero_add,Nat.mul_one] using hc)
  | succ n ih =>
    have hp : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue counter := by omega
    obtain ⟨decTicks,next,hlen,hval,hD,hDC⟩ :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.decrement_positive M counter
        [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] [] v hp
    have hnext : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue next=n := by omega
    have hB :=
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.branch_positive M v
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store next [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] [])
    obtain ⟨applyTicks,hA,hAC,hAM⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.apply_call M next (encode a) (encode (step a)) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.putCounter v (true,none))
      (tf a) (sf a) hhead (h a)
    obtain ⟨iterTicks,hI,hIC,hIM⟩ :=
        ih next (step a) ((encode (step a)).head?,(true,none),none) hnext rfl
    have hDB : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) (decTicks+1)
        ⟨some (.counter .borrow),v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩=
        some ⟨some (.machine (.simulate 0)),Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.putCounter v (true,none),
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store next [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩ := by
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add,hD,Option.bind_some]
      simpa only [Fin.default_eq_zero] using hB
    have hDBA : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) ((decTicks+1)+applyTicks)
        ⟨some (.counter .borrow),v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩=
        some ⟨some (.counter .borrow),((encode (step a)).head?,(true,none),none),
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store next [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode (step a)).tail.map some)) [] []⟩ := by
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add,hDB,Option.bind_some,hA]
      rfl
    refine ⟨((decTicks+1)+applyTicks)+iterTicks,?_,?_,?_⟩
    · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add,hDBA,Option.bind_some]
      simpa only [Function.iterate_succ_apply] using hI
    · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ _ _ _ hDBA,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ _ _ _ hDB,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ 1 _ _ hD,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.branch_clock]
      rw [hlen] at hIC
      rw [trajectoryCharge_succ]
      have hw : 1≤(1+counter.length)^2 := by
        have hp : 1+counter.length≤(1+counter.length)^2 := Nat.le_pow (by decide)
        omega
      have hsquare : (trajectoryCharge encode step tf n (step a))^2+(1+(encode a).length+(encode (step a)).length+tf a)^2≤
          (trajectoryCharge encode step tf n (step a)+(1+(encode a).length+(encode (step a)).length+tf a))^2 := by
        nlinarith only [Nat.zero_le (trajectoryCharge encode step tf n (step a)*(1+(encode a).length+(encode (step a)).length+tf a))]
      nlinarith only [hDC,hAC,hIC,hsquare,hw]
    · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_add _ _ _ _ _ hDBA,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_add _ _ _ _ _ hDB,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_add _ _ 1 _ _ hD]
      rw [hlen] at hIM
      have hDM := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) decTicks
        ⟨some (.counter .borrow),v,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store counter [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩
      have hBM := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) 1
        ⟨some .branch,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.putCounter v (true,none),Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store next [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation.pack ((encode a).tail.map some)) [] []⟩
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.branch_clock] at hBM
      have hw : 1≤(1+counter.length)^2 := by
        have hp : 1+counter.length≤(1+counter.length)^2 := Nat.le_pow (by decide)
        omega
      have hbudget : 20*(1+counter.length)^2≤
          20*(n+1+1)*(1+counter.length)^2+20000*(trajectoryCharge encode step sf (n+1) a)^2 := by
        nlinarith only [Nat.zero_le (n*(1+counter.length)^2),Nat.zero_le ((trajectoryCharge encode step sf (n+1) a)^2)]
      have hpa :
          1+(encode a).length+(encode (step a)).length+sf a≤trajectoryCharge encode step sf
          (n+1) a := by rw [trajectoryCharge_succ]; omega
      have hpi :
          trajectoryCharge encode step sf n (step a)≤trajectoryCharge encode step sf (n+1) a := by
            rw [trajectoryCharge_succ]; omega
      have hsqa := Nat.mul_le_mul hpa hpa
      have hsqi := Nat.mul_le_mul hpi hpi
      apply max_le (max_le (max_le (by omega) (by omega)) ?_) ?_
      · nlinarith only [hAM,hsqa,Nat.zero_le ((n+1+1)*(1+counter.length)^2)]
      · nlinarith only [hIM,hsqi,Nat.zero_le ((1+counter.length)^2)]

/-- Aggregates the framed iteration input length, iteration count, final encoding length,
trajectory costs, and intermediate encoding lengths, plus one. -/
def budgetBase {α : Type} (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α)
    (cost : α → ℕ) (n : ℕ) (a : α) : ℕ :=
  1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length + n + (encode ((step^[n]) a)).length +
    trajectorySum step cost n a + trajectorySum step (fun x => (encode x).length) n a

/-- The trajectory charge is bounded by twice the sum of iteration count, final encoding length,
trajectory costs, intermediate encoding lengths, and one. -/
private theorem charge_bound {α : Type} (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α)
    (cost : α → ℕ) (n : ℕ) (a : α) :
    trajectoryCharge encode step cost n a ≤
      2 * (1 + n + (encode ((step^[n]) a)).length + trajectorySum step cost n a +
        trajectorySum step (fun x => (encode x).length) n a) := by
  have htel : trajectoryCharge encode step cost n a + (encode a).length =
      1 + 2 * (encode ((step^[n]) a)).length + n +
        2 * trajectorySum step (fun x => (encode x).length) n a +
        trajectorySum step cost n a := by
    induction n generalizing a with
    | zero => simp [trajectoryCharge_zero, trajectorySum]; omega
    | succ n ih =>
      rw [trajectoryCharge_succ, trajectorySum_succ_left, trajectorySum_succ_left,
        Function.iterate_succ_apply]
      have hi := ih (step a)
      omega
  omega

/-- The input, counter, trajectory, and final-step charges are bounded by `100000` times the
square of `budgetBase`. -/
private theorem resource_bound {α : Type} (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α)
    (cost : α → ℕ) (n : ℕ) (a : α) :
    200 * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length) ^ 2 +
        20 * (n + 1) * (1 + n.bits.length) ^ 2 +
        20000 * (trajectoryCharge encode step cost n a) ^ 2 + 1 ≤
      100000 * (budgetBase encode step cost n a) ^ 2 := by
  have hc := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.counter_budget n
  have hcharge := charge_bound encode step cost n a
  have hR : 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length ≤ budgetBase encode step cost n a := by
    dsimp [budgetBase]; omega
  have hN : 1 + n ≤ budgetBase encode step cost n a := by dsimp [budgetBase]; omega
  have hC : trajectoryCharge encode step cost n a ≤ 2 * budgetBase encode step cost n a := by
    dsimp [budgetBase]; omega
  have hR2 := Nat.mul_le_mul hR hR
  have hN2 := Nat.mul_le_mul hN hN
  have hC2 := Nat.mul_le_mul hC hC
  have hB : 1 ≤ (budgetBase encode step cost n a) ^ 2 := by
    have hb : budgetBase encode step cost n a ≤ (budgetBase encode step cost n a) ^ 2 :=
      Nat.le_pow (by decide)
    omega
  nlinarith only [hc, hR2, hN2, hC2, hB]

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput in
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore in

/-- The complete loop-input program halts with the reversed encoded iterate on its output stack
and blank remaining stacks, with separate quadratic total and maximum clock bounds. -/
private theorem input_complete {α : Type} {q : ℕ}
    (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1)))
    (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α) (tf sf : α → ℕ)
    (h : ∀ a, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (encode a) (encode (step a)) (tf a) (sf a)) (n : ℕ) (a : α) :
    ∃ ticks,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) ticks
        (TM2.init Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Slot.output (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).reverse) =
        some ⟨none, (none, (false, none), none), Function.update (fun _ => [])
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Slot.output (encode ((step^[n]) a)).reverse⟩ ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) ticks
        (TM2.init Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Slot.output (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).reverse) ≤
        100000 * (budgetBase encode step tf n a) ^ 2 ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunMaxClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) ticks
        (TM2.init Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Slot.output (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).reverse) ≤
        100000 * (budgetBase encode step sf n a) ^ 2 := by
  obtain ⟨prefixTicks, hP, hPC⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.frontend M n (encode a) default
  let v : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Local :=
      ((encode a).head?,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.getCounter default, none)
  obtain ⟨loopTicks, hL, hLC, hLM⟩ := core_complete M encode step tf sf h n n.bits a v
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits n) rfl
  obtain ⟨hN, hNC⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.execution id Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.Label.loop .done id (fun _ v => v) id
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) (fun _ => rfl) v loopTicks _ _ hL
  have hNM := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.max_clock id Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.Label.loop .done id (fun _ v => v) id
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.program M) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) (fun _ => rfl) v loopTicks _ _ hL
  simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq] at hN hNC hNM
  rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.init_eq]
  have hPN : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) (prefixTicks + loopTicks)
      ⟨some (.reader 0), default,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).reverse []⟩ =
      some ⟨some .done, (none, (false, none), none),
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (encode ((step^[n]) a)).reverse []⟩ := by
    rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add, hP, Option.bind_some]
    exact hN
  have hdone : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) 1
      ⟨some .done, (none, (false, none), none),
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (encode ((step^[n]) a)).reverse []⟩ = 1 := rfl
  refine ⟨(prefixTicks + loopTicks) + 1, ?_, ?_, ?_⟩
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add, hPN, Option.bind_some, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_one]
    rw [← Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.output_store]
    rfl
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ 1 _ _ hPN, hdone, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add _ _ _ _ _ hP, hNC]
    exact (Nat.add_le_add_right (Nat.add_le_add hPC hLC) 1).trans
      (by simpa only [Nat.add_assoc] using resource_bound encode step tf n a)
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_add _ _ 1 _ _ hPN, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_add _ _ _ _ _ hP, hNM]
    have hd : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunMaxClock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) 1
        ⟨some .done, (none, (false, none), none),
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (encode ((step^[n]) a)).reverse []⟩ = 1 := rfl
    rw [hd]
    have hPM := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.maxClock_le_clock (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M) prefixTicks
      ⟨some (.reader 0), default,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.store [] [] [] [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).reverse []⟩
    have hb := resource_bound encode step sf n a
    omega

/-- A machine realizing one encoded state transition yields one uniform binary machine for every
iterate, with quadratic time and space bounds in the respective `budgetBase`. -/
theorem uniform_iterates {α : Type} {q : ℕ}
    (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1)))
    (encode : α → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (step : α → α) (tf sf : α → ℕ)
    (h : ∀ a, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (encode a) (encode (step a)) (tf a) (sf a)) :
    ∃ (r : ℕ) (N : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (r + 1))) (C : ℕ), 0 < C ∧
      ∀ n a, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs N (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)) (encode ((step^[n]) a))
        (C * (budgetBase encode step tf n a) ^ 2)
        (C * (budgetBase encode step sf n a) ^ 2) := by
  obtain ⟨r, N, C, hC, hN⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler_separate (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopInput.program M)
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Slot.output Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore.Slot.output
  refine ⟨r, N, 100002 * C, Nat.mul_pos (by decide) hC, ?_⟩
  intro n a
  obtain ⟨ticks, hr, ht, hs⟩ := input_complete M encode step tf sf h n a
  have hRuns := hN (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)) (encode ((step^[n]) a)) ticks
    (none, (false, none), none) hr
  have bound (cost : α → ℕ) :
      (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length) ^ 2 +
          100000 * (budgetBase encode step cost n a) ^ 2 +
          (1 + (encode ((step^[n]) a)).length) ^ 2 ≤
        100002 * (budgetBase encode step cost n a) ^ 2 := by
    have hi : 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length ≤ budgetBase encode step cost n a := by
      dsimp [budgetBase]; omega
    have ho : 1 + (encode ((step^[n]) a)).length ≤ budgetBase encode step cost n a := by
      dsimp [budgetBase]; omega
    nlinarith only [Nat.mul_le_mul hi hi, Nat.mul_le_mul ho ho]
  apply Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hRuns
  · calc
      _ ≤ C * ((1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length) ^ 2 +
          100000 * (budgetBase encode step tf n a) ^ 2 +
          (1 + (encode ((step^[n]) a)).length) ^ 2) := Nat.mul_le_mul_left C (by omega)
      _ ≤ C * (100002 * (budgetBase encode step tf n a) ^ 2) :=
        Nat.mul_le_mul_left C (bound tf)
      _ = _ := by ring
  · calc
      _ ≤ C * ((1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed (encode a)).length) ^ 2 +
          100000 * (budgetBase encode step sf n a) ^ 2 +
          (1 + (encode ((step^[n]) a)).length) ^ 2) := Nat.mul_le_mul_left C (by omega)
      _ ≤ C * (100002 * (budgetBase encode step sf n a) ^ 2) :=
        Nat.mul_le_mul_left C (bound sf)
      _ = _ := by ring

end Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.CanonicalIteration
