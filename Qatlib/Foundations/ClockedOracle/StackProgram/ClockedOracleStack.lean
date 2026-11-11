/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.Linarith
import Qatlib.Foundations.ClockedOracle.StackProgram.ClockedOracleStackDefs

/-!
# Execution and cost bounds for oracle stack programs

Proves fuel composition, halted-state stability, and equality of runs when two oracles agree on
the logged queries. `g1` gives the exact behavior of `scanProgram`, while `g2` bounds state
sizes and total cost by the available fuel.

The model makes query addresses and execution work explicit in an oracle-computation setting;
see [KitaevShenVyalyi2002] for computational background.

## Main statements

* `g1`: The scan program halts without error after `3n + 2` ticks and cost, consumes all `n`
  input bits, emits `n` true bits, and makes no oracle queries.
* `g2`: After `k` units of fuel from initialization, cost equals ticks plus logged address work;
  ticks, log, output, and address lengths satisfy the stated fuel bounds, input length does not
  increase, and cost is at most `k * (k + 1)`.
* `run_eq_of_trace`: Runs from the same state agree when the two oracles agree on all queries
  logged by the first run.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.ClockedOracle.StackProgram

/-- Running for `a + b` units of fuel equals running first for `a` and then for `b` from the
resulting state. -/
theorem run_add (P : List Instr) (O : ℕ → List Bool → Bool)
    (a b : ℕ) (s : State) :
    run P O (a + b) s = run P O b (run P O a s) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (step P O s)

/-- A run with one additional unit of fuel is one step after the shorter run. -/
theorem run_succ_last (P : List Instr) (O : ℕ → List Bool → Bool)
    (k : ℕ) (s : State) : run P O (k + 1) s = step P O (run P O k s) := by
  simpa only [run] using run_add P O k 1 s

/-- Running from a halted state leaves that state unchanged for any fuel. -/
theorem run_halted (P : List Instr) (O : ℕ → List Bool → Bool)
    (k : ℕ) (s : State) (h : s.halted = true) : run P O k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [run, step, h] using ih

/-- A scan configuration with input `xs`, `m` true output bits, and prescribed tick and cost
counters. -/
private def scanState (xs : List Bool) (m t c : ℕ) : State :=
  { input := xs, output := List.replicate m true, ticks := t, cost := c }

/-- Scanning `xs` for `3 * xs.length + 2` units of fuel consumes the input, halts at instruction
three, adds one true output bit per input bit, and increments both counters by that fuel
amount. -/
private theorem run_scan (xs : List Bool) (O : ℕ → List Bool → Bool) (m t c : ℕ) :
    run scanProgram O (3 * xs.length + 2) (scanState xs m t c) =
      { pc := 3, output := List.replicate (m + xs.length) true, halted := true,
        ticks := t + 3 * xs.length + 2, cost := c + 3 * xs.length + 2 } := by
  induction xs generalizing m t c with
  | nil => simp [scanState, scanProgram, run, step]
  | cons b xs ih =>
    have hf : 3 * (b :: xs).length + 2 = 3 + (3 * xs.length + 2) := by simp; omega
    rw [hf, run_add]
    have hs : run scanProgram O 3 (scanState (b :: xs) m t c) =
        scanState xs (m + 1) (t + 3) (c + 3) := by
      cases b <;> simp [scanState, scanProgram, run, step, List.replicate_succ,
        Nat.add_assoc]
    rw [hs, ih]
    simp [List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The scan program halts without error after `3n + 2` ticks and cost, consumes all `n` input
bits, emits `n` true bits, and makes no oracle queries. -/
theorem g1 :
    ∀ (xs : List Bool) (O : ℕ → List Bool → Bool),
      let s := run scanProgram O (3 * xs.length + 2) (init xs)
      s.halted = true ∧ s.error = false ∧ s.input = [] ∧
      s.output = List.replicate xs.length true ∧
      s.ticks = 3 * xs.length + 2 ∧ s.cost = 3 * xs.length + 2 ∧ s.log = [] := by
  intro xs O
  have h : run scanProgram O (3 * xs.length + 2) (init xs) =
      { pc := 3, output := List.replicate xs.length true, halted := true,
        ticks := 3 * xs.length + 2, cost := 3 * xs.length + 2 } := by
    simpa [scanState, init] using run_scan xs O 0 0 0
  dsimp only
  rw [h]
  simp

/-- One step preserves the cost identity and the stated log, input, output, address, and
quadratic cost bounds with the fuel bound increased by one. -/
private theorem step_bounds (P : List Instr) (O : ℕ → List Bool → Bool)
    (n k : ℕ) (s : State)
    (h : s.cost = s.ticks + addressWork s ∧ s.log.length ≤ s.ticks ∧ s.ticks ≤ k ∧
      s.input.length ≤ n ∧ s.output.length ≤ k ∧ s.address.length ≤ k ∧
      s.cost ≤ k * (k + 1)) :
    let r := step P O s
    r.cost = r.ticks + addressWork r ∧ r.log.length ≤ r.ticks ∧ r.ticks ≤ k + 1 ∧
      r.input.length ≤ n ∧ r.output.length ≤ k + 1 ∧ r.address.length ≤ k + 1 ∧
      r.cost ≤ (k + 1) * (k + 1 + 1) := by
  rcases h with ⟨hc, hl, ht, hi, ho, ha, hb⟩
  have hnext : s.cost + 1 + s.address.length ≤ (k + 1) * (k + 1 + 1) := by
    nlinarith
  dsimp only
  unfold step
  split
  · exact ⟨hc, hl, by omega, hi, by omega, by omega, by nlinarith⟩
  · cases hp : P[s.pc]? with
    | none => simp_all [addressWork]; omega
    | some i =>
      cases i <;> simp_all [addressWork, List.length_tail] <;> omega

/-- After `k` units of fuel from initialization, cost equals ticks plus logged address work;
ticks, log, output, and address lengths satisfy the stated fuel bounds, input length does
not increase, and cost is at most `k * (k + 1)`. -/
theorem g2 :
    ∀ (P : List Instr) (O : ℕ → List Bool → Bool) (xs : List Bool) (k : ℕ),
      let s := run P O k (init xs)
      s.cost = s.ticks + addressWork s ∧ s.log.length ≤ s.ticks ∧ s.ticks ≤ k ∧
      s.input.length ≤ xs.length ∧ s.output.length ≤ k ∧ s.address.length ≤ k ∧
      s.cost ≤ k * (k + 1) := by
  intro P O xs k
  induction k with
  | zero => simp [run, init, addressWork]
  | succ k ih =>
    rw [run_succ_last]
    exact step_bounds P O xs.length k _ ih

/-- Every existing query-log entry remains in the log after one step. -/
theorem log_subset_step (P : List Instr) (O : ℕ → List Bool → Bool) (s : State) :
    ∀ p ∈ s.log, p ∈ (step P O s).log := by
  intro p hp
  unfold step
  split
  · exact hp
  · cases h : P[s.pc]? with
    | none => exact hp
    | some i => cases i <;> simp_all

/-- Every initial query-log entry remains in the log after a run. -/
theorem log_subset_run (P : List Instr) (O : ℕ → List Bool → Bool)
    (k : ℕ) (s : State) : ∀ p ∈ s.log, p ∈ (run P O k s).log := by
  induction k generalizing s with
  | zero => exact fun _ h => h
  | succ k ih =>
    intro p hp
    exact ih (step P O s) p (log_subset_step P O s p hp)

/-- One-step states agree for two oracles that agree on all entries in the first step's
resulting query log. -/
private theorem step_eq_of_trace (P : List Instr) (O Q : ℕ → List Bool → Bool)
    (s : State) (h : ∀ p ∈ (step P O s).log, O p.1 p.2 = Q p.1 p.2) :
    step P O s = step P Q s := by
  cases hh : s.halted with
  | true => simp [step, hh]
  | false =>
    cases hp : P[s.pc]? with
    | none => simp [step, hh, hp]
    | some i =>
      cases i with
      | query slot f r =>
        have he : O slot s.address = Q slot s.address :=
          h (slot, s.address) (by simp [step, hh, hp])
        simp [step, hh, hp, he]
      | peek e f r => simp [step, hh, hp]
      | pop next => simp [step, hh, hp]
      | emit b next => simp [step, hh, hp]
      | address b next => simp [step, hh, hp]
      | halt => simp [step, hh, hp]

/-- Runs from the same state agree when the two oracles agree on all queries logged by the first
run. -/
theorem run_eq_of_trace (P : List Instr) (O Q : ℕ → List Bool → Bool)
    (k : ℕ) (s : State)
    (h : ∀ p ∈ (run P O k s).log, O p.1 p.2 = Q p.1 p.2) :
    run P O k s = run P Q k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have hs : step P O s = step P Q s := step_eq_of_trace P O Q s
      (fun p hp => h p (log_subset_run P O k (step P O s) p hp))
    calc
      run P O (k + 1) s = run P Q k (step P O s) := ih (step P O s) h
      _ = run P Q (k + 1) s := by rw [hs]; rfl

/-- Packages fuel composition, stability of halted states, and equality of initialized runs for
oracles agreeing on the logged queries. -/
theorem g3 :
    (∀ (P : List Instr) (O : ℕ → List Bool → Bool) (a b : ℕ) (s : State),
      run P O (a + b) s = run P O b (run P O a s)) ∧
    (∀ (P : List Instr) (O : ℕ → List Bool → Bool) (k : ℕ) (s : State),
      s.halted = true → run P O k s = s) ∧
    (∀ (P : List Instr) (O Q : ℕ → List Bool → Bool) (xs : List Bool) (k : ℕ),
      (∀ p ∈ (run P O k (init xs)).log, O p.1 p.2 = Q p.1 p.2) →
      run P O k (init xs) = run P Q k (init xs)) :=
  ⟨run_add, run_halted, fun P O Q xs k => run_eq_of_trace P O Q k (init xs)⟩

end Qatlib.Foundations.ClockedOracle.StackProgram
