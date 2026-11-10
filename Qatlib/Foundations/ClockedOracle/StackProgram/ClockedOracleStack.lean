/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.Linarith
import Qatlib.Foundations.ClockedOracle.StackProgram.ClockedOracleStackDefs

set_option autoImplicit false
namespace Qatlib.Foundations.ClockedOracle.StackProgram

theorem run_add (P : List Instr) (O : ℕ → List Bool → Bool)
    (a b : ℕ) (s : State) :
    run P O (a + b) s = run P O b (run P O a s) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (step P O s)

theorem run_succ_last (P : List Instr) (O : ℕ → List Bool → Bool)
    (k : ℕ) (s : State) : run P O (k + 1) s = step P O (run P O k s) := by
  simpa only [run] using run_add P O k 1 s

theorem run_halted (P : List Instr) (O : ℕ → List Bool → Bool)
    (k : ℕ) (s : State) (h : s.halted = true) : run P O k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [run, step, h] using ih

private def scanState (xs : List Bool) (m t c : ℕ) : State :=
  { input := xs, output := List.replicate m true, ticks := t, cost := c }

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

theorem log_subset_step (P : List Instr) (O : ℕ → List Bool → Bool) (s : State) :
    ∀ p ∈ s.log, p ∈ (step P O s).log := by
  intro p hp
  unfold step
  split
  · exact hp
  · cases h : P[s.pc]? with
    | none => exact hp
    | some i => cases i <;> simp_all

theorem log_subset_run (P : List Instr) (O : ℕ → List Bool → Bool)
    (k : ℕ) (s : State) : ∀ p ∈ s.log, p ∈ (run P O k s).log := by
  induction k generalizing s with
  | zero => exact fun _ h => h
  | succ k ih =>
    intro p hp
    exact ih (step P O s) p (log_subset_step P O s p hp)

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
