/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridExecutionDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybrid
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace NativeTape

variable {Γ Λ : Type} [Inhabited Γ]

theorem Result.bits_prepend_none (r : Result Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (Result.prepend (cfg, none) r).bits = r.bits := by
  show ((cfg, none) :: r.trace).filterMap Prod.snd = r.trace.filterMap Prod.snd
  simp

theorem Result.bits_prepend_some (r : Result Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (b : Bool) :
    (Result.prepend (cfg, some b) r).bits = b :: r.bits := by
  show ((cfg, some b) :: r.trace).filterMap Prod.snd = b :: r.trace.filterMap Prod.snd
  simp

theorem Result.unread_prepend (r : Result Γ Λ) (e : Tick Γ Λ) :
    (Result.prepend e r).unread = r.unread := rfl

theorem Result.steps_prepend (r : Result Γ Λ) (e : Tick Γ Λ) :
    (Result.prepend e r).steps = r.steps + 1 := by
  show (e :: r.trace).length = r.trace.length + 1
  simp

theorem run_bits_partition (M : Program Γ Λ) :
    ∀ (n : ℕ) (bits : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      (run M n bits cfg).bits ++ (run M n bits cfg).unread = bits := by
  intro n
  induction n with
  | zero =>
    intro bits cfg
    cases h : M cfg.q cfg.Tape.head <;> simp [run, h, Result.bits]
  | succ n ih =>
    intro bits cfg
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h, Result.bits]
    | det q' s =>
      simp only [run, h]
      rw [Result.bits_prepend_none, Result.unread_prepend]
      exact ih bits (advance cfg (q', s))
    | coin k =>
      cases bits with
      | nil => simp [run, h, Result.bits]
      | cons b bs =>
        simp only [run, h]
        rw [Result.bits_prepend_some, Result.unread_prepend]
        simp only [List.cons_append]
        rw [ih bs (advance cfg (k b))]

theorem run_steps_le_budget (M : Program Γ Λ) :
    ∀ (n : ℕ) (bits : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      (run M n bits cfg).steps ≤ n := by
  intro n
  induction n with
  | zero =>
    intro bits cfg
    cases h : M cfg.q cfg.Tape.head <;> simp [run, h, Result.steps]
  | succ n ih =>
    intro bits cfg
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h, Result.steps]
    | det q' s =>
      simp only [run, h]
      rw [Result.steps_prepend]
      exact Nat.succ_le_succ (ih bits (advance cfg (q', s)))
    | coin k =>
      cases bits with
      | nil => simp [run, h, Result.steps]
      | cons b bs =>
        simp only [run, h]
        rw [Result.steps_prepend]
        exact Nat.succ_le_succ (ih bs (advance cfg (k b)))

theorem Result.bits_append (r s : Result Γ Λ) :
    (Result.appendTrace r.trace s).bits = r.bits ++ s.bits := by
  show (r.trace ++ s.trace).filterMap Prod.snd =
    r.trace.filterMap Prod.snd ++ s.trace.filterMap Prod.snd
  rw [List.filterMap_append]

theorem Result.unread_of_append (r s : Result Γ Λ) :
    (Result.appendTrace r.trace s).unread = s.unread := rfl

theorem Result.steps_append (r s : Result Γ Λ) :
    (Result.appendTrace r.trace s).steps = r.steps + s.steps := by
  show (r.trace ++ s.trace).length = r.trace.length + s.trace.length
  rw [List.length_append]

theorem resume_bits_partition (M : Program Γ Λ) (extra : ℕ) (r : Result Γ Λ)
    (h : r.stop = .fuel) :
    (resume M extra r).bits ++ (resume M extra r).unread = r.bits ++ r.unread := by
  have hs := run_bits_partition M extra r.unread r.cfg
  simp only [resume, if_pos h]
  show (Result.appendTrace r.trace (run M extra r.unread r.cfg)).bits ++
      (Result.appendTrace r.trace (run M extra r.unread r.cfg)).unread = r.bits ++ r.unread
  rw [Result.bits_append, Result.unread_of_append, List.append_assoc, hs]

theorem resume_steps (M : Program Γ Λ) (extra : ℕ) (r : Result Γ Λ)
    (h : r.stop = .fuel) :
    (resume M extra r).steps = r.steps + (run M extra r.unread r.cfg).steps := by
  simp only [resume, if_pos h]
  show (Result.appendTrace r.trace (run M extra r.unread r.cfg)).steps =
      r.steps + (run M extra r.unread r.cfg).steps
  rw [Result.steps_append]

end NativeTape

namespace NativeHybrid

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable {D : ℕ} {A : Type}

theorem Record.run_of_halted {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (h : c.native.stop = NativeTape.Stop.halted) :
    (Record.run c O p).quantum = some (p.record O) ∧
    (Record.run c O p).native = c.native := by
  simp [Record.run, h]

theorem Record.run_of_suspended {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (h : c.native.stop ≠ NativeTape.Stop.halted) :
    (Record.run c O p).quantum = none ∧
    (Record.run c O p).native = c.native := by
  simp [Record.run, h]

theorem Record.suspended_keeps_native {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (h : c.native.stop ≠ NativeTape.Stop.halted) :
    (Record.run c O p).native.cfg = c.native.cfg ∧
    (Record.run c O p).native.unread = c.native.unread ∧
    (Record.run c O p).ledger.nativeSteps = c.native.steps ∧
    (Record.run c O p).ledger.nativeBits = c.native.bits.length ∧
    (Record.run c O p).ledger.quantum = HybridCounts.zero := by
  simp [Record.run, h, Record.ledger]

theorem Record.action_of_halted {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    {ρ : Operator D} (h : c.native.stop = NativeTape.Stop.halted) :
    (Record.run c O p).action ρ = (p.record O).operator * ρ := by
  simp [Record.run, h, Record.action, nativeAction]

theorem Record.action_of_suspended {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    {ρ : Operator D} (h : c.native.stop ≠ NativeTape.Stop.halted) :
    (Record.run c O p).action ρ = 0 := by
  simp [Record.run, h, Record.action]

omit [Inhabited Λ] in

theorem Record.action_state_independent {rec : Record Γ Λ D A} :
    ∃ A : Operator D, ∀ ρ : Operator D, rec.action ρ = A * ρ := by
  cases hq : rec.quantum with
  | none =>
    refine ⟨0, ?_⟩
    intro ρ
    simp [Record.action, hq]
  | some t =>
    refine ⟨t.operator, ?_⟩
    intro ρ
    simp [Record.action, hq, nativeAction]

theorem Record.run_branch_of_halted {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (h : c.native.stop = NativeTape.Stop.halted) (ρ : Operator D) :
    (Record.run c O p).branch ρ =
      ((CoinCode.wordWeight (p.record O).coins : ℝ) : ℂ) • conjBranch (p.record O).operator ρ := by
  simp [Record.run, h, Record.branch]

theorem Record.run_bornMass_of_halted {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (h : c.native.stop = NativeTape.Stop.halted) (ρ : Operator D) :
    (Record.run c O p).bornMass ρ =
      CoinCode.wordWeight (p.record O).coins *
        (Matrix.trace (conjBranch (p.record O).operator ρ)).re := by
  rw [Record.bornMass]
  simp [Record.run, h, Record.branch, Matrix.trace_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem Record.run_branch_eq_instrument {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hp : (c.next NativeTape.Stop.halted).Legal)
    (h : c.native.stop = NativeTape.Stop.halted) (ρ : Operator D) :
    ∃ i : Fin (c.next NativeTape.Stop.halted).leafCount,
      (Record.run c O p).branch ρ = ((c.next NativeTape.Stop.halted).instrument O hO hp).branch i ρ := by
  obtain ⟨i, hi⟩ := p.record_index O
  refine ⟨i, ?_⟩
  rw [Record.run_branch_of_halted h ρ, HybridProgram.branch_law _ O hO hp ρ i, hi]

theorem Record.run_bornMass_eq_instrumentProb {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hp : (c.next NativeTape.Stop.halted).Legal)
    (h : c.native.stop = NativeTape.Stop.halted) (ρ : Operator D) :
    ∃ i : Fin (c.next NativeTape.Stop.halted).leafCount,
      (Record.run c O p).bornMass ρ =
        instrumentProb ((c.next NativeTape.Stop.halted).instrument O hO hp) ρ i := by
  obtain ⟨i, hi⟩ := p.record_index O
  refine ⟨i, ?_⟩
  rw [Record.run_bornMass_of_halted h ρ, HybridProgram.probability_law _ O hO hp ρ i, hi]

theorem Record.run_bornMass_eq_instrumentProb_of {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hp : (c.next NativeTape.Stop.halted).Legal)
    (h : c.native.stop = NativeTape.Stop.halted) (ρ : Operator D)
    (i : Fin (c.next NativeTape.Stop.halted).leafCount)
    (hidx : (c.next NativeTape.Stop.halted).leaf O i = p.record O) :
    (Record.run c O p).bornMass ρ =
      instrumentProb ((c.next NativeTape.Stop.halted).instrument O hO hp) ρ i := by
  rw [Record.run_bornMass_of_halted h ρ, ← hidx]
  exact (HybridProgram.probability_law _ O hO hp ρ i).symm

theorem Record.zero_mass_branch_retained {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hp : (c.next NativeTape.Stop.halted).Legal)
    (h : c.native.stop = NativeTape.Stop.halted) (ρ : Operator D)
    (i : Fin (c.next NativeTape.Stop.halted).leafCount)
    (hidx : (c.next NativeTape.Stop.halted).leaf O i = p.record O)
    (hmass : instrumentProb ((c.next NativeTape.Stop.halted).instrument O hO hp) ρ i = 0) :
    (Record.run c O p).quantum ≠ none ∧ (Record.run c O p).bornMass ρ = 0 := by
  refine ⟨?_, ?_⟩
  · simp [Record.run, h]
  · rw [Record.run_bornMass_eq_instrumentProb_of hO hp h ρ i hidx, hmass]

theorem Record.ledger_quantum_of_halted {c : Call Γ Λ D A} {O : Operator D}
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)}
    (h : c.native.stop = NativeTape.Stop.halted) :
    (Record.run c O p).ledger.quantum = (p.record O).counts := by
  simp [Record.run, h, Record.ledger]

theorem Record.resume_bits_partition {c : Call Γ Λ D A} (extra : ℕ)
    (h : c.native.stop = NativeTape.Stop.fuel) :
    (NativeTape.resume c.program extra c.native).bits ++
      (NativeTape.resume c.program extra c.native).unread = c.bits := by
  rw [NativeTape.resume_bits_partition c.program extra c.native h]
  have hr := NativeTape.run_bits_partition c.program c.budget c.bits c.config
  simpa [Call.native] using hr

theorem Record.resume_steps {c : Call Γ Λ D A} (extra : ℕ)
    (h : c.native.stop = NativeTape.Stop.fuel) :
    (NativeTape.resume c.program extra c.native).steps =
      c.native.steps + (NativeTape.run c.program extra c.native.unread c.native.cfg).steps := by
  exact NativeTape.resume_steps c.program extra c.native h

theorem Record.resume_quantum {c : Call Γ Λ D A} {O : Operator D} (extra : ℕ)
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)} :
    (Record.resume c O extra p).quantum =
      if (NativeTape.resume c.program extra c.native).stop = NativeTape.Stop.halted
      then some (p.record O) else none := by
  by_cases h : (NativeTape.resume c.program extra c.native).stop = NativeTape.Stop.halted
  · have hr : (Record.resume c O extra p) =
        ⟨NativeTape.resume c.program extra c.native, some (p.record O)⟩ := by
      simp [Record.resume, h]
    rw [hr]
    simp [h]
  · have hr : (Record.resume c O extra p) =
        ⟨NativeTape.resume c.program extra c.native, none⟩ := by
      simp [Record.resume, h]
    rw [hr]
    simp [h]

theorem Record.resume_native {c : Call Γ Λ D A} {O : Operator D} (extra : ℕ)
    {p : HybridProgram.Path (c.next NativeTape.Stop.halted)} :
    (Record.resume c O extra p).native = NativeTape.resume c.program extra c.native := by
  by_cases h : (NativeTape.resume c.program extra c.native).stop = NativeTape.Stop.halted
  · have hr : (Record.resume c O extra p) =
        ⟨NativeTape.resume c.program extra c.native, some (p.record O)⟩ := by
      simp [Record.resume, h]
    rw [hr]
  · have hr : (Record.resume c O extra p) =
        ⟨NativeTape.resume c.program extra c.native, none⟩ := by
      simp [Record.resume, h]
    rw [hr]

end NativeHybrid

theorem stageA_execution_clause16 {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {D : ℕ} {A : Type} (c : NativeHybrid.Call Γ Λ D A) (O : Operator D)
    (p : HybridProgram.Path (c.next NativeTape.Stop.halted)) (ρ : Operator D) :
    (c.native.bits ++ c.native.unread = c.bits) ∧
    (c.native.steps ≤ c.budget) ∧
    (c.native.bits.length ≤ c.bits.length) ∧
    ((NativeHybrid.Record.run c O p).native = c.native) ∧
    ((NativeHybrid.Record.run c O p).quantum =
      if c.native.stop = NativeTape.Stop.halted then some (p.record O) else none) ∧
    ((NativeHybrid.Record.run c O p).ledger.nativeSteps = c.native.steps) ∧
    ((NativeHybrid.Record.run c O p).ledger.nativeBits = c.native.bits.length) ∧
    (c.native.stop = NativeTape.Stop.halted →
      (NativeHybrid.Record.run c O p).action ρ = (p.record O).operator * ρ) ∧
    (c.native.stop ≠ NativeTape.Stop.halted →
      (NativeHybrid.Record.run c O p).action ρ = 0) := by
  have hpart : c.native.bits ++ c.native.unread = c.bits :=
    NativeTape.run_bits_partition c.program c.budget c.bits c.config
  have hsteps : c.native.steps ≤ c.budget :=
    NativeTape.run_steps_le_budget c.program c.budget c.bits c.config
  have hlen : c.native.bits.length ≤ c.bits.length := by
    have h2 : c.bits.length = c.native.bits.length + c.native.unread.length := by
      rw [← hpart, List.length_append]
    rw [h2]
    exact Nat.le_add_right _ _
  by_cases hh : c.native.stop = NativeTape.Stop.halted
  · refine ⟨hpart, hsteps, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [NativeHybrid.Record.run, hh]
    · simp [NativeHybrid.Record.run, hh]
    · simp [NativeHybrid.Record.run, hh, NativeHybrid.Record.ledger]
    · simp [NativeHybrid.Record.run, hh, NativeHybrid.Record.ledger]
    · intro _
      simp [NativeHybrid.Record.run, hh, NativeHybrid.Record.action,
        NativeHybrid.nativeAction]
    · intro h
      exact (h hh).elim
  · refine ⟨hpart, hsteps, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [NativeHybrid.Record.run, hh]
    · simp [NativeHybrid.Record.run, hh]
    · simp [NativeHybrid.Record.run, hh, NativeHybrid.Record.ledger]
    · simp [NativeHybrid.Record.run, hh, NativeHybrid.Record.ledger]
    · intro h
      exact (hh h).elim
    · intro _
      simp [NativeHybrid.Record.run, hh, NativeHybrid.Record.action]

theorem stageA_execution_clause16_transport {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {D : ℕ} {A : Type} (c : NativeHybrid.Call Γ Λ D A) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hp : (c.next NativeTape.Stop.halted).Legal)
    (p : HybridProgram.Path (c.next NativeTape.Stop.halted)) (ρ : Operator D)
    (extra : ℕ) :
    (c.native.stop = NativeTape.Stop.halted →
      (∃ i : Fin (c.next NativeTape.Stop.halted).leafCount,
        (NativeHybrid.Record.run c O p).branch ρ =
          ((c.next NativeTape.Stop.halted).instrument O hO hp).branch i ρ) ∧
      (∃ j : Fin (c.next NativeTape.Stop.halted).leafCount,
        (NativeHybrid.Record.run c O p).bornMass ρ =
          instrumentProb ((c.next NativeTape.Stop.halted).instrument O hO hp) ρ j) ∧
      (NativeHybrid.Record.run c O p).ledger.quantum = (p.record O).counts) ∧
    (c.native.stop ≠ NativeTape.Stop.halted →
      (NativeHybrid.Record.run c O p).quantum = none ∧
      (NativeHybrid.Record.run c O p).ledger.quantum = HybridCounts.zero) ∧
    (c.native.stop = NativeTape.Stop.fuel →
      (NativeTape.resume c.program extra c.native).bits ++
        (NativeTape.resume c.program extra c.native).unread = c.bits ∧
      (NativeTape.resume c.program extra c.native).steps =
        c.native.steps +
          (NativeTape.run c.program extra c.native.unread c.native.cfg).steps) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := NativeHybrid.Record.run_branch_eq_instrument hO hp hh ρ
      exact ⟨i, hi⟩
    · obtain ⟨j, hj⟩ := NativeHybrid.Record.run_bornMass_eq_instrumentProb hO hp hh ρ
      exact ⟨j, hj⟩
    · exact NativeHybrid.Record.ledger_quantum_of_halted hh
  · intro hs
    refine ⟨(NativeHybrid.Record.run_of_suspended hs).1, ?_⟩
    simp [NativeHybrid.Record.run, hs, NativeHybrid.Record.ledger]
  · intro hf
    exact ⟨NativeHybrid.Record.resume_bits_partition extra hf,
      NativeHybrid.Record.resume_steps extra hf⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality
