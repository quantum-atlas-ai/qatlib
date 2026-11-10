/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def tapeDecisionRun (M : Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ℕ → Turing.TM0.Cfg Γ Λ → Option Bool
  | 0, cfg => if Turing.TM0.step M cfg = none then some (accept cfg.q) else none
  | t + 1, cfg =>
      match Turing.TM0.step M cfg with
      | none => some (accept cfg.q)
      | some cfg' => tapeDecisionRun M accept t cfg'

def tapeDecision (M : Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (input : List Γ) (t : ℕ) : Option Bool :=
  tapeDecisionRun M accept t (Turing.TM0.init input)

private theorem flip_bind_none {σ : Type*} (f : σ → Option σ) :
    (flip bind f) (none : Option σ) = none := rfl

private theorem iterate_flip_bind_none {σ : Type*} (f : σ → Option σ) (k : ℕ) :
    (flip bind f)^[k] none = none := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; exact flip_bind_none f

theorem bitMachineAfter_eq_iterate (M : Turing.TM0.Machine Γ Λ) (input : List Γ) (s : ℕ) :
    BitMachineAfter M input s =
      (flip bind (Turing.TM0.step M))^[s] (some (Turing.TM0.init input)) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

theorem tapeDecisionRun_eq_some_iff (M : Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (t : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (b : Bool) :
    tapeDecisionRun M accept t cfg = some b ↔
      ∃ (s : ℕ) (cfg' : Turing.TM0.Cfg Γ Λ),
        s ≤ t ∧ (flip bind (Turing.TM0.step M))^[s] (some cfg) = some cfg' ∧
          Turing.TM0.step M cfg' = none ∧ accept cfg'.q = b := by
  induction t generalizing cfg with
  | zero =>
    constructor
    · intro h
      simp only [tapeDecisionRun] at h
      by_cases hs : Turing.TM0.step M cfg = none
      · rw [if_pos hs] at h
        exact ⟨0, cfg, le_refl 0, rfl, hs, Option.some.inj h⟩
      · rw [if_neg hs] at h
        nomatch h
    · rintro ⟨s, cfg', hs_le, hiter, hhalt, hacc⟩
      obtain rfl : s = 0 := Nat.le_zero.mp hs_le
      simp only [Function.iterate_zero_apply] at hiter
      obtain rfl : cfg' = cfg := (Option.some.inj hiter).symm
      simp only [tapeDecisionRun, if_pos hhalt, hacc]
  | succ t ih =>
    constructor
    · intro h
      simp only [tapeDecisionRun] at h
      split at h
      · rename_i hs
        exact ⟨0, cfg, Nat.zero_le _, rfl, hs, Option.some.inj h⟩
      · rename_i cfg₁ hs
        rw [ih] at h
        obtain ⟨s, cfg', hs_le, hiter, hhalt, hacc⟩ := h
        refine ⟨s + 1, cfg', Nat.succ_le_succ hs_le, ?_, hhalt, hacc⟩
        rw [Function.iterate_succ_apply]
        have hstep : (flip bind (Turing.TM0.step M)) (some cfg) = some cfg₁ := hs
        rw [hstep]
        exact hiter
    · rintro ⟨s, cfg', hs_le, hiter, hhalt, hacc⟩
      simp only [tapeDecisionRun]
      split
      · rename_i hs
        cases s with
        | zero =>
          simp only [Function.iterate_zero_apply] at hiter
          obtain rfl : cfg' = cfg := (Option.some.inj hiter).symm
          exact congrArg some hacc
        | succ s =>
          exfalso
          rw [Function.iterate_succ_apply] at hiter
          have hstep : (flip bind (Turing.TM0.step M)) (some cfg) = none := hs
          rw [hstep, iterate_flip_bind_none] at hiter
          nomatch hiter
      · rename_i cfg₁ hs
        rw [ih]
        cases s with
        | zero =>
          exfalso
          simp only [Function.iterate_zero_apply] at hiter
          obtain rfl : cfg = cfg' := Option.some.inj hiter
          rw [hhalt] at hs
          nomatch hs
        | succ s =>
          refine ⟨s, cfg', Nat.succ_le_succ_iff.mp hs_le, ?_, hhalt, hacc⟩
          rw [Function.iterate_succ_apply] at hiter
          have hstep : (flip bind (Turing.TM0.step M)) (some cfg) = some cfg₁ := hs
          rw [hstep] at hiter
          exact hiter

theorem clocked_tape_decision_halt_and_timeout :
    ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ)
      (a : Λ → Bool) (input : List Γ) (t : ℕ) (b : Bool),
      tapeDecision M a input t = some b ↔
        ∃ (s : ℕ) (cfg : Turing.TM0.Cfg Γ Λ),
          s ≤ t ∧ BitMachineAfter M input s = some cfg ∧
            Turing.TM0.step M cfg = none ∧ a cfg.q = b := by
  intro Γ Λ _ _ M a input t b
  simp only [tapeDecision, tapeDecisionRun_eq_some_iff, bitMachineAfter_eq_iterate]

theorem clocked_tape_decision_monotone_and_in_time :
    ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ)
      (a : Λ → Bool) (input : List Γ) (t u : ℕ) (b : Bool),
      t ≤ u → tapeDecision M a input t = some b →
        tapeDecision M a input u = some b ∧
          ∃ cfg : Turing.TM0.Cfg Γ Λ,
            Nonempty (StateTransition.EvalsToInTime (Turing.TM0.step M)
                (Turing.TM0.init input) (some cfg) t) ∧
              Turing.TM0.step M cfg = none ∧ a cfg.q = b := by
  intro Γ Λ _ _ M a input t u b htu h
  simp only [tapeDecision, tapeDecisionRun_eq_some_iff] at h
  obtain ⟨s, cfg, hst, hiter, hhalt, hacc⟩ := h
  refine ⟨?_, cfg, ⟨⟨⟨s, ?_⟩, hst⟩, hhalt, hacc⟩⟩
  · simp only [tapeDecision, tapeDecisionRun_eq_some_iff]
    exact ⟨s, cfg, hst.trans htu, hiter, hhalt, hacc⟩
  · exact hiter

end Qatlib.Concepts.ClassicalTape.TapeCompilation
