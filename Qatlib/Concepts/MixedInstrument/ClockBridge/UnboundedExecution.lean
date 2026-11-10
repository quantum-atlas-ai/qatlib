/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.UnboundedExecutionDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open scoped ENNReal BigOperators Classical

theorem exec_never_add_halted {α : Type} [Fintype α] (p : ExecLaw α) :
    neverMass p + haltedMass p = 1 := by
  simp [neverMass, haltedMass]

theorem exec_never_mass_nonneg {α : Type} [Fintype α] (p : ExecLaw α) :
    0 ≤ neverMass p := by
  exact p.nonneg none

theorem exec_never_mass_le_one {α : Type} [Fintype α] (p : ExecLaw α) :
    neverMass p ≤ 1 := by
  have h1 : (∑ x, (if x = none then p.prob x else 0)) = p.prob none := by simp
  have h2 : (∑ x, (if x = none then p.prob x else 0)) ≤ ∑ x, p.prob x := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    split_ifs
    · linarith [p.nonneg x]
    · linarith [p.nonneg x]
  rw [h1] at h2
  rw [← p.sum_one]
  exact h2

theorem exec_halted_mass_nonneg {α : Type} [Fintype α] (p : ExecLaw α) :
    0 ≤ haltedMass p := by
  simp only [haltedMass]
  linarith [exec_never_mass_le_one p]

theorem clause20_joint_law_split {α : Type} [Fintype α] (p : ExecLaw α) :
    0 ≤ neverMass p ∧ neverMass p ≤ 1 ∧ 0 ≤ haltedMass p ∧
      neverMass p + haltedMass p = 1 :=
  ⟨exec_never_mass_nonneg p, exec_never_mass_le_one p, exec_halted_mass_nonneg p,
    exec_never_add_halted p⟩

theorem clause20_expected_cost_le_budget {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) (b : ℕ) (hb : ∀ o, c o ≤ b) :
    execExpectedCost p c ≤ (b : ENNReal) := by
  have h1 : ∀ o, ENNReal.ofReal (p.prob o) * (c o : ENNReal)
      ≤ ENNReal.ofReal (p.prob o) * (b : ENNReal) := by
    intro o
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb o)
      (by positivity)
  have h2 : ∑ o, ENNReal.ofReal (p.prob o) * (b : ENNReal)
      = (∑ o, ENNReal.ofReal (p.prob o)) * (b : ENNReal) := by
    rw [← Finset.sum_mul]
  have h3 : (∑ o, ENNReal.ofReal (p.prob o)) = 1 := by
    have h := ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Option α)))
      (f := fun o => p.prob o) (fun o _ => p.nonneg o)
    rw [← h, p.sum_one]
    simp
  calc
    execExpectedCost p c = ∑ o, ENNReal.ofReal (p.prob o) * (c o : ENNReal) := rfl
    _ ≤ ∑ o, ENNReal.ofReal (p.prob o) * (b : ENNReal) :=
      Finset.sum_le_sum (fun o _ => h1 o)
    _ = (∑ o, ENNReal.ofReal (p.prob o)) * (b : ENNReal) := h2
    _ = 1 * (b : ENNReal) := by rw [h3]
    _ = (b : ENNReal) := by simp

theorem clause20_peak_space_le_budget {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) (b : ℕ) (hb : ∀ o, c o ≤ b) :
    execPeakSpace p c ≤ b := by
  refine Finset.sup_le (fun o ho => ?_)
  have ho' : 0 < p.prob o := by
    simpa [Finset.mem_filter, Finset.mem_univ, true_and] using! ho
  exact hb o

theorem clause20_never_mass_le_complement {α : Type} [Fintype α] (p : ExecLaw α)
    (s : ℝ) (hs : s ≤ 1 - neverMass p) : neverMass p ≤ 1 - s := by
  linarith

theorem clause20_never_mass_le_half {α : Type} [Fintype α] (p : ExecLaw α)
    (h : neverMass p ≤ 1 / 2) : 1 / 2 ≤ 1 - neverMass p := by
  linarith

theorem clause19_source_cutoff_lt_charged (N : ℕ) (hN : 0 < N) :
    sourceCutoff N < chargedCutoff N := by
  exact source_deadline_lt_charged_budget N hN

theorem clause19_c_fold_cutoff_dominates (N : ℕ) (hN : 0 < N) (c : ℕ) (hc : 1 ≤ c) :
    sourceCutoff N < c * chargedCutoff N := by
  have hlt : sourceCutoff N < chargedCutoff N := clause19_source_cutoff_lt_charged N hN
  have h1 : chargedCutoff N ≤ c * chargedCutoff N := by
    calc
      chargedCutoff N = 1 * chargedCutoff N := (one_mul _).symm
      _ ≤ c * chargedCutoff N := Nat.mul_le_mul hc (Nat.le_refl _)
  exact Nat.lt_of_lt_of_le hlt h1

theorem clause19_source_cutoff_success_mass {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    ∃ p : ℝ, 1 / 2 ≤ p ∧ p ≤ 1 := by
  obtain ⟨p, -, hp, hp1⟩ := source_timeout_success T hN
  exact ⟨p, hp, hp1⟩

theorem clause19_source_cutoff_never_mass_le_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    ∃ p : ℝ, 0 ≤ 1 - p ∧ 1 - p ≤ 1 / 2 := by
  obtain ⟨p, hp, hp1⟩ := clause19_source_cutoff_success_mass T hN
  exact ⟨p, by linarith, by linarith⟩

theorem clause19_comparison_never_mass {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ) :
    (1 - chargedInitialSuccess T (c * chargedBudget N)) ≤
        (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ↔ chargedInitialSuccess T (c * chargedBudget N) ≥
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  constructor <;> intro h <;> linarith

theorem clause19_comparison_never_mass_strict {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ) :
    (1 - chargedInitialSuccess T (c * chargedBudget N)) <
        (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ↔ chargedInitialSuccess T (c * chargedBudget N) >
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  constructor <;> intro h <;> linarith

theorem clause19_short_run_never_mass_le_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    1 - chargedInitialSuccess T (chargedBudget N) ≤ 1 / 2 := by
  have h := charged_initial_success_half T hN
  linarith

theorem clause19_long_run_never_mass_under_comparison {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ)
    (h : chargedInitialSuccess T (c * chargedBudget N) >
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c) :
    1 - chargedInitialSuccess T (c * chargedBudget N) ≤
      (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  have h' := (clause19_comparison_never_mass_strict T c).mpr h
  linarith

end Qatlib.Concepts.MixedInstrument.ClockBridge
