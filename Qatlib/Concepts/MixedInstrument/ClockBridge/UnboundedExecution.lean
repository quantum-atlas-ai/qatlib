/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.UnboundedExecutionDefs

/-!
# Unbounded execution mass and resource bounds

This module splits an execution law into halted and never-halting mass and derives expected-cost
and peak-space bounds from uniform outcome bounds. It also records cutoff inequalities and
reformulations of charged success comparisons. The quantum algorithmic setting is described in
[NielsenChuang2010].

## Main statements

* `clause20_joint_law_split`: collects halted and never-halting mass bounds.
* `clause20_expected_cost_le_budget`: bounds expected cost by a uniform budget.
* `clause19_comparison_never_mass`: rewrites a failure comparison as a success comparison.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open scoped ENNReal BigOperators Classical

/-- The never-halting mass and halted mass of an execution law sum to one. -/
theorem exec_never_add_halted {α : Type} [Fintype α] (p : ExecLaw α) :
    neverMass p + haltedMass p = 1 := by
  simp [neverMass, haltedMass]

/-- The never-halting mass of an execution law is nonnegative. -/
theorem exec_never_mass_nonneg {α : Type} [Fintype α] (p : ExecLaw α) :
    0 ≤ neverMass p := by
  exact p.nonneg none

/-- The never-halting mass of an execution law is at most one. -/
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

/-- The halted mass of an execution law is nonnegative. -/
theorem exec_halted_mass_nonneg {α : Type} [Fintype α] (p : ExecLaw α) :
    0 ≤ haltedMass p := by
  simp only [haltedMass]
  linarith [exec_never_mass_le_one p]

/-- The never-halting mass lies in `[0, 1]`, the halted mass is nonnegative, and the two masses
sum to one. -/
theorem clause20_joint_law_split {α : Type} [Fintype α] (p : ExecLaw α) :
    0 ≤ neverMass p ∧ neverMass p ≤ 1 ∧ 0 ≤ haltedMass p ∧
      neverMass p + haltedMass p = 1 :=
  ⟨exec_never_mass_nonneg p, exec_never_mass_le_one p, exec_halted_mass_nonneg p,
    exec_never_add_halted p⟩

/-- If every execution outcome has cost at most `b`, its expected cost is at most `b`. -/
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

/-- If the space cost of every execution outcome is at most `b`, the execution peak-space
quantity is at most `b`. -/
theorem clause20_peak_space_le_budget {α : Type} [Fintype α] (p : ExecLaw α)
    (c : ExecOutcome α → ℕ) (b : ℕ) (hb : ∀ o, c o ≤ b) :
    execPeakSpace p c ≤ b := by
  refine Finset.sup_le (fun o ho => ?_)
  have ho' : 0 < p.prob o := by
    simpa [Finset.mem_filter, Finset.mem_univ, true_and] using! ho
  exact hb o

/-- A lower bound `s` on the complement of never-halting mass gives the upper bound `1 - s` on
never-halting mass. -/
theorem clause20_never_mass_le_complement {α : Type} [Fintype α] (p : ExecLaw α)
    (s : ℝ) (hs : s ≤ 1 - neverMass p) : neverMass p ≤ 1 - s := by
  linarith

/-- If never-halting mass is at most one half, its complement is at least one half. -/
theorem clause20_never_mass_le_half {α : Type} [Fintype α] (p : ExecLaw α)
    (h : neverMass p ≤ 1 / 2) : 1 / 2 ≤ 1 - neverMass p := by
  linarith

/-- For positive `N`, the source cutoff is strictly smaller than the charged cutoff. -/
theorem clause19_source_cutoff_lt_charged (N : ℕ) (hN : 0 < N) :
    sourceCutoff N < chargedCutoff N := by
  exact source_deadline_lt_charged_budget N hN

/-- For positive `N` and `c ≥ 1`, the source cutoff is strictly smaller than `c` times the
charged cutoff. -/
theorem clause19_c_fold_cutoff_dominates (N : ℕ) (hN : 0 < N) (c : ℕ) (hc : 1 ≤ c) :
    sourceCutoff N < c * chargedCutoff N := by
  have hlt : sourceCutoff N < chargedCutoff N := clause19_source_cutoff_lt_charged N hN
  have h1 : chargedCutoff N ≤ c * chargedCutoff N := by
    calc
      chargedCutoff N = 1 * chargedCutoff N := (one_mul _).symm
      _ ≤ c * chargedCutoff N := Nat.mul_le_mul hc (Nat.le_refl _)
  exact Nat.lt_of_lt_of_le hlt h1

/-- For a nonempty finite input, there exists a real number between one half and one. -/
theorem clause19_source_cutoff_success_mass {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    ∃ p : ℝ, 1 / 2 ≤ p ∧ p ≤ 1 := by
  obtain ⟨p, -, hp, hp1⟩ := source_timeout_success T hN
  exact ⟨p, hp, hp1⟩

/-- For a nonempty finite input, there exists a real `p` whose complement lies between zero and
one half. -/
theorem clause19_source_cutoff_never_mass_le_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    ∃ p : ℝ, 0 ≤ 1 - p ∧ 1 - p ≤ 1 / 2 := by
  obtain ⟨p, hp, hp1⟩ := clause19_source_cutoff_success_mass T hN
  exact ⟨p, by linarith, by linarith⟩

/-- The displayed upper bound on the long-run failure complement is equivalent to the
corresponding lower bound on `chargedInitialSuccess`. -/
theorem clause19_comparison_never_mass {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ) :
    (1 - chargedInitialSuccess T (c * chargedBudget N)) ≤
        (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ↔ chargedInitialSuccess T (c * chargedBudget N) ≥
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  constructor <;> intro h <;> linarith

/-- The displayed strict upper bound on the long-run failure complement is equivalent to the
corresponding strict lower bound on `chargedInitialSuccess`. -/
theorem clause19_comparison_never_mass_strict {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ) :
    (1 - chargedInitialSuccess T (c * chargedBudget N)) <
        (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ↔ chargedInitialSuccess T (c * chargedBudget N) >
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  constructor <;> intro h <;> linarith

/-- For a nonempty finite input, the complement of charged initial success at `chargedBudget N`
is at most one half. -/
theorem clause19_short_run_never_mass_le_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    1 - chargedInitialSuccess T (chargedBudget N) ≤ 1 / 2 := by
  have h := charged_initial_success_half T hN
  linarith

/-- The assumed strict success comparison implies the corresponding non-strict power bound on
the complement of long-run charged initial success. -/
theorem clause19_long_run_never_mass_under_comparison {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ)
    (h : chargedInitialSuccess T (c * chargedBudget N) >
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c) :
    1 - chargedInitialSuccess T (c * chargedBudget N) ≤
      (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  have h' := (clause19_comparison_never_mass_strict T c).mpr h
  linarith

end Qatlib.Concepts.MixedInstrument.ClockBridge
