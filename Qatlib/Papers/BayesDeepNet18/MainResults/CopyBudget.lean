/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BayesDeepNet18.MainResults.CopyEvolutionModel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Integer-copy and input-normalization boundaries of the legacy evolution contracts. -/

set_option autoImplicit false

namespace Qatlib.Papers.BayesDeepNet18.MainResults

open scoped ComplexOrder

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BayesDeepNet18.MainResults

/-- The one-dimensional identity is a concrete admissible density input. -/
theorem one_density : IsDensityOperator (1 : Operator 1) := by
  exact ⟨Matrix.PosSemidef.one, by simp⟩

/-- A positive simulated time requires at least one round in the original witness model. -/
theorem copies_pos {d : ℕ} {H : Operator d} {t ε : ℝ} {step : StepFamily d}
    (ht : 0 < t) (W : IteratedStepWitness d H t ε step) : 1 ≤ W.copies := by
  have hn : W.copies ≠ 0 := by
    intro hz
    have h := W.hsteps
    simp only [hz, Nat.cast_zero, zero_mul] at h
    exact (ne_of_gt ht) h.symm
  omega

/-- The all-positive-accuracy bound omits the additive one forced by integer copies. -/
theorem budget_failure {d : ℕ} (H : Operator d) (step : StepFamily d)
    (C : ℝ) (hC : 0 < C) :
    ¬ ∃ W : IteratedStepWitness d H 1 (2 * C) step,
      (W.copies : ℝ) ≤ C * (1 : ℝ) ^ 2 / (2 * C) := by
  rintro ⟨W, hW⟩
  have hn : (1 : ℝ) ≤ (W.copies : ℝ) := by
    exact_mod_cast copies_pos (by norm_num : (0 : ℝ) < 1) W
  have hhalf : C * (1 : ℝ) ^ 2 / (2 * C) = 1 / 2 := by
    rw [one_pow, mul_one, div_eq_iff (by positivity : 2 * C ≠ 0)]
    ring
  rw [hhalf] at hW
  linarith

/-- The zero-order polynomial's zero budget cannot partition any positive time. -/
theorem zero_budget {d : ℕ} (H : Operator d) (step : StepFamily d)
    (t ε : ℝ) (ht : 0 < t) :
    ¬ ∃ W : IteratedStepWitness d H t ε step, (W.copies : ℝ) ≤ 0 := by
  rintro ⟨W, hW⟩
  have hn : (1 : ℝ) ≤ (W.copies : ℝ) := by exact_mod_cast copies_pos ht W
  linarith

end Qatlib.Papers.BayesDeepNet18.MainResults
