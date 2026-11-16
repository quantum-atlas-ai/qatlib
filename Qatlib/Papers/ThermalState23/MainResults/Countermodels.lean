/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# Missing-unitarity countermodel for the legacy boosting contract

The legacy Proposition H.1 quantified over arbitrary matrix-valued functions
`M` and `U`. With no unitary target condition, both functions can be zero.
The paper's lower-bound target must be restored before using its conclusion.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.ThermalState23.MainResults.Countermodels

/-- The complete legacy H.1 statement with its unconstrained matrix target. -/
def LegacyH1 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, k < N ∧
    ¬ ∃ (M U : ℝ → Matrix (Fin N) (Fin N) ℂ),
        (∀ E : ℝ, ‖M E - U E‖ ≤ 1 / 2) ∧
          (∀ (E : ℝ) (i j : Fin N),
              (∀ m : ℤ,
                  (k : ℝ) * (2 * Real.pi / (N : ℝ)) <
                    |2 * Real.pi * ((i : ℝ) - (j : ℝ)) / (N : ℝ) - E -
                      2 * Real.pi * (m : ℝ)|) →
                M E i j = 0) ∧
            ∀ i j : Fin N, Continuous fun E : ℝ => M E i j

/-- Zero matrix functions disprove the legacy H.1 statement without a target-unitarity premise. -/
theorem zero_refutes_H1 : ¬ LegacyH1 := by
  intro h
  obtain ⟨N, _, hN⟩ := h 0
  apply hN
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩
  · intro E
    simp
  · intro E i j _
    rfl
  · intro i j
    exact continuous_const

end Qatlib.Papers.ThermalState23.MainResults.Countermodels
