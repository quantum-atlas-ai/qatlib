module

import Qatlib.Papers.QAOAWeighted24.MainResults.Counterexample

/-!
# Consumer checks for the weighted-QAOA sharpness witness

This ordinary `module` imports the Dev theorem through its public namespace and
instantiates both the literal C4 refutation and the repaired direct-edge bound.
-/

set_option autoImplicit false

open Qatlib.Papers.QAOAWeighted24.MainResults

/-- The source's unrestricted derivative bound fails on the concrete positive C4 witness. -/
example :
    |c4SelectedDerivative 2 (Real.pi / 12)| >
      printedDerivativeBound 2 (Real.pi / 12) :=
  c4_positive_literal_counterexample

/-- The consumer sees the exact negation of the unrestricted source scope. -/
example :
    ¬ (∀ γ w : ℝ,
      |c4SelectedDerivative γ w| ≤ printedDerivativeBound γ w) :=
  unrestricted_derivative_bound_refuted

/-- The repaired bound applies at the concrete admissible parameter `γ = 1`. -/
example (w : ℝ) :
    |Real.sin (w * 1) + 1 * w * Real.cos (w * 1)| ≤ (1 + 1) * |w| := by
  simpa using repaired_direct_derivative_bound 1 (by norm_num) (by norm_num) w
