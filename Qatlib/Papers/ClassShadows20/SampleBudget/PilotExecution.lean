/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMomentsBounds
public import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot

@[expose] public section


/-!
# Executed arithmetic for the shadows pilot moments

This is a resource supplement for the rational `pilotMoments` used by the
Classical Shadows statistical support. The executed bit-arithmetic evaluator
returns the same two moments and sample count, with a uniform polynomial bound
on the explicit binary routines' Boolean-gate charges in the encoded supplied
table. Those charges are taken from the very arithmetic calls producing the values.

This result supplies partial pilot arithmetic support. It excludes record
generation, the cost of evaluating `f`, representation interpretation, structural
control, allocation, median selection, and peak workspace of primitive routines.
The counter measures arithmetic gates. The full sampler and statistical pipeline require
separate execution and resource guarantees.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.ClassShadows20.SampleBudget

open Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection
open scoped BigOperators

/-- The counted binary evaluator returns exactly the original rational pilot moments. -/
theorem pilot_moments_execution {I : Type} (N : ℕ) (f : I → ℚ) (omega : Fin N → I) :
    let result := run (List.ofFn fun i => f (omega i))
    (result.mean, result.secondMoment, result.records) = pilotMoments N f omega := by
  have h := run_values (List.ofFn fun i => f (omega i))
  rw [pilotMoments_eq]
  simp only [List.sum_ofFn, List.map_ofFn, List.length_ofFn] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

/-- The same evaluator returns nonzero, uniformly bounded Boolean-gate charges
for a nonempty supplied table, together with output-width bounds. -/
theorem pilot_moments_executed_cost {I : Type} (N : ℕ) (f : I → ℚ) (omega : Fin N → I) :
    let samples := List.ofFn fun i => f (omega i)
    N ≤ (run samples).bitOps ∧
      (run samples).bitOps ≤ 3565 * (encodedSize samples + 1) ^ 4 ∧
      width (run samples).mean ≤ 2 * encodedSize samples ∧
      width (run samples).secondMoment ≤ 2 * encodedSize samples := by
  refine ⟨?_, run_cost_bound _, run_output_width _⟩
  simpa only [List.length_ofFn] using run_cost_lower (List.ofFn fun i => f (omega i))

end Qatlib.Papers.ClassShadows20.SampleBudget
