/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# An existential amplitude-estimation contract

This module defines `estimateSandwich`, an existential estimate-and-distribution contract
supporting the estimation analysis of [Ambainis2012]. For each unitary preparation and failure
tolerance, it asks for a finite outcome law, a high-mass set satisfying the specified error
bound, exact zero estimates at zero mass, and a circuit realization with a query-and-gate bound.

## Main statements

* `estimateSandwich`: The existential probability, accuracy, zero-mass, and circuit-cost
  contract.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate

open Matrix

/-- The proposition that every unitary-prepared marked probability has an estimator with a
normalized nonnegative finite law, a good set of mass at least `1 - δ` satisfying the stated
resolution-dependent error bound, and exact zero output at zero mass. The law must be
realized by a circuit with combined query and gate count at most `r * (6 * M - 3)` for some
`M ≥ 2` and `r`. -/
def estimateSandwich : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ), W ∈ Matrix.unitaryGroup I ℂ →
    ∀ (j₀ : I) (S : Finset I) (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∃ (M r : ℕ), 2 ≤ M ∧
    ∃ (est : (Fin r → Fin M) → ℝ) (law : (Fin r → Fin M) → ℝ)
      (good : Finset (Fin r → Fin M)),
      (∑ ω, law ω = 1) ∧ (∀ ω, 0 ≤ law ω) ∧
      (1 - δ ≤ ∑ ω ∈ good, law ω) ∧
      (∀ ω ∈ good, |est ω - MeasureProb (ApplyGate W (Ket j₀)) S|
        ≤ MeasureProb (ApplyGate W (Ket j₀)) S / 4
          + 8 / (M : ℝ) * Real.sqrt (MeasureProb (ApplyGate W (Ket j₀)) S)
          + 10 / (M : ℝ) ^ 2) ∧
      (MeasureProb (ApplyGate W (Ket j₀)) S = 0 → ∀ ω, est ω = 0) ∧
      (∃ (R : Type) (_ : Fintype R) (O : Matrix R R ℂ) (cct : Circuit R)
        (init : QState R) (lbl : R → (Fin r → Fin M)),
        (∀ ω, law ω =
          MeasureProb (Run O cct init) (Finset.univ.filter (fun p => lbl p = ω))) ∧
        QueryCount cct + GateCount cct ≤ r * (6 * M - 3))

end Qatlib.Papers.VarTimeAmpAmp10.Estimate
