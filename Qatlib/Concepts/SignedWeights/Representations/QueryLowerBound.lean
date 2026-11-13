/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle

/-!
# Negative-Weight Query Lower Bounds

This module states the bounded-error query lower bounds associated with Theorem 2 of
[HoyerLeeSpalek2007] for finite-alphabet phase-oracle circuits. A Hermitian witness `Γ`
vanishing on equal-output pairs yields both a matrix progress inequality involving
`maxFilterNorm` and a query lower bound involving `advPmValue`.

The general output estimate uses the factor `1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps`.
When the output type has exactly two elements, `theorem2_boolean` uses the stronger factor
without the final `2 * eps` term.

## Main statements

- `theorem2_general` proves the witness and optimized bounds for a general finite output type.
- `theorem2_boolean` proves the stronger bounds for a two-element output type.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Theorem 2.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.QueryLowerBound

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- A bounded-error finite-alphabet query run yields the witness progress bound and the
optimized `advPmValue` query lower bound with error factor `1 - 2 * Real.sqrt (eps * (1 -
eps)) - 2 * eps`. This is the general-output estimate associated with Theorem 2 of
[HoyerLeeSpalek2007]. -/
theorem theorem2_general
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (Γ : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hΓ : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Γ‖ ≤
      2 * (QueryCount C) * maxFilterNorm input Γ ∧
    ENNReal.ofReal ((1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) / 2) *
      advPmValue input f ≤ ((QueryCount C : ℕ) : ℝ≥0∞) := by
  have h := stageA_general_adversary_clause16_full_endpoint_v2 q n X W Y input f Γ C psi out eps
    hΓ hz hrun
  exact ⟨h.1, h.2.1⟩

/-- For a bounded-error query run with exactly two output values, the witness and optimized
query lower bounds use error factor `1 - 2 * Real.sqrt (eps * (1 - eps))`. This is the
two-output estimate associated with Theorem 2 of [HoyerLeeSpalek2007]. -/
theorem theorem2_boolean
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (Γ : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hΓ : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps) (hc : Fintype.card Y = 2) :
    (1 - 2 * Real.sqrt (eps * (1 - eps))) * ‖Γ‖ ≤
      2 * (QueryCount C) * maxFilterNorm input Γ ∧
    ENNReal.ofReal ((1 - 2 * Real.sqrt (eps * (1 - eps))) / 2) *
      advPmValue input f ≤ ((QueryCount C : ℕ) : ℝ≥0∞) :=
  (stageA_general_adversary_clause16_full_endpoint_v2 q n X W Y input f Γ C psi out eps
    hΓ hz hrun).2.2 hc

end

end Qatlib.Concepts.SignedWeights.Representations.QueryLowerBound
