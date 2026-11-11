/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision

/-!
# Specification of an explicit copy budget

`SupNormTightCopyBudget` specifies the sufficient copy count max(1, ⌈8t²‖ρ - σ‖₁/ε⌉) for
fresh-copy evolution of a density operator. It requires error at most ε, exact resource counts,
and the uniform bound n ≤ 16t²/ε + 1.

This is an explicit precision budget for density-matrix exponentiation
[LloydMohseniRebentrost2014].

## Main statements

* `SupNormTightCopyBudget`: states the state-dependent budget and its uniform upper bound.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent

open Matrix

set_option autoImplicit false

/-- Specifies the error, resource counts, and uniform size bound for the copy budget `max 1
(Nat.ceil (8 * t² * Matrix.traceNorm (ρ - σ) / ε))` on density operators. -/
def SupNormTightCopyBudget : Prop :=
  ∀ (D : ℕ) (ρ σ : Operator D) (t ε : ℝ),
    IsDensityOperator ρ → IsDensityOperator σ → 0 < ε →
    let n : ℕ := max 1 (Nat.ceil (8 * t ^ 2 * Matrix.traceNorm (ρ - σ) / ε))
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) 1
        (TensorGate σ (1 : Operator 1)) -
      TensorGate (HamiltonianEvolution ρ t) (1 : Operator 1) * TensorGate σ (1 : Operator 1) *
        (TensorGate (HamiltonianEvolution ρ t) (1 : Operator 1))ᴴ) ≤ ε ∧
    freshCopyResourceCounts D (List.replicate n (t / (n : ℝ))) = (n, n, n, 0) ∧
    (n : ℝ) ≤ 16 * t ^ 2 / ε + 1

end Qatlib.Concepts.CopyEvolution.CopyExponent
