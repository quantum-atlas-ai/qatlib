/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutStat

/-!
# Specification of finite-copy Helstrom discrimination

This module defines `FiniteCopyHelstromDiscrimination`, a proposition relating the positive
spectral projector of `ρ - σ` to equal-prior discrimination success. It requires that this
projector attains the trace-norm optimum and that all binary effects satisfy the corresponding
upper bound [Helstrom1976].

The specification also requires a success lower bound for timed two-species sign readout under a
spectral gap, together with its four resource counts. The finite-copy component expresses the
discrimination application of [LloydMohseniRebentrost2014] using `twoSpeciesSignErrorBudget`.

## Main statements

* `FiniteCopyHelstromDiscrimination`: the combined optimality, finite-copy accuracy, and
  resource specification.

## References

* [Helstrom, 1976][Helstrom1976]
* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

/-- The proposition combining Helstrom optimality of the positive spectral projector with a
finite-copy two-species success bound under a spectral gap. It also specifies the four
resource counts of the QPE procedure. -/
def FiniteCopyHelstromDiscrimination : Prop :=
  ∀ (d M n : ℕ) (γ : ℝ) (ρ σ V : Operator d) (x : Fin d → ℝ),
    2 ≤ M → 0 < n → 0 < γ → γ ≤ 1 →
    IsDensityOperator ρ → IsDensityOperator σ →
    V ∈ Matrix.unitaryGroup (Fin d) ℂ →
    ρ-σ = V * Matrix.diagonal (fun j => (x j : ℂ)) * Vᴴ →
    (∀ j, x j ≠ 0 → γ ≤ |x j|) →
    let Aplus := V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ
    Aplus.PosSemidef ∧ (1-Aplus).PosSemidef ∧
    ((Matrix.trace (Aplus*ρ)).re + (Matrix.trace ((1-Aplus)*σ)).re)/2 =
      1/2 + Matrix.traceNorm (ρ-σ)/4 ∧
    (∀ A : Operator d, A.PosSemidef → (1-A).PosSemidef →
      ((Matrix.trace (A*ρ)).re + (Matrix.trace ((1-A)*σ)).re)/2
        ≤ 1/2 + Matrix.traceNorm (ρ-σ)/4) ∧
    ((1/2 + Matrix.traceNorm (ρ-σ)/4) - twoSpeciesSignErrorBudget M n γ ≤
      (twoSpeciesTimedPositiveMass d M n ρ σ ρ + twoSpeciesTimedNegativeMass d M n ρ σ σ)/2) ∧
    twoSpeciesQPEResources M n = (2*(M-1)*n,2*(M-1)*n,2*(M-1)*n,0)

end Qatlib.Concepts.CopyEvolution.Discriminate
