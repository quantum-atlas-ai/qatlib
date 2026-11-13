/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Conditional branch error specifications

Defines the selected instrument output `selectedBranch` and its trace-normalized version
`normalizedBranch`. The predicate `PureUniformBranchBound` records a uniform unnormalized error
bound and reference success lower bound on normalized pure inputs.

The structure `MixedChannelGuarantee` and its predicate `Holds` describe success and
normalized-output error bounds for all density inputs. These specifications use the quantum
instrument framework of [Watrous2018].

## Main statements

* `PureUniformBranchBound`: uniform pure-input branch error and success assumptions.
* `MixedChannelGuarantee.Holds`: the corresponding mixed-input conditional statement.
* `transportPureToMixed`: the proposed error and success parameters.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix
open scoped Classical Matrix.Norms.L2Operator

/-- The sum of an instrument's output branches over the selected finite outcome set. -/
noncomputable def selectedBranch {O : Type} [Fintype O] {D E : ℕ} (J : Instrument O D E)
    (S : Finset O) (ρ : Operator D) : Operator E :=
  ∑ o ∈ S, (J.branch o) ρ

/-- Divides an operator by its complex trace, returning zero when that trace is zero. -/
noncomputable def normalizedBranch {E : ℕ} (σ : Operator E) : Operator E :=
  if Matrix.trace σ = 0 then 0 else ((Matrix.trace σ)⁻¹ : ℂ) • σ

/-- A nonnegative error, a positive larger gap, and uniform pure-input bounds on the
selected-branch trace-norm difference and reference branch trace. -/
noncomputable def PureUniformBranchBound {O : Type} [Fintype O] {D E : ℕ}
    (J K : Instrument O D E) (S : Finset O) (error gap : ℝ) : Prop :=
  0 ≤ error ∧ 0 < gap ∧ error < gap ∧
    (∀ ψ : QState (Fin D), Normalized ψ →
      Matrix.traceNorm (selectedBranch J S (outerProduct ψ)
          - selectedBranch K S (outerProduct ψ)) ≤ error ∧
        gap ≤ (Matrix.trace (selectedBranch K S (outerProduct ψ))).re)

/-- The real direction-error and success-gap parameters of a mixed-input conditional guarantee. -/
structure MixedChannelGuarantee (D E : ℕ) where

  directionError : ℝ

  successGap : ℝ

/-- Asserts positive success gap and nonnegative direction error, a reference success lower
bound, positive actual success, and a trace-norm bound between normalized selected outputs
for every density input. -/
noncomputable def MixedChannelGuarantee.Holds {O : Type} [Fintype O] {D E : ℕ}
    (G : MixedChannelGuarantee D E) (J K : Instrument O D E)
    (S : Finset O) : Prop :=
  0 < G.successGap ∧ 0 ≤ G.directionError ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      G.successGap ≤ (Matrix.trace (selectedBranch K S ρ)).re ∧
        0 < (Matrix.trace (selectedBranch J S ρ)).re ∧
        Matrix.traceNorm (normalizedBranch (selectedBranch J S ρ)
            - normalizedBranch (selectedBranch K S ρ)) ≤ G.directionError)

/-- The mixed-input guarantee parameters with direction error `2 * error / (gap - error)` and
success gap `gap - error`. -/
noncomputable def transportPureToMixed {D E : ℕ} (error gap : ℝ) :
    MixedChannelGuarantee D E :=
  ⟨2 * error / (gap - error), gap - error⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision
