/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix
open scoped Classical Matrix.Norms.L2Operator

noncomputable def selectedBranch {O : Type} [Fintype O] {D E : ℕ} (J : Instrument O D E)
    (S : Finset O) (ρ : Operator D) : Operator E :=
  ∑ o ∈ S, (J.branch o) ρ

noncomputable def normalizedBranch {E : ℕ} (σ : Operator E) : Operator E :=
  if Matrix.trace σ = 0 then 0 else ((Matrix.trace σ)⁻¹ : ℂ) • σ

noncomputable def PureUniformBranchBound {O : Type} [Fintype O] {D E : ℕ}
    (J K : Instrument O D E) (S : Finset O) (error gap : ℝ) : Prop :=
  0 ≤ error ∧ 0 < gap ∧ error < gap ∧
    (∀ ψ : QState (Fin D), Normalized ψ →
      Matrix.traceNorm (selectedBranch J S (outerProduct ψ)
          - selectedBranch K S (outerProduct ψ)) ≤ error ∧
        gap ≤ (Matrix.trace (selectedBranch K S (outerProduct ψ))).re)

structure MixedChannelGuarantee (D E : ℕ) where

  directionError : ℝ

  successGap : ℝ

noncomputable def MixedChannelGuarantee.Holds {O : Type} [Fintype O] {D E : ℕ}
    (G : MixedChannelGuarantee D E) (J K : Instrument O D E)
    (S : Finset O) : Prop :=
  0 < G.successGap ∧ 0 ≤ G.directionError ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      G.successGap ≤ (Matrix.trace (selectedBranch K S ρ)).re ∧
        0 < (Matrix.trace (selectedBranch J S ρ)).re ∧
        Matrix.traceNorm (normalizedBranch (selectedBranch J S ρ)
            - normalizedBranch (selectedBranch K S ρ)) ≤ G.directionError)

noncomputable def transportPureToMixed {D E : ℕ} (error gap : ℝ) :
    MixedChannelGuarantee D E :=
  ⟨2 * error / (gap - error), gap - error⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision
