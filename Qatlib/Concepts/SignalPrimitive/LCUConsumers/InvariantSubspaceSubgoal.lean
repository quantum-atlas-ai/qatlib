/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# LCU Qubitization Invariant Plane

`InvariantSubspaceSubgoal` specifies the two-dimensional invariant-plane property of a
qubitization walk built from an LCU encoding. For a normalized eigenvector of a prepared
nonnegative combination of Hermitian unitaries with eigenvalue `x` satisfying `|x| < 1`, it asks
for an orthonormal pair and a positive `y` with `x ^ 2 + y ^ 2 = 1`, in the qubitization setting
of [LowChuang2019].

On this pair, `QubitizationWalk (LCUWorkspace U P) j₀` has diagonal coefficient `2 * x ^ 2 - 1`
and opposite off-diagonal coefficients `2 * x * y`.

## Main statements

- `InvariantSubspaceSubgoal` defines the normalized invariant-plane contract for the LCU walk.

## References

- [Low and Chuang, 2019][LowChuang2019].
-/

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

open Matrix

namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers

/-- The LCU qubitization contract asserting an orthonormal invariant pair for each normalized
encoded eigenvector with `|x| < 1`. The walk acts on this pair with coefficients `2 * x ^ 2
- 1` and `2 * x * y`, where `y > 0` and `x ^ 2 + y ^ 2 = 1`. -/
def InvariantSubspaceSubgoal : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ), (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
    (∀ j, (U j)ᴴ = U j) →
    ∀ (w : J → ℝ), (∀ j, 0 ≤ w j) →
    ∀ (P : Matrix J J ℂ) (j₀ : J), IsPrepare P w j₀ →
    ∀ (ψ : QState I), Normalized ψ →
    ∀ (x : ℝ), |x| < 1 → (∑ j, w j • U j) *ᵥ ψ = ((x : ℝ) : ℂ) • ψ →
    ∃ (ψ₀ ψ₁ : QState (J × I)) (y : ℝ),
      Normalized ψ₀ ∧ Normalized ψ₁ ∧ Inner ψ₀ ψ₁ = 0 ∧
      QubitizationWalk (LCUWorkspace U P) j₀ *ᵥ ψ₀
        = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₀ - (((2 * x * y : ℝ)) : ℂ) • ψ₁ ∧
      QubitizationWalk (LCUWorkspace U P) j₀ *ᵥ ψ₁
        = (((2 * x * y : ℝ)) : ℂ) • ψ₀ + (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₁ ∧
      0 < y ∧ x ^ 2 + y ^ 2 = 1

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
