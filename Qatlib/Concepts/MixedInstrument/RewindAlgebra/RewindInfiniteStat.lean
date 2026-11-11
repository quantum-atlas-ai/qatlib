/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.RejectionRewind.InfiniteRewindProgram

/-!
# Infinite rewind completion specification

`RewindInfiniteCompletion` specifies a completely positive trace preserving limit of stopped
rewind maps for two orthogonal projectors. It requires summability of the success series on
every operator and a uniform inverse linear trace norm tail bound on density inputs. This
expresses infinite completion of the rejection process from [TemmeEtAl2011].

## Main statements

* `RewindInfiniteCompletion`: The proposition asserting a summable success series
  representation, convergence of stopped rewind maps, a completely positive trace preserving
  limit, and trace norm tail at most `1 / (2 * (n + 1))` on density inputs.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuantumGibbs.RejectionRewind

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Matrix Filter
open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator

/-- The proposition asserting a summable success series representation, convergence of stopped
rewind maps, a completely positive trace preserving limit, and trace norm tail at most `1 /
(2 * (n + 1))` on density inputs. -/
def RewindInfiniteCompletion : Prop :=
  ∀ (D : ℕ) (P Q : Operator D),
    P.IsHermitian → P * P = P → Q.IsHermitian → Q * Q = Q →
    ∃ T : Operator D →ₗ[ℂ] Operator D,
      (∀ X : Operator D,
        Summable (fun n : ℕ => rewindSuccessRoundMap P Q n X) ∧
        T X = rewindStoppedMap P Q 0 X +
          ∑' n : ℕ, rewindSuccessRoundMap P Q n X) ∧
      (∀ X : Operator D,
        Tendsto (fun n : ℕ => rewindStoppedMap P Q n X) atTop (𝓝 (T X))) ∧
      CompletelyPositive T ∧ TracePreserving T ∧
      (∀ ρ : Operator D, ρ.PosSemidef → Matrix.trace ρ = 1 →
        ∀ n : ℕ, Matrix.traceNorm (T ρ - rewindStoppedMap P Q n ρ) ≤
          1 / (2 * ((n : ℝ) + 1)))

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
