/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel

/-!
# Quantum detailed balance

This module defines the square-root sandwich and the quantum detailed-balance predicate for
complex linear maps on finite matrix algebras. The predicate expresses Hilbert–Schmidt symmetry
after the sandwich, following [TemmeEtAl2011]. Channel and density hypotheses are supplied
separately by its consumers.

## Main statements

* `densSqrt`: The functional-calculus square root used in the sandwich.
* `QuantumDetailedBalance`: The trace-pairing symmetry for all complex matrices.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdaptiveCP.BranchTrace


namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Matrix

variable {D : ℕ}

/-- The matrix obtained by applying the real square-root function to `σ` through continuous
functional calculus. -/
noncomputable def densSqrt (σ : Operator D) : Operator D := cfc Real.sqrt σ

/-- The trace-pairing symmetry of `T` after sandwiching by `densSqrt σ`, required for every pair
of complex matrices. This is the linear-map formulation of quantum detailed balance in
[Temme et al., Section 6][TemmeEtAl2011]. -/
def QuantumDetailedBalance (T : Operator D →ₗ[ℂ] Operator D) (σ : Operator D) : Prop :=
  ∀ ρ φ : Operator D,
    Matrix.trace (ρᴴ * T (densSqrt σ * φ * densSqrt σ))
      = Matrix.trace ((T (densSqrt σ * ρ * densSqrt σ))ᴴ * φ)

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
