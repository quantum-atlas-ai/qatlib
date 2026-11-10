/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdaptiveCP.BranchTrace


namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Matrix

variable {D : ℕ}

noncomputable def densSqrt (σ : Operator D) : Operator D := cfc Real.sqrt σ

def QuantumDetailedBalance (T : Operator D →ₗ[ℂ] Operator D) (σ : Operator D) : Prop :=
  ∀ ρ φ : Operator D,
    Matrix.trace (ρᴴ * T (densSqrt σ * φ * densSqrt σ))
      = Matrix.trace ((T (densSqrt σ * ρ * densSqrt σ))ᴴ * φ)

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
