/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent

open Matrix

set_option autoImplicit false

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
