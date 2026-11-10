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
open scoped ComplexOrder

set_option autoImplicit false

def StateDependentCopyPrecision : Prop :=
  ∀ (D r : ℕ) (ρ : Operator D) (t : ℝ) (n : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    IsDensityOperator ρ → X.PosSemidef → 0 < n →
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) r X -
        TensorGate (HamiltonianEvolution ρ t) (1 : Operator r) * X *
          (TensorGate (HamiltonianEvolution ρ t) (1 : Operator r))ᴴ) ≤
      8 * t ^ 2 / (n : ℝ) * Matrix.traceNorm (X - TensorGate ρ (Matrix.traceLeft X)) ∧
    freshCopyResourceCounts D (List.replicate n (t / (n : ℝ))) = (n, n, n, 0)

end Qatlib.Concepts.CopyEvolution.CopyExponent
