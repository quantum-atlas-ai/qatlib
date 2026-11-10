/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent

open Matrix
open scoped ComplexOrder

def LowRankExponentiationRestricted : Prop :=
  ∀ (r d T k : ℕ) (ψ : Fin r → QState (Fin d)), (∀ i, Normalized (ψ i)) →
    ∀ (w : Fin r → ℝ), (∀ i, 0 ≤ w i) → (∑ i, (w i) ^ 2 = 1) →
    ∀ (t : ℝ), |t| ≤ (T : ℝ) →
    ∀ (s : ℕ) (Y : Matrix (Fin r × Fin s) (Fin r × Fin s) ℂ), Y.PosSemidef →
    let X : Operator r := gramMatrix ψ w
    let n := copyPrecisionBudget T k
    Matrix.traceNorm (freshCopyReferenceRun X (List.replicate n (t / (n : ℝ))) s Y -
        TensorGate (HamiltonianEvolution X t) (1 : Operator s) * Y *
          (TensorGate (HamiltonianEvolution X t) (1 : Operator s))ᴴ) ≤
          ((2 : ℝ)⁻¹) ^ k * Matrix.traceNorm Y ∧
    freshCopyResourceCounts r (List.replicate n (t / (n : ℝ))) = (n, n, n, 0)

end Qatlib.Concepts.CopyEvolution.CopyExponent
