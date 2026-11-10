/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.CopyEvolution.SelfTomography.EpsilonCubedSelfTomographyDefs
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix

set_option autoImplicit false

def EpsilonCubedSelfTomography : Prop :=
  ∀ (D : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ) (ε : ℝ),
    IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ →
    (∀ i, 0 ≤ eig i ∧ eig i ≤ 1) → 0 < ε → ε ≤ 1 / 2 →
    let M : ℕ := Nat.ceil (2 / ε)
    let n : ℕ := Nat.ceil (8 * (M : ℝ) * Real.pi ^ 2 / ε)
    2 ≤ M ∧ (2 : ℝ) / M ≤ ε ∧
    8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) ≤ ε ∧
    ((M - 1 : ℕ) * n : ℝ) ≤ 1000 / ε ^ 3 ∧
    (∀ (j : Fin D) (z : Fin M), z ∈ qpeGoodLabels M (eig j) →
      |qpeLabelDecode M z - eig j| ≤ 2 / (M : ℝ)) ∧
    (Matrix.trace (qpeSelfTomographyGoodProjector D M V eig *
        copyQPEIdealOutput D M ρ)).re ≥ 8 / Real.pi ^ 2 ∧
    (Matrix.trace (qpeSelfTomographyGoodProjector D M V eig *
        copyQPEOutput D M n ρ)).re ≥ 8 / Real.pi ^ 2 - ε ∧
    copyQPEResources D M n = ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0)

end Qatlib.Concepts.CopyEvolution.SelfTomography
