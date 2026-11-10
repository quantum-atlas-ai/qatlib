/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.QspSimulation.WordModel

def FunctionFormSubgoal : Prop :=
  ∀ (phis : List ℝ), ∃ (P Q₁ Q₂ S : Polynomial ℂ),
    P.natDegree ≤ phis.length ∧
    S.natDegree ≤ phis.length ∧
    Q₁.natDegree ≤ phis.length - 1 ∧
    Q₂.natDegree ≤ phis.length - 1 ∧
    (∀ t : ℂ, P.eval (-t) = ((-1 : ℂ) ^ phis.length) * P.eval t) ∧
    (∀ t : ℂ, S.eval (-t) = ((-1 : ℂ) ^ phis.length) * S.eval t) ∧
    (∀ t : ℂ, Q₁.eval (-t) = ((-1 : ℂ) ^ (phis.length + 1)) * Q₁.eval t) ∧
    (∀ t : ℂ, Q₂.eval (-t) = ((-1 : ℂ) ^ (phis.length + 1)) * Q₂.eval t) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 0 = P.eval ((x : ℂ))) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 1 = S.eval ((x : ℂ))) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 1
      = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₁.eval ((x : ℂ))) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 0
      = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₂.eval ((x : ℂ)))

end Qatlib.Concepts.QspSimulation.WordModel
