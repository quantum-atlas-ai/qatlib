/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.ResidueFactoringPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

def ResidueFactoringAlgorithm : Prop :=
  ∀ (N R k M : ℕ) [NeZero N] (hM : 0 < M) (hk : N ≤ 2 ^ k),
    3 ≤ N → ¬Nat.Prime N → 2 * N ^ 2 < M →
    (∀ d : ℕ, shorPreprocess N = ShorPreResult.factor d →
        1 < d ∧ d < N ∧ d ∣ N) ∧
    shorResidueProgramSuccessProb N R k M hM hk
      ≥ 1 - (1 - shorResidueAttemptBound N k) ^ R ∧
    (∀ (y : ZMod N) (d : ℕ),
        residueClassicalFactor N y = some d → 1 < d ∧ d < N ∧ d ∣ N) ∧
    (∀ (a : (ZMod N)ˣ) (y z : Fin M) (d : ℕ),
        attemptFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
