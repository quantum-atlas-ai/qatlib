/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

def FactoringPreprocessing : Prop :=
  (∀ (N d : ℕ), 3 ≤ N → shorPreprocess N = ShorPreResult.factor d →
      1 < d ∧ d < N ∧ d ∣ N) ∧
    (∀ (N : ℕ), 3 ≤ N → shorPreprocess N = ShorPreResult.residue →
      Odd N ∧ (Nat.Prime N ∨ 2 ≤ N.primeFactors.card))

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
