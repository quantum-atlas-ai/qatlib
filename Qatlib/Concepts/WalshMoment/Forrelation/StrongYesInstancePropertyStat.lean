/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.StrongDistributionAuxiliary
import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder
import Qatlib.Concepts.WalshMoment.Forrelation.StrongYesInstancePropertyDefs
set_option warningAsError false

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib
open scoped BigOperators
open Classical

def StrongYesInstanceProperty : Prop :=
  ∀ (n ℓ : ℕ) (κ ρ : ℝ) (v : ℕ),
    0 < ℓ → 0 ≤ κ → κ ≤ 1 → 0 ≤ ρ →
    ∀ (t1 t2 : ℝ),
      t1 = (1 + κ) / 2 + (v : ℝ) / ℓ + ρ →
      t2 = (1 + 3 * κ) / 2 - 15 * κ ^ 2 / 4 - 5 * κ / ℓ - ρ →
      t1 < t2 →
      strongFailProb n ℓ κ t1 t2 v ≤
        (ℓ : ℝ) ^ 6 * (2 : ℝ) ^ (-(n : ℤ)) +
          2 * (ℓ : ℝ) ^ 2 *
            Real.exp (-(ρ ^ 2 * (2 : ℝ) ^ n / (2 * (ℓ : ℝ) ^ 2)))

end Qatlib.Concepts.WalshMoment.Forrelation
