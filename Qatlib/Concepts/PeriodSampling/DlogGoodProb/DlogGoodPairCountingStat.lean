/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb

open scoped Classical

def DlogGoodPairCounting : Prop :=
  ∀ (p q r : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q →
    ((Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card
        ≥ q / 12) ∧
      ((Finset.univ.filter fun cd : Fin q × Fin q => dlogGoodPair p q r cd.1 cd.2).card
          ≥ q / 12)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
