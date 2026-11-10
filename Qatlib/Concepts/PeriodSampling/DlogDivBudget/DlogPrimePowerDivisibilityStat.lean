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

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open scoped Classical

def DlogPrimePowerDivisibility : Prop :=
  ∀ (p q : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → q < 2 * p →
    (∀ c₁ c₂ : Fin q, dlogSmallResidue p q c₁ → dlogSmallResidue p q c₂ →
        dlogCprime p q c₁ = dlogCprime p q c₂ → c₁ = c₂) ∧
    (∀ c : Fin q, dlogSmallResidue p q c →
        0 ≤ dlogCprime p q c ∧ dlogCprime p q c ≤ (p - 1 : ℕ)) ∧
    (∀ w : ℕ, 2 ≤ w → w ∣ p - 1 →
        (Finset.univ.filter fun c : Fin q =>
            dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c).card
          ≤ (p - 1) / w + 1)

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
