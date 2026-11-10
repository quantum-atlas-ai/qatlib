/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogCRTRecovery

open Qatlib

def DlogCrtRecovery : Prop :=
  ∀ (p q r : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → r < p - 1 →
    ∀ (t : ℕ) (c : Fin t → Fin q) (d' : Fin t → ℤ),
      (∀ i, (d' i + r * dlogCprime p q (c i) : ℤ)
          % ((p - 1 : ℕ) : ℤ) = 0) →
      (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ p - 1 → 18 < ℓ →
          ∃ i, ¬ (ℓ : ℤ) ∣ dlogCprime p q (c i)) →
      ∀ r' : ℕ, r' < p - 1 →
        (∀ i, (d' i + r' * dlogCprime p q (c i) : ℤ)
            % ((p - 1 : ℕ) : ℤ) = 0) →
        (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ p - 1 → ℓ ≤ 18 →
            r' % ℓ ^ ((p - 1).factorization ℓ)
              = r % ℓ ^ ((p - 1).factorization ℓ)) →
        r' = r

end Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
