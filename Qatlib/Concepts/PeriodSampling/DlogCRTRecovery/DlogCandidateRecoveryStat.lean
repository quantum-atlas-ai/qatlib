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

namespace Qatlib.Concepts.PeriodSampling.DlogCRTRecovery

def DlogCandidateRecovery : Prop :=
  ∀ (p q r : ℕ), Nat.Prime p → 3 ≤ p → (p : ℕ) < q → r < p - 1 →
    ∀ c d : Fin q, dlogGoodPair p q r c d →
      (∃ dprime : ℤ,
          |((dprime : ℝ) - ((d : ℕ) * (p - 1) : ℝ) / (q : ℝ))| ≤ 1 / 2 ∧
          ((dprime + r * dlogCprime p q c : ℤ) : ℤ) % ((p - 1 : ℕ) : ℤ) = 0 ∧
          (Nat.gcd (dlogCprime p q c).natAbs (p - 1) = 1 →
            ∃ r' : ℕ, r' < p - 1 ∧
              ((r' : ℤ) * dlogCprime p q c + dprime) % ((p - 1 : ℕ) : ℤ) = 0 ∧
              (r' : ℤ) ≡ (r : ℤ) [ZMOD ((p - 1 : ℕ) : ℤ)]))

end Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
