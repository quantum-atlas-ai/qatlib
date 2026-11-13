/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms

/-!
# Fair-bit unit sampler contract

Defines `FairBitUnitSampler`, recording the unique bit-string encoding of each unit, the number
of rejected strings, and the support of the bit-cost distribution. These properties specify the
unit sampler used in the factoring probability model associated with [Shor1997].

## Main statements

* `FairBitUnitSampler`: Specifies exact unit-decoding counts and bit-cost support.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

/-- For positive bit width and sufficient capacity, requires each unit to have exactly one
encoding, exactly `2 ^ k - Fintype.card (ZMod N)ˣ` strings to be rejected, and costed
sampling mass to vanish at every cost other than `k`. -/
def FairBitUnitSampler : Prop :=
  ∀ (N k : ℕ) [NeZero N], 0 < k → Fintype.card (ZMod N)ˣ ≤ 2 ^ k →
    (∀ u : (ZMod N)ˣ,
        (Finset.univ.filter fun b : Reg k => decodeUnit N k b = some u).card = 1) ∧
      ((Finset.univ.filter fun b : Reg k => decodeUnit N k b = none).card
          = 2 ^ k - Fintype.card (ZMod N)ˣ) ∧
      (∀ (ω : Reg k) (n : ℕ), n ≠ k → fairBitsCosted k (ω, n) = 0)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
