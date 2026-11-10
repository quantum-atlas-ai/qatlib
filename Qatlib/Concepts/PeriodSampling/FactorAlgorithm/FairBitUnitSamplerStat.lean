/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

def FairBitUnitSampler : Prop :=
  ∀ (N k : ℕ) [NeZero N], 0 < k → Fintype.card (ZMod N)ˣ ≤ 2 ^ k →
    (∀ u : (ZMod N)ˣ,
        (Finset.univ.filter fun b : Reg k => decodeUnit N k b = some u).card = 1) ∧
      ((Finset.univ.filter fun b : Reg k => decodeUnit N k b = none).card
          = 2 ^ k - Fintype.card (ZMod N)ˣ) ∧
      (∀ (ω : Reg k) (n : ℕ), n ≠ k → fairBitsCosted k (ω, n) = 0)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
