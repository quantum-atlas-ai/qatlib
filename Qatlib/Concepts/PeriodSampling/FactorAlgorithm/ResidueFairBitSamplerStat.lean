/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.ResidueFactoringPrograms

/-!
# Fair-bit residue sampler contract

Defines `ResidueFairBitSampler`, the exact counting and cost specification for decoding bit
strings as residues. The contract also bounds the chosen sampler capacity for positive inputs in
the factoring framework associated with [Shor1997].

## Main statements

* `ResidueFairBitSampler`: Specifies unique residue encodings, rejection counts, exact bit cost,
  and capacity bounds.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

/-- Requires one encoding per residue, exactly `2 ^ k - N` rejected strings, and no mass at bit
costs other than `k` when capacity is sufficient; also requires `N ≤ 2 ^ shorResidueBits N <
2 * N` for positive `N`. -/
def ResidueFairBitSampler : Prop :=
  (∀ (N k : ℕ) [NeZero N], N ≤ 2 ^ k →
    (∀ y : ZMod N,
        (Finset.univ.filter fun b : Reg k => decodeResidue N k b = some y).card = 1) ∧
    ((Finset.univ.filter fun b : Reg k => decodeResidue N k b = none).card = 2 ^ k - N) ∧
    (∀ (ω : Reg k) (n : ℕ), n ≠ k → fairBitsCosted k (ω, n) = 0)) ∧
  (∀ N : ℕ, 0 < N →
    N ≤ 2 ^ shorResidueBits N ∧ 2 ^ shorResidueBits N < 2 * N)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
