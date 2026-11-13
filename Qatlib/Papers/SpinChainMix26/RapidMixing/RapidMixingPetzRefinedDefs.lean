/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

/-!
# Block-length choice and Petz cost ledger

This module supplies auxiliary definitions for the formalization of [Kim2026]. The block length
`ellStar η` is the natural ceiling of `aEta η` plus one, and `PetzCostLedger` records update,
preparation, inverse-preparation, angle-gate, and classical-bit counts.

## Main definitions

* `ellStar`: the chosen influence-dependent block length.
* `petzCostLedger`: counts with one update and each preparation per block, and multiplicative
  angle-gate and classical-bit totals.

## References

* [Kim, 2026][Kim2026]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs

namespace Qatlib.Papers.SpinChainMix26.RapidMixing
namespace NEXT

open Matrix Qatlib
open scoped BigOperators ComplexOrder

set_option autoImplicit false

/-- The block length `Nat.ceil (aEta η) + 1`, chosen above the influence constant. -/
noncomputable def ellStar (η : InfluenceProfile) : ℕ := Nat.ceil (aEta η) + 1

/-- Natural-number counts of block updates, state preparations, inverse preparations, angle
gates, and classical bits. -/
structure PetzCostLedger where

  blockUpdates : ℕ

  statePreparations : ℕ

  inversePreparations : ℕ

  angleGates : ℕ

  classicalBits : ℕ

/-- Constructs a ledger with one update and each preparation per block, scaling angle-gate and
classical-bit counts by the number of blocks. -/
noncomputable def petzCostLedger (blocks angleGates classicalBits : ℕ) : PetzCostLedger :=
  { blockUpdates := blocks
    statePreparations := blocks
    inversePreparations := blocks
    angleGates := blocks * angleGates
    classicalBits := blocks * classicalBits }

end NEXT
end Qatlib.Papers.SpinChainMix26.RapidMixing
