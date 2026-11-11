/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecoveryDefs

/-!
# Resource ledger for algebraic recovery

`RecoveryLedger` records label reads, gcd reductions, Smith operations, and group enumeration.
The constructor `recoveryLedger` combines the compact decoder ledger with a supplied
Smith-operation count for a compact presentation. See [Lomont2004] for the mathematical
background.

## Main statements

* `RecoveryLedger`: the four algebraic recovery counters.
* `recoveryLedger`: assemble counters from compact decoding.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.ReductionCore.CompactPresentation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical

/-- Natural number counters for label reads, gcd reductions, Smith operations, and group
enumeration. -/
structure RecoveryLedger where

  labelReads : ℕ

  gcdReductions : ℕ

  smithOperations : ℕ

  groupEnumeration : ℕ

/-- Combine the compact decoding ledger with a supplied Smith-operation count. -/
def recoveryLedger (p : CompactPresentation) (L : List (FactorLabel p.smith))
    (ops : ℕ) : RecoveryLedger where
  labelReads := (compactDecodeLedger p.smith L).labelReads
  gcdReductions := (compactDecodeLedger p.smith L).gcdReductions
  smithOperations := ops
  groupEnumeration := (compactDecodeLedger p.smith L).groupEnumeration

end Qatlib.Concepts.HspRecovery.ReductionCore
