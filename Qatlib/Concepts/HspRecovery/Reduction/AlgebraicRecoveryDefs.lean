/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecoveryDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.ReductionCore.CompactPresentation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical

structure RecoveryLedger where

  labelReads : ℕ

  gcdReductions : ℕ

  smithOperations : ℕ

  groupEnumeration : ℕ

def recoveryLedger (p : CompactPresentation) (L : List (FactorLabel p.smith))
    (ops : ℕ) : RecoveryLedger where
  labelReads := (compactDecodeLedger p.smith L).labelReads
  gcdReductions := (compactDecodeLedger p.smith L).gcdReductions
  smithOperations := ops
  groupEnumeration := (compactDecodeLedger p.smith L).groupEnumeration

end Qatlib.Concepts.HspRecovery.ReductionCore
