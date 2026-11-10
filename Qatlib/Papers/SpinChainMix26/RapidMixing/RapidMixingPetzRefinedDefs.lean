/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs

namespace Qatlib.Papers.SpinChainMix26.RapidMixing
namespace NEXT

open Matrix Qatlib
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable def ellStar (η : InfluenceProfile) : ℕ := Nat.ceil (aEta η) + 1

structure PetzCostLedger where

  blockUpdates : ℕ

  statePreparations : ℕ

  inversePreparations : ℕ

  angleGates : ℕ

  classicalBits : ℕ

noncomputable def petzCostLedger (blocks angleGates classicalBits : ℕ) : PetzCostLedger :=
  { blockUpdates := blocks
    statePreparations := blocks
    inversePreparations := blocks
    angleGates := blocks * angleGates
    classicalBits := blocks * classicalBits }

end NEXT
end Qatlib.Papers.SpinChainMix26.RapidMixing
