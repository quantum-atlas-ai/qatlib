/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Qatlib.Concepts.HspRecovery.RecordExtract.TwirlingCounterexampleAuxiliary

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.RecordExtract
open scoped ComplexOrder
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

def TwirlingCounterexample : Prop := by
  classical
  exact
  sourcePlusDensity.PosSemidef ∧ sourcePlusDensity.trace = 1 ∧
    sourceFixedProjector SourceTwoPointGroup ⊥ * sourcePlusDensity *
      sourceFixedProjector SourceTwoPointGroup ⊥ = sourcePlusDensity ∧
    sourceRightTwirl SourceTwoPointGroup sourcePlusDensity = sourcePlusDensity ∧
    sourcePlusDensity ≠ sourceCosetDensity SourceTwoPointGroup ⊥ ∧
    ¬ ∃ convert : Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ →
        Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ,
      ∀ (H : Subgroup SourceTwoPointGroup) (rho : Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ),
        rho.PosSemidef → rho.trace = 1 →
          sourceFixedProjector SourceTwoPointGroup H * rho *
            sourceFixedProjector SourceTwoPointGroup H = rho →
          convert rho = sourceCosetDensity SourceTwoPointGroup H

end Qatlib.Concepts.HspRecovery.ReductionCore
