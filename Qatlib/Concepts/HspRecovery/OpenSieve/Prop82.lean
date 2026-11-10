/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.TwirlingCounterexample
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open scoped ComplexOrder

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Prop82

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.RecordExtract

def SourcePurelyHInvariantConversion (G : Type*) [Group G] [Fintype G] : Prop :=
  ∃ convert : Matrix G G ℂ → Matrix G G ℂ,
    ∀ (H : Subgroup G) (rho : Matrix G G ℂ),
      rho.PosSemidef → rho.trace = 1 →
      sourceFixedProjector G H * rho * sourceFixedProjector G H = rho →
      convert rho = sourceCosetDensity G H

theorem prop82_universal_conversion_refuted :
    ¬ SourcePurelyHInvariantConversion SourceTwoPointGroup := by
  intro h
  exact sourceTwirlingCounterexample.2.2.2.2.2 h

theorem prop82_counterexample : TwirlingCounterexample :=
  sourceTwirlingCounterexample

end Qatlib.Concepts.HspRecovery.OpenSieve.Prop82
