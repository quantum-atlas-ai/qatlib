/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
open scoped ComplexOrder
set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract
abbrev SourceTwoPointGroup := Multiplicative (ZMod 2)
noncomputable def sourcePlusDensity : Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ :=
  fun _ _ => 1 / 2
end Qatlib.Concepts.HspRecovery.RecordExtract
