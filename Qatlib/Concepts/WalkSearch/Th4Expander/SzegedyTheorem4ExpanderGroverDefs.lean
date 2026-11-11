/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS

/-!
# Expander detection search length

This module defines `expanderSearchLength` as the natural-number ceiling of `1000 * sqrt (n /
δ)`. The parameter is used to index detection times for a chain with size `n` and gap parameter
`δ`.

The square-root size-to-gap scale is the one used in the walk-detection framework [Szegedy2004].

## Main statements

* `expanderSearchLength`: the integer detection horizon.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Qatlib.Concepts.WalkSearch.Th4Expander

/-- The detection search length `ceil (1000 * sqrt (n / δ))`. -/
noncomputable def expanderSearchLength (n : ℕ) (δ : ℝ) : ℕ :=
  Nat.ceil (1000 * Real.sqrt ((n : ℝ) / δ))
end Qatlib.Concepts.WalkSearch.Th4Expander
