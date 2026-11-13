/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchTwoStageAccessLedgerStat
import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch

/-!
# Exact access counts for two-stage sketches

This module proves `SketchTwoStageAccessLedger`: the row sketch construction records `r` sampler
reads and `r` probability reads, and the conditional column construction records `c` of each.
The counts apply to every pair of sample tuples and provide an access ledger for the
sampling-based sketch framework [ChiaEtAl2022].

## Main statements

* `sketchTwoStageAccessLedger`: exact sampler and probability read counts for both stages.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis

/-- For every pair of row and conditional column sample tuples, each compact sketch construction
records sampler and probability read counts equal to its sample count. See [ChiaEtAl2022]. -/
theorem sketchTwoStageAccessLedger : SketchTwoStageAccessLedger := by
  intro K C _ _ _ _ r c qs condQ v w
  simp [compactSketchBuild_eq]

end Qatlib.Concepts.SketchSpectral.SketchAnalysis
