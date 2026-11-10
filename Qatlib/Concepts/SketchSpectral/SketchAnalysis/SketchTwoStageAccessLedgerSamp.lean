/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchTwoStageAccessLedgerStat
import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
set_option warningAsError false
open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis

theorem sketchTwoStageAccessLedger : SketchTwoStageAccessLedger := by
  intro K C _ _ _ _ r c qs condQ v w
  simp [compactSketchBuild_eq]

end Qatlib.Concepts.SketchSpectral.SketchAnalysis
