/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch

/-!
# Statement of the two-stage sketch access ledger

This module defines `SketchTwoStageAccessLedger`, recording exact read counts for compact row
and conditional column sketch construction. Each stage uses one sampler read and one probability
read per sample, so its two recorded counts equal its sample count. These counts support access
accounting for sampling-based matrix arithmetic [ChiaEtAl2022].

## Main statements

* `SketchTwoStageAccessLedger`: the four exact read-count identities.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis

open Matrix

/-- The statement that row and conditional column compact sketch constructions record sampler
and probability read counts `r` and `c`, respectively. -/
def SketchTwoStageAccessLedger : Prop :=
  ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (r c : ℕ) (qs : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist K)
    (condQ : (Fin r → K) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist C)
    (v : Fin r → K) (w : Fin c → C),
    (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchBuild qs r v).2.1 = r ∧
    (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchBuild qs r v).2.2 = r ∧
    (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchBuild (condQ v) c w).2.1 = c ∧
    (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchBuild (condQ v) c w).2.2 = c

end Qatlib.Concepts.SketchSpectral.SketchAnalysis
