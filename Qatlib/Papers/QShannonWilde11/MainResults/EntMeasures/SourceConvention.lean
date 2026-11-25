/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux

@[expose] public section


/-!
# Source convention for the `g₂` continuity function

Paper version: **arXiv:1106.1445v8**, [Wilde2017], §11.10, Eqs. (11.252)–(11.257), fixed
PDF p. 359.
<https://arxiv.org/abs/1106.1445>

The Fannes–Audenaert/AFW continuity bounds of §11.10 are stated with the function
`g₂(ε) = (1 + ε) log(1 + ε) − ε log ε`.  The shared model records the doubled-argument
variant `(1 + 2ε) log(1 + 2ε) − 2ε log(2ε)` as
`Qatlib.Papers.QShannonWilde11.MainResults.Model.g2`.  This file fixes the paper's own
normalisation as `g2Source` and records that the model function is exactly the paper's
function at twice the argument, so that either convention can be used downstream.

The continuity bounds themselves are not proved here, and the two functions are only
related through the argument rescaling: `g2` is not the paper's `g₂` at the same argument.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.EntMeasures

open Qatlib.Papers.QShannonWilde11.MainResults.Model

noncomputable section

/-- The paper's `g₂` normalisation `g₂(ε) = (1 + ε) log(1 + ε) − ε log ε` of the
continuity bounds, [Wilde2017], §11.10, Eqs. (11.252)–(11.257). -/
def g2Source (ε : ℝ) : ℝ := (1 + ε) * Real.log (1 + ε) - ε * Real.log ε

/-- The model function `g2` is the paper's `g2Source` at twice its argument, that is
`g2 ε = g₂(2ε)`; the two conventions therefore agree after rescaling `ε ↦ 2ε`. -/
theorem g2_eq_g2Source_two_mul (ε : ℝ) : g2 ε = g2Source (2 * ε) := rfl

/-- At `ε = 0` the paper's `g₂` uses the library convention `log 0 = 0` and vanishes. -/
theorem g2Source_zero : g2Source 0 = 0 := by
  simp [g2Source]

/-- The model function vanishes at `ε = 0` under the same logarithm convention. -/
theorem g2_zero : g2 0 = 0 := by
  simp [g2]

end

end Qatlib.Papers.QShannonWilde11.MainResults.EntMeasures
