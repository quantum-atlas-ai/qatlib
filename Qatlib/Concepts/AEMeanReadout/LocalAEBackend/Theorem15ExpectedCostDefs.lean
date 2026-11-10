/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open scoped Classical

noncomputable def basicApproxCountTotalCost (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : ℕ :=
  (∑ l : Fin (basicApproxCountLoopCap N),
    if l.val < basicApproxCountStop N ω then 2*2^l.val else 0) +
  basicApproxCountFinalM ε (basicApproxCountStop N ω)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
