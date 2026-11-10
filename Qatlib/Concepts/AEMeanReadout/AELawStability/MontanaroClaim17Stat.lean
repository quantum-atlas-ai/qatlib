/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Qatlib.Concepts.AEMeanReadout.AELawStability

def MontanaroClaim17 : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    |Real.arcsin x - Real.arcsin y| ≤ (Real.pi / 2) * Real.sqrt |x ^ 2 - y ^ 2|

end Qatlib.Concepts.AEMeanReadout.AELawStability
