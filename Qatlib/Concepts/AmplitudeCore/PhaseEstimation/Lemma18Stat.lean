/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Spec
def expected : Prop :=
  (∀ (n : ℕ),
  let N : ℕ := 2 ^ n;
  ∀ (M P : ℕ) (y : Fin N),
    0 < M →
    0 < P →
    (P * y.val) % N ≠ 0 →
    let ω : ℂ := Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I);
    ‖(1 - ω ^ (M * P * y.val)) / (1 - ω ^ (P * y.val))‖ ^ 2 =
      (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
        (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 ∧
    (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
        (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 ≤
      (M : ℝ) ^ 2)
end Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Spec
