/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic

namespace Qatlib.Concepts.AmpTransform.ErrorStream.Lemma16Spec
def expected : Prop :=
  (∀ (n L M : ℕ), 0 < L + M → L + M < 2 ^ n →
  let N : ℝ := ((2 ^ n : ℕ) : ℝ);
  let T : ℝ := ((L + M : ℕ) : ℝ);
  let θ : ℝ := Real.arcsin (Real.sqrt (T / N));
  let k : ℕ := Nat.floor (Real.pi / (4 * θ));
  let a_k : ℝ := Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt T;
  let b_k : ℝ := Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (N - T);
  (T / Real.sqrt N) * (a_k - b_k) =
    Real.tan θ * Real.sin (2 * (k : ℝ) * θ))
end Qatlib.Concepts.AmpTransform.ErrorStream.Lemma16Spec
