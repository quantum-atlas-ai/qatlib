/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic

namespace Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Spec
def expected : Prop :=
  (∀ (θ : ℝ) (a a_tilde : ℂ) (Z : ℝ) (Z_tilde : ℂ),
  0 ≤ θ →
  θ ≤ 1 →
  ‖a‖ ≤ Z →
  ‖a - a_tilde‖ ≤ (θ / 3) * Z →
  ‖(Z : ℂ) - Z_tilde‖ ≤ (θ / 3) * Z →
  ‖a_tilde / Z_tilde - a / (Z : ℂ)‖ ≤ θ)
end Qatlib.Papers.LowRankMatrix19.SDPTrace.Lemma627Spec
