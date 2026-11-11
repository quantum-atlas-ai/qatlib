/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DecisionRisk.HarmonicError.GraphPairCertificate

/-! Original scalar shared-axis certificate from OQ #145, beyond the paper's
one-parameter numerical trine example. It has no general Bloch/graph/POVM
representation theorem and no new whole-family A rating. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SeqQsdJeong26.TrineExample
open Qatlib.Foundations.DecisionRisk.HarmonicError

/-- The stated finite risk construction satisfies `shared_axes_scalar_strict` with all displayed hypotheses retained. -/
theorem shared_axes_scalar_strict {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) : c^2 < pairedAxesCost c x y := by
  exact Qatlib.Foundations.DecisionRisk.HarmonicError.pairedAxesCost_strict hc hc1 hball

end Qatlib.Papers.SeqQsdJeong26.TrineExample
