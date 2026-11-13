/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoModelCorrected

/-!
# Specification of polynomial payoff circuit bounds

This module states `PolyRotationFigTwoDepthCorrected`, connecting the evaluation and degree of
the composed payoff-angle polynomial to a bound on the corrected Figure 2 program length.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `PolyRotationFigTwoDepthCorrected`: The proposition that the payoff-angle polynomial evaluates
  to the intended doubled shifted angle, has degree at most `s * (2 * u + 1)` when `fp` has
  degree at most `s`, and yields the stated corrected circuit-length bound for `n ≥ 1`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib

/-- The proposition that the payoff-angle polynomial evaluates to the intended doubled shifted
angle, has degree at most `s * (2 * u + 1)` when `fp` has degree at most `s`, and yields the
stated corrected circuit-length bound for `n ≥ 1`. -/
def PolyRotationFigTwoDepthCorrected : Prop :=
  ∀ (u n : ℕ) (c : ℝ) (fp : Polynomial ℝ),
    (∀ x : Reg n, (riskFigTwoAnglePoly u c fp).eval (figTwoRegEval x : ℝ)
      = 2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ)) + Real.pi/4)) ∧
    (∀ s : ℕ, fp.natDegree ≤ s →
      (riskFigTwoAnglePoly u c fp).natDegree ≤ s*(2*u+1)) ∧
    (∀ s : ℕ, fp.natDegree ≤ s → 1 ≤ n →
      (figTwoProgramCorrected (n := n) (s*(2*u+1))
        (fun y => (riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))).length
        ≤ 31 * (s*(2*u+1)+1) * n^(s*(2*u+1)+1))

end Qatlib.Concepts.RiskEstimation.PolyRotation
