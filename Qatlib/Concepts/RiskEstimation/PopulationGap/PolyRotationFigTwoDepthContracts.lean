/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout
open Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib

def PolyRotationFigTwoDepth : Prop :=
  ∀ (u n : ℕ) (c : ℝ) (fp : Polynomial ℝ),
    (∀ x : Reg n, (riskFigTwoAnglePoly u c fp).eval (figTwoRegEval x : ℝ)
      = 2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ)) + Real.pi/4)) ∧
    (∀ s : ℕ, fp.natDegree ≤ s →
      (riskFigTwoAnglePoly u c fp).natDegree ≤ s*(2*u+1)) ∧
    (∀ s : ℕ, fp.natDegree ≤ s → 1 ≤ n →
      (figTwoProgram (n := n) (s*(2*u+1))
        (fun y => (riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))).length
        ≤ 31 * (s*(2*u+1)+1) * n^(s*(2*u+1)+1))

end Qatlib.Concepts.RiskEstimation.PopulationGap
