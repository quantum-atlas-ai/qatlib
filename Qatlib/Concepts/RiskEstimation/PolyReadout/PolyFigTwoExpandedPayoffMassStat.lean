/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix
open scoped Classical BigOperators

def PolyFigTwoExpandedPayoffMass : Prop :=
  ∀ (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n) (u : ℕ) (c : ℝ) (fp : Polynomial ℝ),
    A ∈ Matrix.unitaryGroup (Reg n) ℂ →
    MeasureProb (figTwoExpandedPreparation n A u c fp*ᵥKet (figTwoStart n j))
      (figTwoGoodSet n) =
      ∑ x, BornProb (A*ᵥKet j) x*
        Real.sin (c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4)^2

end Qatlib.Concepts.RiskEstimation.PolyReadout
