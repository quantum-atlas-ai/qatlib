/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoModelCorrected
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

open Matrix

def PolyRotationFigTwoCorrected : Prop :=
  ∀ (n k : ℕ) (p : Polynomial ℝ), p.natDegree ≤ k →
    let g : Reg n → ℝ := fun y => p.eval (figTwoRegEval y : ℝ)
    let embed : Reg n → Bool → Reg (n+1+(n-1)) :=
      fun x b => (multiKnownSplit n).symm ((x, b), fun _ => false)
    ((∀ x : Reg n, figTwoProgramAngle k g x = p.eval (figTwoRegEval x : ℝ))) ∧
    (∀ x : Reg n,
      Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
        (reflectionCompile (figTwoProgramCorrected k g))
        (Ket (embed x false)) =
      ∑ b : Bool,
        ((qubitEulerRotation (p.eval (figTwoRegEval x : ℝ))) *ᵥ Ket false) b •
          Ket (embed x b)) ∧
    ((figTwoProgramCorrected k g).length = ((figTwoTerms (n := n) k).map (fun l => multiKnownCost l.length)).sum) ∧
    (1 ≤ n → (figTwoProgramCorrected k g).length ≤ 31 * (k+1) * n^(k+1))

end Qatlib.Concepts.RiskEstimation.PolyRotation
