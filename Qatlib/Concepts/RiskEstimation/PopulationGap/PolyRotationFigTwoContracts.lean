/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDefs

/-!
# Polynomial controlled rotation contract

This module defines `PolyRotationFigTwo`, a specification connecting polynomial evaluation on a
Boolean register to the action of the compiled controlled rotation program. It also specifies
the exact sum of multi control costs and a polynomial word length bound, providing a circuit
contract for the risk rotation construction associated with [WoernerEgger2019].

## Main definition

* `PolyRotationFigTwo`: polynomial angle recovery, embedded basis state execution, and
  reflection word length requirements.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Matrix

/-- Specifies exact polynomial angles and embedded Euler rotation action for the compiled
program, together with its exact cost sum and the length bound `31 * (k + 1) * n ^ (k + 1)`
for positive `n`. -/
def PolyRotationFigTwo : Prop :=
  ∀ (n k : ℕ) (p : Polynomial ℝ), p.natDegree ≤ k →
    let g : Reg n → ℝ := fun y => p.eval (figTwoRegEval y : ℝ)
    let embed : Reg n → Bool → Reg (n+1+(n-1)) :=
      fun x b => (multiKnownSplit n).symm ((x, b), fun _ => false)
    ((∀ x : Reg n, figTwoProgramAngle k g x = p.eval (figTwoRegEval x : ℝ))) ∧
    (∀ x : Reg n,
      Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
        (reflectionCompile (figTwoProgram k g))
        (Ket (embed x false)) =
      ∑ b : Bool,
        ((qubitEulerRotation (p.eval (figTwoRegEval x : ℝ))) *ᵥ Ket false) b •
          Ket (embed x b)) ∧
    ((figTwoProgram k g).length = ((figTwoTerms (n := n) k).map (fun l => multiKnownCost l.length)).sum) ∧
    (1 ≤ n → (figTwoProgram k g).length ≤ 31 * (k+1) * n^(k+1))

end Qatlib.Concepts.RiskEstimation.PopulationGap
