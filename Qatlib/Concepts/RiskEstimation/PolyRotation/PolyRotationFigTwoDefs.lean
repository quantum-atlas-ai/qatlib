/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyControlledRotation
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs

/-!
# Figure 2 angle expansion and register layout

This module defines binary register evaluation, subset coefficients, control terms, and the
data, target, and work-wire layout. It also represents the truncated payoff angle as a
polynomial through `riskSinTaylorPoly` and `riskFigTwoAnglePoly`.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `figTwoAngle`: The alternating powerset sum defining the subset coefficient of a
  register-angle function.
* `riskFigTwoAnglePoly`: The doubled shifted payoff-angle polynomial `2 * c * (riskSinTaylorPoly
  u c).comp fp + π / 2`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib

/-- The ordered list of all data-wire indices. -/
def figTwoDataList (n : ℕ) : List (Fin n) := List.finRange n

/-- The natural number represented by a Boolean register, with wire `i` carrying weight `2 ^
i.val`. -/
def figTwoRegEval {n : ℕ} (x : Reg n) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => x i = true), (2 : ℕ)^i.val

/-- The alternating powerset sum defining the subset coefficient of a register-angle function. -/
def figTwoAngle {n : ℕ} (g : Reg n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ)^(S.card - T.card) * g (fun i => decide (i ∈ T))

/-- The data-wire sublists of length at most `k` used as control subsets. -/
def figTwoTerms {n : ℕ} (k : ℕ) : List (List (Fin n)) :=
  (figTwoDataList n).sublists.filter (fun l => l.length ≤ k)

/-- The embedding of a data-wire index into the expanded Figure 2 register. -/
def figTwoDataWire (n : ℕ) (i : Fin n) : Fin (n+1+(n-1)) := ⟨i.val, by omega⟩

/-- The target-flag wire immediately following the data wires. -/
def figTwoTargetWire (n : ℕ) : Fin (n+1+(n-1)) := ⟨n, by omega⟩

/-- The ordered list of `n - 1` work wires following the target flag. -/
def figTwoWorkWires (n : ℕ) : List (Fin (n+1+(n-1))) :=
  (List.finRange (n-1)).map (fun j => ⟨n+1+j.val, by omega⟩)

/-- The original Figure 2 word assembled from selected data-control subsets and their
subset-angle coefficients. -/
noncomputable def figTwoProgram {n : ℕ} (k : ℕ) (g : Reg n → ℝ) :
    List (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (n+1+(n-1))) :=
  figTwoRotationSteps (figTwoTargetWire n) (figTwoWorkWires n)
    ((figTwoTerms k).map (fun l =>
      (l.map (figTwoDataWire n), figTwoAngle g l.toFinset)))

/-- The sum of subset-angle coefficients whose control bits are all true in the input register. -/
noncomputable def figTwoProgramAngle {n : ℕ} (k : ℕ) (g : Reg n → ℝ) (x : Reg n) : ℝ :=
  (((figTwoTerms k).filter (fun l => l.all x)).map (fun l => figTwoAngle g l.toFinset)).sum

/-- The polynomial representation of the truncated odd payoff-angle expansion. -/
noncomputable def riskSinTaylorPoly (u : ℕ) (c : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (u+1),
    Polynomial.C (((2*j).choose j : ℕ)/((2*j+1 : ℝ)) * c^(2*j)) *
      (Polynomial.X - Polynomial.C (1/2))^(2*j+1)

/-- The doubled shifted payoff-angle polynomial `2 * c * (riskSinTaylorPoly u c).comp fp + π /
2`. -/
noncomputable def riskFigTwoAnglePoly (u : ℕ) (c : ℝ) (fp : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (2*c) * (riskSinTaylorPoly u c).comp fp + Polynomial.C (Real.pi/2)

end Qatlib.Concepts.RiskEstimation.PolyRotation
