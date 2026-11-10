/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyControlledRotation
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

open Qatlib

def figTwoDataList (n : ℕ) : List (Fin n) := List.finRange n

def figTwoRegEval {n : ℕ} (x : Reg n) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => x i = true), (2 : ℕ)^i.val

def figTwoAngle {n : ℕ} (g : Reg n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ)^(S.card - T.card) * g (fun i => decide (i ∈ T))

def figTwoTerms {n : ℕ} (k : ℕ) : List (List (Fin n)) :=
  (figTwoDataList n).sublists.filter (fun l => l.length ≤ k)

def figTwoDataWire (n : ℕ) (i : Fin n) : Fin (n+1+(n-1)) := ⟨i.val, by omega⟩

def figTwoTargetWire (n : ℕ) : Fin (n+1+(n-1)) := ⟨n, by omega⟩

def figTwoWorkWires (n : ℕ) : List (Fin (n+1+(n-1))) :=
  (List.finRange (n-1)).map (fun j => ⟨n+1+j.val, by omega⟩)

noncomputable def figTwoProgram {n : ℕ} (k : ℕ) (g : Reg n → ℝ) :
    List (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (n+1+(n-1))) :=
  figTwoRotationSteps (figTwoTargetWire n) (figTwoWorkWires n)
    ((figTwoTerms k).map (fun l =>
      (l.map (figTwoDataWire n), figTwoAngle g l.toFinset)))

noncomputable def figTwoProgramAngle {n : ℕ} (k : ℕ) (g : Reg n → ℝ) (x : Reg n) : ℝ :=
  (((figTwoTerms k).filter (fun l => l.all x)).map (fun l => figTwoAngle g l.toFinset)).sum

noncomputable def riskSinTaylorPoly (u : ℕ) (c : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (u+1),
    Polynomial.C (((2*j).choose j : ℕ)/((2*j+1 : ℝ)) * c^(2*j)) *
      (Polynomial.X - Polynomial.C (1/2))^(2*j+1)

noncomputable def riskFigTwoAnglePoly (u : ℕ) (c : ℝ) (fp : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (2*c) * (riskSinTaylorPoly u c).comp fp + Polynomial.C (Real.pi/2)

end Qatlib.Concepts.RiskEstimation.PolyRotation
