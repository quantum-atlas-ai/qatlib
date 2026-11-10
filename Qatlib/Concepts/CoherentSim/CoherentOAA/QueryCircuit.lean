/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix

inductive AdjointStep (H : Type*) where
  | gate : Matrix H H ℂ → AdjointStep H
  | forward : AdjointStep H
  | backward : AdjointStep H

def swapQueries {H : Type*} : AdjointStep H → AdjointStep H
  | .gate V => .gate V
  | .forward => .backward
  | .backward => .forward

def adjointQueryCount {H : Type*} : List (AdjointStep H) → ℕ
  | [] => 0
  | .gate _ :: cs => adjointQueryCount cs
  | .forward :: cs => adjointQueryCount cs + 1
  | .backward :: cs => adjointQueryCount cs + 1

def adjointGateCount {H : Type*} : List (AdjointStep H) → ℕ
  | [] => 0
  | .gate _ :: cs => adjointGateCount cs + 1
  | .forward :: cs => adjointGateCount cs
  | .backward :: cs => adjointGateCount cs

variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def instructionMatrix (U : Matrix H H ℂ) : AdjointStep H → Matrix H H ℂ
  | .gate V => V
  | .forward => U
  | .backward => Uᴴ

noncomputable def evaluate (U : Matrix H H ℂ) : List (AdjointStep H) → Matrix H H ℂ
  | [] => 1
  | c :: cs => instructionMatrix U c * evaluate U cs

theorem evaluate_swapQueries (U : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate U (cs.map swapQueries) = evaluate Uᴴ cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [evaluate, instructionMatrix, swapQueries, ih]

omit [Fintype H] [DecidableEq H] in

@[simp] theorem adjointQueryCount_swapQueries (cs : List (AdjointStep H)) :
    adjointQueryCount (cs.map swapQueries) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [swapQueries, adjointQueryCount, ih]

omit [Fintype H] [DecidableEq H] in

@[simp] theorem adjointGateCount_swapQueries (cs : List (AdjointStep H)) :
    adjointGateCount (cs.map swapQueries) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [swapQueries, adjointGateCount, ih]

noncomputable def compileQSVT (P Q : Matrix H H ℂ) (base : ℂ) :
    List ℂ → List (AdjointStep H)
  | [] => [.gate (phaseRotation Q base)]
  | z :: zs => .gate (phaseRotation Q z) :: .forward ::
      (compileQSVT Q P base zs).map swapQueries

theorem evaluate_compileQSVT (U P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    evaluate U (compileQSVT P Q base zs) = phasedAlternating U P Q base zs := by
  induction zs generalizing U P Q with
  | nil => simp [compileQSVT, evaluate, instructionMatrix, phasedAlternating]
  | cons z zs ih =>
    simp [compileQSVT, evaluate, instructionMatrix, evaluate_swapQueries, ih,
      phasedAlternating, Matrix.mul_assoc]

omit [Fintype H] in

theorem queryCount_compileQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointQueryCount (compileQSVT P Q base zs) = zs.length := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileQSVT, adjointQueryCount, ih]

omit [Fintype H] in

theorem gateCount_compileQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointGateCount (compileQSVT P Q base zs) = zs.length + 1 := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileQSVT, adjointGateCount, ih]

end Qatlib.Concepts.CoherentSim.CoherentOAA
