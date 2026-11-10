/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalWordConstruction
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix

noncomputable def l3Unit (delta : ℝ) : ℂ := l3PhaseUnit delta

theorem l3Unit_eq (delta : ℝ) : l3Unit delta = l3PhaseUnit delta := rfl

noncomputable def l3FailureFactor (delta lam : ℝ) : ℝ :=
  1 - 2 * lam + 2 * lam * Real.cos (l3Phase delta)

noncomputable def l3WidthValue (delta : ℝ) : ℝ := (ylcGamma 3 delta) ^ 3

inductive FixedPointAccess where

  | prepA

  | prepAdag

  | markQuery

  | controlQuery (bits : ℕ) (angle : ℝ)

  | goodPhase (bits : ℕ) (angle : ℝ)

def prepAccessCount : List FixedPointAccess → ℕ
  | [] => 0
  | .prepA :: t => prepAccessCount t + 1
  | .prepAdag :: t => prepAccessCount t + 1
  | _ :: t => prepAccessCount t

def queryAccessCount : List FixedPointAccess → ℕ
  | [] => 0
  | .markQuery :: t => queryAccessCount t + 1
  | .controlQuery _ _ :: t => queryAccessCount t + 1
  | _ :: t => queryAccessCount t

def phaseAccessCount : List FixedPointAccess → ℕ
  | [] => 0
  | .controlQuery _ _ :: t => phaseAccessCount t + 1
  | .goodPhase _ _ :: t => phaseAccessCount t + 1
  | _ :: t => phaseAccessCount t

def phaseBitCount : List FixedPointAccess → ℕ
  | [] => 0
  | .controlQuery b _ :: t => phaseBitCount t + b
  | .goodPhase b _ :: t => phaseBitCount t + b
  | _ :: t => phaseBitCount t

noncomputable def iterateAccesses (l : ℕ) (delta : ℝ) (bits : ℕ) (i : ℕ) :
    List FixedPointAccess :=
  [ .markQuery,
    .controlQuery bits (-(wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))),
    .prepA,
    .goodPhase bits (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta)),
    .prepAdag ]

noncomputable def fixedPointAccessWord (l : ℕ) (delta : ℝ) (bits : ℕ) :
    List FixedPointAccess :=
  (List.range l).flatMap fun i => iterateAccesses l delta bits i

noncomputable def FixedPointAccess.matrix (lam : ℝ) : FixedPointAccess →
    Matrix (Fin 2) (Fin 2) ℂ
  | .prepA => 1
  | .prepAdag => 1
  | .markQuery => 1
  | .controlQuery _ angle => targetReflection angle
  | .goodPhase _ angle => -(stateReflection lam angle)

noncomputable def accessWordMatrix (lam : ℝ) : List FixedPointAccess →
    Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | a :: t => accessWordMatrix lam t * a.matrix lam

noncomputable def dyadicAngle (bits : ℕ) (angle : ℝ) : ℝ :=
  (2 * Real.pi * ((Int.floor (angle * (2:ℝ) ^ bits / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ)) /
    (2:ℝ) ^ bits

noncomputable def lcuPrepareState {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (lam : ℝ) : QState (J × Fin 2) :=
  TensorState (Ket j₀) (ampState lam)

noncomputable def lcuSelectOperator {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : Matrix (J × Fin 2) (J × Fin 2) ℂ :=
  publicWordFiber j₀ l delta lam

noncomputable def lcuSuccessProb {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : ℝ :=
  ‖Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
      (lcuSelectOperator j₀ l delta lam *ᵥ lcuPrepareState j₀ lam)‖ ^ 2

noncomputable def lcuConditionalOutput {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : QState (J × Fin 2) :=
  conditionalOutput (fiberTarget j₀)
    (lcuSelectOperator j₀ l delta lam *ᵥ lcuPrepareState j₀ lam)

end Qatlib.Papers.FixedPtSearch14.FixedPoint
