/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Matrix

set_option autoImplicit false

section Model

variable {C : Type} [Fintype C] [DecidableEq C]

abbrev VtSpace (C : Type) [Fintype C] : Type := Fin 3 × C

def vtBadFlag : Fin 3 := 0

def vtGoodFlag : Fin 3 := 1

def vtRunningFlag : Fin 3 := 2

def stoppedSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 ≠ vtRunningFlag)

def goodSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 = vtGoodFlag)

def badSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 = vtBadFlag)

def runningSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 = vtRunningFlag)

def IsVtStage (U : Matrix (VtSpace C) (VtSpace C) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (VtSpace C) ℂ ∧
    ∀ p : VtSpace C, p.1 ≠ vtRunningFlag → ∀ q : VtSpace C,
      U q p = if q = p then (1 : ℂ) else 0

noncomputable def vtRunMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (k : ℕ) : Matrix (VtSpace C) (VtSpace C) ℂ :=
  (stages.take k).foldl (fun A U => U * A) 1

noncomputable def vtState (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (k : ℕ) (ψ : QState (VtSpace C)) : QState (VtSpace C) :=
  vtRunMatrix stages k *ᵥ ψ

noncomputable def stoppedMass (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (k : ℕ) : ℝ :=
  MeasureProb (vtState stages k (Ket j₀)) (stoppedSet C)

noncomputable def pstop (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (j : ℕ) : ℝ :=
  stoppedMass stages j₀ (j + 1) - stoppedMass stages j₀ j

noncomputable def psucc (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) : ℝ :=
  MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C)

noncomputable def stopTime (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1)

noncomputable def vtTav (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range stages.length,
    pstop stages j₀ j * (stopTime j) ^ 2)

noncomputable def vtTmax (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) : ℝ :=
  (2 : ℝ) ^ stages.length

def stageDuration (j : ℕ) : ℕ := 2 ^ j

end Model

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
