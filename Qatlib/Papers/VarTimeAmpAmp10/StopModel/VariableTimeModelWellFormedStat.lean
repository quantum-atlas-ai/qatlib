/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.GrowingStopDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

def VariableTimeModelWellFormed : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C),
    GrowingVtLegal stages history →
    (∀ k,(h : k < stages.length) → ∀ ψ : QState (VtSpace C),
      Collapse (ApplyGate stages[k] ψ) (reachedStoppedSet history k)=Collapse ψ (reachedStoppedSet history k)) ∧
    (∀ ψ k,k < stages.length → reachedStoppedMass stages history ψ k ≤ reachedStoppedMass stages history ψ (k+1) ∧
      0 ≤ reachedPstop stages history ψ k) ∧
    (∀ k,vtRunMatrix stages k∈Matrix.unitaryGroup (VtSpace C) ℂ)
end Qatlib.Papers.VarTimeAmpAmp10.StopModel
