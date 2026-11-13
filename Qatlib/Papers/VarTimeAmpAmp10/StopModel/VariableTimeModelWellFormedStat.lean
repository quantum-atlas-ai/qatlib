/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.GrowingStopDefs

/-!
# Growing-history well-formedness contract

`VariableTimeModelWellFormed` specifies the preservation and probability laws of
`GrowingVtLegal` stage sequences. It requires preservation of each already reached stopped
component, nondecreasing reached stopped mass, nonnegative stopping increments, and unitary
prefixes.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `VariableTimeModelWellFormed`: growing-history preservation and mass-accounting specification.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- The proposition that legal growing-history stages preserve reached stopped components, have
nondecreasing reached mass and nonnegative increments, and yield unitary prefix matrices. -/
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
