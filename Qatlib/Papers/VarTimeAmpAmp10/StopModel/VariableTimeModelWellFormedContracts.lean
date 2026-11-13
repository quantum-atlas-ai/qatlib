/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeDefs

/-!
# Fixed stopped-subspace well-formedness contract

`variableTimeModelWellFormed` states preservation of stopped components, monotonicity of stopped
mass, and unitarity of prefix evolution for sequences satisfying `IsVtStage`. Its stage
condition fixes the entire stopped subspace.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `variableTimeModelWellFormed`: preservation, monotonicity, and prefix unitarity specification.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- The proposition that stages fixing the stopped subspace preserve stopped components, yield
nondecreasing stopped mass, and have unitary prefix products. -/
def variableTimeModelWellFormed : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)),
    (∀ U ∈ stages, IsVtStage U) →
    (∀ (U : Matrix (VtSpace C) (VtSpace C) ℂ), IsVtStage U →
      ∀ ψ : QState (VtSpace C),
        Collapse (ApplyGate U ψ) (stoppedSet C) = Collapse ψ (stoppedSet C)) ∧
    (∀ (j₀ : VtSpace C) (k : ℕ), k < stages.length →
      stoppedMass stages j₀ k ≤ stoppedMass stages j₀ (k + 1)) ∧
    (∀ k : ℕ, vtRunMatrix stages k ∈ Matrix.unitaryGroup (VtSpace C) ℂ)

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
