/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def s2SourceRound (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) : PMF (Option I × ℕ × ℕ) :=
  sourceQSearchRound A hA j₀ S l

noncomputable def s2EstimationReadout (M : ℕ) (b : ℕ) (z : Fin M) : ℚ :=
  labelReadout M b z

structure S2SourceRecord (M : ℕ) (b : ℕ) (I : Type) where

  outcome : Option I × ℕ × ℕ

  readout : Option (Fin M → ℚ)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
