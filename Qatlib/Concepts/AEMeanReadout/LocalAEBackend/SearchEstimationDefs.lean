/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram

/-!
# Source search and rational estimation records

This module exposes `s2SourceRound` as the source search round and `s2EstimationReadout` as its
rational label readout interface. `S2SourceRecord` stores a search outcome with two
natural-number ledgers and an optional function assigning rational values to phase labels. These
interfaces support the search and amplitude-estimation constructions of [BrassardEtAl2002].

## Main definitions

* `s2SourceRound`: the source quantum-search round interface.
* `s2EstimationReadout`: rational readout of an amplitude-estimation label.
* `S2SourceRecord`: a search outcome and an optional label readout function.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The stage-two interface to `sourceQSearchRound`, returning an optional marked index and two
natural-number cost ledgers. -/
noncomputable def s2SourceRound (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) : PMF (Option I × ℕ × ℕ) :=
  sourceQSearchRound A hA j₀ S l

/-- The rational label readout `labelReadout` for grid size M and precision b. -/
noncomputable def s2EstimationReadout (M : ℕ) (b : ℕ) (z : Fin M) : ℚ :=
  labelReadout M b z

/-- A record containing a source-search outcome with two cost ledgers and an optional
rational-valued function on the M phase labels. -/
structure S2SourceRecord (M : ℕ) (b : ℕ) (I : Type) where

  outcome : Option I × ℕ × ℕ

  readout : Option (Fin M → ℚ)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
