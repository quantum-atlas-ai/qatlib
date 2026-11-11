/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvtDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.SsvtDefs

/-!
# Source-word resource ledgers

This module defines `SourceWordLedger` and aggregate ledger constructors for the source QSVT
words associated with [GilyenSuLowWiebe2019]. The fields record total data queries,
projector-controlled NOTs, phase gates, and peak workspace.

Both `paperOddWordLedger` and `paperEvenWordLedger` assign counts `d`, `2d`, `d`, and one,
respectively. `paperLedger` constructs the same record from arbitrary supplied counts.

## Main statements

* `SourceWordLedger`: the four resource fields.
* `paperOddWordLedger` and `paperEvenWordLedger`: the source-word count formulas.
* `paperLedger`: construction from explicit counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib
open Qatlib

/-- A record of total data queries, projector-controlled NOTs, phase gates, and peak workspace
for a source word. -/
structure SourceWordLedger where

  dataQueries : ℕ

  projectorNots : ℕ

  phaseGates : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

/-- The odd source-word ledger with `d` data queries, `2d` projector-controlled NOTs, `d` phase
gates, and peak workspace one. -/
def paperOddWordLedger (d : ℕ) : SourceWordLedger :=
  { dataQueries := d
    projectorNots := 2 * d
    phaseGates := d
    peakWorkspace := 1 }

/-- The even source-word ledger with `d` data queries, `2d` projector-controlled NOTs, `d` phase
gates, and peak workspace one. -/
def paperEvenWordLedger (d : ℕ) : SourceWordLedger :=
  { dataQueries := d
    projectorNots := 2 * d
    phaseGates := d
    peakWorkspace := 1 }

/-- Constructs a source-word ledger from its four resource counts. -/
def paperLedger (dataQueries projectorNots phaseGates peakWorkspace : ℕ) :
    SourceWordLedger :=
  { dataQueries := dataQueries
    projectorNots := projectorNots
    phaseGates := phaseGates
    peakWorkspace := peakWorkspace }

end Qatlib.Concepts.QsvtCore.PhaseExistence
