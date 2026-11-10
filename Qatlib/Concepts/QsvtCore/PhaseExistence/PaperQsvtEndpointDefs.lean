/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvtDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.SsvtDefs
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib
open Qatlib

structure SourceWordLedger where

  dataQueries : ℕ

  projectorNots : ℕ

  phaseGates : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

def paperOddWordLedger (d : ℕ) : SourceWordLedger :=
  { dataQueries := d
    projectorNots := 2 * d
    phaseGates := d
    peakWorkspace := 1 }

def paperEvenWordLedger (d : ℕ) : SourceWordLedger :=
  { dataQueries := d
    projectorNots := 2 * d
    phaseGates := d
    peakWorkspace := 1 }

def paperLedger (dataQueries projectorNots phaseGates peakWorkspace : ℕ) :
    SourceWordLedger :=
  { dataQueries := dataQueries
    projectorNots := projectorNots
    phaseGates := phaseGates
    peakWorkspace := peakWorkspace }

end Qatlib.Concepts.QsvtCore.PhaseExistence
