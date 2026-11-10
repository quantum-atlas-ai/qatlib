/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.TaylorDiscardSegment
import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator ComplexOrder

set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 800000

namespace Qatlib.Papers.TruncTaylor14.DiscardCore

def sourceDiscardCutoffKey (r k : ℕ) : ℕ :=
  factorialTaylorCutoff (factorialTaylorPrecision r k)
end Qatlib.Papers.TruncTaylor14.DiscardCore
