/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace


namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

section
set_option linter.unusedSectionVars false

variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]

set_option maxHeartbeats 0 in

end

section PhaseAdaptiveCompilation
variable {n q : ℕ} [NeZero q] {W H : Type}
  [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H]

end PhaseAdaptiveCompilation

section PhaseAdaptiveLowerBounds
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]

end PhaseAdaptiveLowerBounds

section PhaseKrausCompilation
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]

end PhaseKrausCompilation

section InstrumentNativeQueryStopping
variable {d : ℕ}

end InstrumentNativeQueryStopping

section WeightedSourceAdversaryOptimization
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

end WeightedSourceAdversaryOptimization

section MinimaxGram
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]

variable [DecidableEq X]

end MinimaxGram

section EqualitySdp
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

end EqualitySdp

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
section SpectralEmbedding
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

end SpectralEmbedding

section Compression
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

end Compression

section ComplexCostOptimization
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

end ComplexCostOptimization

section BinaryMixed
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]

end BinaryMixed

section UnboundedSource
variable {n q d : ℕ} [NeZero q] {W : Type} [Fintype W]

end UnboundedSource

end Qatlib.Concepts.AdversaryBounds.AdvDuality
