/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument

/-!
# Imports for local cluster networks

This module brings together counted cluster CZ constructions, tensor Pauli measurement records,
and adaptive cluster-sequence instruments through the imports `CountedClusterCZ`,
`TensorPauliRecords`, and `ClusterSequenceInstrument`. It introduces no additional declarations.

These imports combine circuit composition and measurement-record descriptions for cluster-state
computation, whose one-way model is introduced in [RaussendorfBriegel2001].

## Main imports

* `Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ`: counted cluster CZ
  constructions.
* `Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords`: tensor Pauli records.
* `Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument`: adaptive
  cluster-sequence instruments.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

end Qatlib.Concepts.MbqcFlow.FlowDecision
