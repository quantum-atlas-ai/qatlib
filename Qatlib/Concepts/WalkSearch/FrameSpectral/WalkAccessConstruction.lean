/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionDefs

/-!
# Walk access construction interface

This module imports `WalkAccessConstructionDefs`, exposing the lazy matching kernel, finite
setup, update, and check words, and `HasPaidWalkAccess`. It provides a common import point for
the finite gate access construction supporting the walk framework of [Szegedy2004].

## Main definitions

* `lazyMatchingKernel`: The kernel determined by agreement below the top register bit.
* `HasPaidWalkAccess`: Finite gate access semantics and resource bounds.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.WalkSearch.CountedWalk

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open scoped Classical BigOperators

universe u v

end Qatlib.Concepts.WalkSearch.FrameSpectral
