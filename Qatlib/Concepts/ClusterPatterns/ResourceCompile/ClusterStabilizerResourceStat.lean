/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.IsingClusterPulseCompilationStat

/-!
# Cluster stabilizer resource specification

`ClusterStabilizerResource` packages normalization, stabilizer eigenvalues, and frame-word
transport for a finite ordered graph. It distinguishes the incoming-parity eigenvalues of
`sourceResource` from the positive stabilizer eigenvalues of `czResource`, following the
graph-resource setting of [RaussendorfBriegel2000].

## Main statements

* `ClusterStabilizerResource`: the source and CZ resource properties and their frame-word
  relation.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.ResourceCompile
open Qatlib

/-- The proposition that ordered graph source and CZ resources are normalized, have the
specified stabilizer eigenvalues, and are related by execution of the frame word. -/
def ClusterStabilizerResource : Prop :=
  ∀ (n : ℕ) (edges : Finset (Fin n × Fin n)),
    (∀ e ∈ edges, e.1 < e.2) →
    Normalized (sourceResource edges) ∧
    (∀ v : Fin n, ApplyGate (stabilizer edges v) (sourceResource edges) =
      (if incomingOdd edges v then (-1 : ℂ) else 1) • sourceResource edges) ∧
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (frameWord edges) (sourceResource edges)
      = czResource edges ∧
    Normalized (czResource edges) ∧
    (∀ v : Fin n, ApplyGate (stabilizer edges v) (czResource edges) = czResource edges)

end Qatlib.Concepts.ClusterPatterns.ResourceCompile
