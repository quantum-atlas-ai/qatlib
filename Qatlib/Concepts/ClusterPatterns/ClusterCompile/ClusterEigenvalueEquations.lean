/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ResourceCompile.ClusterStabilizerResourceQuan

/-!
# Cluster stabilizer eigenvalue equations

This module exposes stabilizer equations for graph resources with ordered edges, following the
cluster-state description in [RaussendorfBriegel2000]. The source resource has signs determined
by `incomingOdd`, and executing `frameWord` converts it to the normalized controlled-Z resource
with positive stabilizer eigenvalues.

## Main statements

* `cluster_eigenvalue_equations`: Collects normalization, source stabilizer signs, frame
  conversion, and controlled-Z stabilizer equations.
* `cluster_stabilizer_eigenvalue`: Extracts the signed source-resource eigenvalue equation for
  one vertex.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ClusterPatterns.ResourceCompile

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile

open Qatlib

/-- For ordered graph edges, the source and controlled-Z resources are normalized and satisfy
their respective stabilizer equations, with `frameWord` converting the source resource to
the controlled-Z resource; see [RaussendorfBriegel2000]. -/
theorem cluster_eigenvalue_equations (n : ℕ) (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) :
    Normalized (sourceResource edges) ∧
    (∀ v : Fin n, ApplyGate (stabilizer edges v) (sourceResource edges) =
      (if incomingOdd edges v then (-1 : ℂ) else 1) • sourceResource edges) ∧
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (frameWord edges) (sourceResource edges) = czResource edges ∧
    Normalized (czResource edges) ∧
    (∀ v : Fin n, ApplyGate (stabilizer edges v) (czResource edges) = czResource edges) :=
  clusterStabilizerResource n edges horder

/-- The source resource is an eigenvector of each graph stabilizer, with sign determined by the
parity of incoming edges; see [RaussendorfBriegel2000]. -/
theorem cluster_stabilizer_eigenvalue (n : ℕ) (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) (v : Fin n) :
    ApplyGate (stabilizer edges v) (sourceResource edges) =
      (if incomingOdd edges v then (-1 : ℂ) else 1) • sourceResource edges :=
  (clusterStabilizerResource n edges horder).2.1 v

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
