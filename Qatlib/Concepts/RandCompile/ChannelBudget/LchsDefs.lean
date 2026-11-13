/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.Lchs

/-!
# Resource definitions for linear combinations of Hamiltonian simulations

This module names schedule sizes, source-loading counts, Taylor resources, and space budgets for
linear combinations of Hamiltonian simulations, following the framework of [AnLiuLin2023]. The
structure `LchsHybridSampleLedger` records source preparations, fast-forward applications,
queries, and shots for one sample or an entire sampling run.

## Main statements

* `lchs32JointScheduleSize`: counts the joint quadrature labels.
* `lchs34HybridTotalLedger`: collects resources for a prescribed number of samples.
* `lchs35ResourceLedger`: packages the theorem-level resource counts.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib MeasureTheory Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The number `(M + 1) * (Mt + 1)` of joint quadrature labels. -/
def lchs32JointScheduleSize (M Mt : ℕ) : ℕ := (M + 1) * (Mt + 1)

/-- The source-preparation count of the two-dimensional LCHS select operation. -/
def lchs32SourcePreparationCount (M Mt : ℕ) : ℕ := lchs2dSelectPrepareCount M Mt

/-- The native Taylor truncation order selected for precision level `m`. -/
def lchs33HamTOrder (m : ℕ) : ℕ := lchsHamTNativeOrder m

/-- The number of ancilla bits assigned to Taylor word labels of order `K` over `J`. -/
def lchs33AncillaBits (J : Type) [Fintype J] (K : ℕ) : ℕ := taylorAncillaBits J K

/-- The phase-gate count assigned to Taylor word labels of order `K` over `J`. -/
def lchs33PhaseGateCount (J : Type) [Fintype J] (K : ℕ) : ℕ := taylorPhaseGateCount J K

/-- The total query budget for `n` hybrid samples with window parameter `m`. -/
def lchs34HybridSampleQueries (m n : ℕ) : ℕ := lchsHybridTotalQueries m n

/-- The number of fast-forward applications assigned to one hybrid sample. -/
def lchs34FastForwardApplications : ℕ := capFastForwardApplications

/-- The fixed-gate count for an LCHS window of size `k`. -/
def lchs35FixedGateCount (k : ℕ) : ℕ := lchsFixedGateCount k

/-- The bit width assigned to a classical register with parameter `n`. -/
def lchs35RegisterBits (n : ℕ) : ℕ := lchsRegisterBits n

/-- The quantum-space count for `N` labels and `dataStates` data states. -/
def lchs35QuantumSpace (N dataStates : ℕ) : ℕ := lchsQuantumSpace N dataStates

/-- The LCHS theorem resource ledger for the given label, window, source-grid, and data-space
sizes. -/
noncomputable def lchs35ResourceLedger (N m Mt dataStates : ℕ) : LchsTheoremResources :=
  lchsTheoremResources N m Mt dataStates

/-- The single source-preparation operation assigned to each source label. -/
def lchs32LabelSourcePrepare : ℕ := 1

/-- The single source-input adjoint operation assigned to each source label. -/
def lchs32LabelSourceAdjoint : ℕ := 1

/-- The number of label-success rounds, equal to the window parameter `m`. -/
def lchs32LabelSuccessRounds (m : ℕ) : ℕ := m

/-- The reuse multiplicity `M + 1` of each loaded source node. -/
def lchs32SourceNodeReuse (M : ℕ) : ℕ := M + 1

/-- Resource counts for source preparations, fast-forward applications, oracle queries, and
sampling shots. -/
structure LchsHybridSampleLedger where

  sourcePreparations : ℕ

  fastForward : ℕ

  queries : ℕ

  shots : ℕ

/-- The ledger for one hybrid sample, with the source-node preparation count and one
fast-forward application. -/
def lchs34HybridSampleLedger (m Mt : ℕ) : LchsHybridSampleLedger :=
  { sourcePreparations := lchs2dSourceStateCount Mt
    fastForward := capFastForwardApplications
    queries := lchsHybridSampleMaxQueries m
    shots := 1 }

/-- The ledger for `n` hybrid samples, sharing source preparations and scaling fast-forward
applications and queries by the number of shots. -/
def lchs34HybridTotalLedger (m Mt n : ℕ) : LchsHybridSampleLedger :=
  { sourcePreparations := lchs2dSourceStateCount Mt
    fastForward := n * capFastForwardApplications
    queries := lchsHybridTotalQueries m n
    shots := n }

end Qatlib.Concepts.RandCompile.ChannelBudget
