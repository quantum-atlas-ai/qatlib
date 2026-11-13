/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Corollary17DensitySimulationStat
import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1TaylorTruncationLowc
import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1Simulation

/-!
# Simulation from a Purification Unitary

This module proves `corollary17DensitySimulation` for the reduced density matrix prepared by a
unitary `Up` from a basis `seed`. It combines the concrete `purificationBody` encoding with the
Taylor simulation theorem, following the purified-density setting of Corollary 17 in
[LowChuang2019].

The density matrix is a Hermitian contraction, so the simulation uses normalization one. The two
response words have query counts `2 * n` and `2 * n + 1`, where `n ≤ 4 * |t| + 8 * log (8 / ε) +
8`, and their scaled compressed combination approximates the density-matrix evolution within `ε`
in operator norm.

## Main statements

* `corollary17DensitySimulation` proves the density simulation contract for every unitary
  purification circuit and `0 < ε < 1`.

## References

- [Low and Chuang, 2019][LowChuang2019], Corollary 17.
-/

open Qatlib.Concepts.SignalPrimitive.MainResults
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.OperatorAccess.EncodedAccess Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Proves `Corollary17DensitySimulation` by using the density matrix's purification encoding
with normalization one. It establishes the two-word approximation and resource bounds
associated with Corollary 17 of [LowChuang2019]. -/
theorem corollary17DensitySimulation : Corollary17DensitySimulation := by
  intro A I _ _ _ _ Up seed hUp t ε hε hε1
  have hp := purification_actual_positive_block_and_cost Up seed hUp
  let ρ := purifiedDensity (Up *ᵥ Ket seed)
  have hρ : ρ.IsHermitian := hp.1.isHermitian
  have henc : ProjectedUnitaryEncoding ρ (purificationBody Up)
      (encodingFiber seed) (encodingFiber seed) := hp.2.2.1
  have hnorm : ‖ρ‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry _).trans
      (unitary_norm_le_one henc.unitary)
  obtain ⟨n, hcut, htail, hdegree⟩ := theorem1TaylorTruncation t ε hε
  obtain ⟨wc, ws, hqc, hgc, hqs, hgs, herr⟩ := theorem1Simulation (A × I) I
    ρ (purificationBody Up) seed 1 t ε n hρ (by norm_num) hnorm hε hε1
    (by simpa using henc) (by simpa using hcut) (by simpa using htail)
  refine ⟨n, wc, ws, ?_, hqc, hgc, hqs, hgs, herr⟩
  simpa only [min_eq_left hε1.le] using hdegree

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
