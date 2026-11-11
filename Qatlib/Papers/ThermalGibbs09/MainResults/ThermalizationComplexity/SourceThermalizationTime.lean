/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalGibbs09.MainResults.Prelude
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — Main result: universal thermalization time

Poulin--Wocjan, fixed arXiv:0905.2199, p. 3 (the paragraph closing the
presentation of the universal thermalization process).

Claim `c001`: for any local-interaction quantum system the quantum algorithm
prepares the Gibbs state `ρ(β)` with accuracy `δ` by a local thermalization
process in time

`T_th(β) ∈ O( sqrt(D / Z(β)) · (β E_max / δ) · log(1/δ) · [log(1/δ) + β E_max] )`,

where `D` is the Hilbert-space dimension and `Z(β)` the partition function.

## Formalization boundary

This file provides the `ThermalizationProcess` certificate (runtime `Tth` and
the root-fidelity guarantee) but does *not* prove the paper's runtime bound.
The internal circuit that realizes the process (sequential QPE with
`η = O(log(1/δ) + βE_max)` median repetitions, Grover/fixed-point
amplification with `q = O(sqrt(D/Z(β)))` reflections, and `ℓ = ε/δ` cooling
steps) is not rebuilt in Lean, so `Tth` is unconstrained by any algorithm and
the bound cannot be honestly asserted.  See the prose status note below the
structure for the precise gap.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalGibbs09.MainResults.ThermalizationComplexity

open Qatlib.Papers.ThermalGibbs09.MainResults
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- A certified local thermalization process at inverse temperature `β`:
it has a runtime `Tth` (counted in uses of the simulated time-evolution
circuit `U`) and outputs a state whose root fidelity with the Gibbs state
`ρ(β)` is at least `1 - δ`. -/
structure ThermalizationProcess (D : ℕ) (H : Matrix (Fin D) (Fin D) ℂ) (β δ : ℝ) where
  /-- Runtime, counted in uses of the time-evolution circuit `U`. -/
  Tth : ℝ
  /-- The runtime is nonnegative. -/
  Tth_nonneg : 0 ≤ Tth
  /-- The state produced by the process. -/
  output : Matrix (Fin D) (Fin D) ℂ
  /-- The output is `δ`-close to the Gibbs state in root fidelity. -/
  output_fidelity : 1 - δ ≤ Froot output (gibbsState β H)

/- **arXiv:0905.2199, p. 3 (main result).** The paper's guarantee: there is an
absolute constant `C > 0` such that, for every `D`-dimensional Hamiltonian `H`
with `‖H‖ ≤ E_max`, every inverse temperature `β ≥ 0`, and every accuracy
`0 < δ ≤ 1`, some local thermalization process prepares the Gibbs state
`ρ(β)` to root fidelity `1 - δ` in time

`Tth ≤ C · sqrt(D / Z(β)) · (β E_max / δ) · log(1/δ) · (log(1/δ) + β E_max)`.

## Status: unformalised algorithmic content

The runtime bound is the *core* of the paper's main theorem and depends on the
concrete process: (i) Grover amplification of the purified marked Gibbs state
with `q = floor(sqrt(D/Z(β_k)))` reflections; (ii) suppression of QPE
fluctuations by `η = O(log(1/δ) + βE_max)` median repetitions; (iii)
fixed-point search at multiplicative cost `log(1/δ)`; (iv) `ℓ = ε/δ` cooling
steps.  None of this circuit-level construction exists in the repository, and
the `ThermalizationProcess` certificate above does *not* constrain `Tth`
against an actual algorithm, so no honest statement of the bound can be proved
here.  We therefore record the guarantee in prose rather than assert an
unprovable `∃` (a trivially satisfiable `∃` with `Tth = 0` would restate the
conclusion and is deliberately avoided).

The parts of the surrounding argument that *are* formalisable live elsewhere:
the cooling-schedule initial condition `Z(0) = D` is `partitionFunction_zero`,
and the ratio-product/error-propagation ledger is
`MainResults.PartitionFunctionComplexity` (`SourcePartitionFunctionRatio`). -/


end Qatlib.Papers.ThermalGibbs09.MainResults.ThermalizationComplexity
