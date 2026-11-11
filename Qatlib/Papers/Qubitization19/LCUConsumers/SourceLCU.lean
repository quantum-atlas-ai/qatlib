/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Corollary16LCUSimulationLowc
import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Corollary17DensitySimulationLowc
import Qatlib.Concepts.OperatorAccess.EncodedAccess
import Mathlib.Tactic

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.PureStateMath.Reflection

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5, Lemma 7, Corollary 16, Corollary 17 — LCU and purified-density consumers

Low–Chuang, *Hamiltonian Simulation by Qubitization*, fixed arXiv:1610.06546v3.

* Lemma 5 (PDF p.8, Eq. (10)): the linear-combination-of-unitaries oracle
  `(PREPARE† ⊗ I) SELECT (PREPARE ⊗ I)` is a standard-form encoding of
  `∑ⱼ αⱼ Uⱼ / ‖α‖₁`.
* Lemma 7 (PDF p.9, Eq. (15)): the SWAP oracle of Eq. (14) is a standard-form
  encoding of the reduced density matrix of the purification register.
* Corollary 16 (PDF p.16): Theorem 1 with the Lemma 5 encoding gives
  `O(‖α‖₁ t + log(1/ε))`-query simulation of `∑ⱼ αⱼ Uⱼ`.
* Corollary 17 (PDF p.16): Theorem 1 with the Lemma 7 encoding gives
  `O(t + log(1/ε))`-query simulation of a density matrix `ρ`.

Matrix-level semantics: queries are counted against the composite
`LCUWorkspace U P` oracle (Lemma 5) and the SWAP oracle `purificationBody U`
(Lemma 7); basic-gate and bit-time synthesis are out of scope and are recorded
in the paper-layer cost contracts of the main results block.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.SignalPrimitive.LCUConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.Qubitization19.LCUConsumers

/-- Fixed arXiv:1610.06546v3, Lemma 5 (PDF p.8, Eq. (10)): the LCU oracle is a
standard-form encoding. Given unitaries `Uⱼ`, nonnegative weights `αⱼ = w j`, and
a PREPARE unitary `P` with `P |j₀⟩ = ∑ⱼ √(w j / s) |j⟩` at the positive scale
`s = ∑ⱼ w j` (paper: `|G⟩ = ∑ⱼ √(αⱼ/‖α‖₁) |j⟩`), the composite
`⟨j₀| ⊗ I) (PREPARE† SELECT PREPARE) (|j₀⟩ ⊗ I)` equals
`∑ⱼ w j • U j / s`, i.e. `IsBlockEncoding (LCUWorkspace U P) j₀ (∑ⱼ w j • U j) s`
with `s = ∑ⱼ w j`. Reuses the frozen
`lcu_isBlockEncoding_of_isScaledPrepare`. -/
theorem lemma5_lcu_block_encoding {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (U : J → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : Matrix J J ℂ) (j₀ : J)
    (hP : IsScaledPrepare P w (∑ j, w j) j₀) :
    IsBlockEncoding (LCUWorkspace U P) j₀ (∑ j, w j • U j) (∑ j, w j) :=
  lcu_isBlockEncoding_of_isScaledPrepare U hU hw hP

/-- Fixed arXiv:1610.06546v3, Lemma 7 (PDF p.9, Eq. (15)): corner form of the
purification/SWAP oracle. For a unitary `U` on the purification register and any
seed `seed`, the `seed`-fiber corner of the physical SWAP word
`purificationBody U = (U† ⊗ I) SWAP (U ⊗ I)` is the reduced density matrix
`ρ = purifiedDensity (U |seed⟩)` of Eq. (13). Reuses the frozen
`purification_corner`. -/
theorem lemma7_purification_corner {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (U : Matrix (A × I) (A × I) ℂ) (seed : A × I) :
    compress (encodingFiber seed) (purificationBody U) (encodingFiber seed) =
      purifiedDensity (U *ᵥ Ket seed) :=
  purification_corner U seed

/-- Fixed arXiv:1610.06546v3, Lemma 7 (PDF p.9, Eqs. (14)–(15)): the full
standard-form encoding statement plus the paid oracle ledger. The density matrix
`ρ = purifiedDensity (U |seed⟩)` is positive semidefinite with unit trace,
`purificationBody U` is a projected unitary encoding of `ρ` between the seed
fiber frames, the instruction word is well formed, and each oracle access costs
exactly 2 preparation-direction queries and 1 SWAP gate. Reuses the frozen
`purification_actual_positive_block_and_cost`. -/
theorem lemma7_purification_encoding {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (U : Matrix (A × I) (A × I) ℂ) (seed : A × I)
    (hU : U ∈ Matrix.unitaryGroup (A × I) ℂ) :
    let rho := purifiedDensity (U *ᵥ Ket seed)
    rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
    ProjectedUnitaryEncoding rho (purificationBody U) (encodingFiber seed) (encodingFiber seed) ∧
    WellFormedAdjointCircuit (purificationWord (A := A) (I := I)) ∧
    adjointQueryCount (purificationWord (A := A) (I := I)) = 2 ∧
    adjointGateCount (purificationWord (A := A) (I := I)) = 1 :=
  purification_actual_positive_block_and_cost U seed hU

/-- Fixed arXiv:1610.06546v3, Corollary 16 (PDF p.16): LCU Hamiltonian
simulation with the paper's query count `O(‖α‖₁ t + log(1/ε))` and the explicit
degree/ledger budget of the frozen contract. This is exactly the frozen
`Corollary16LCUSimulation`, proved by
`QuantumAlgorithm.Papers.Qubitization19.LCUConsumers.corollary16LCUSimulation`;
it feeds Lemma 5's encoding at scale `∑ⱼ w j` into the Theorem 1 operator core. -/
theorem corollary16_lcu_simulation :
    Qatlib.Concepts.SignalPrimitive.LCUConsumers.Corollary16LCUSimulation :=
  Qatlib.Concepts.SignalPrimitive.LCUConsumers.corollary16LCUSimulation

/-- Fixed arXiv:1610.06546v3, Corollary 17 (PDF p.16): simulation of a density
matrix given the purified access oracle of Eq. (14), with query count
`O(t + log(1/ε))`. This is exactly the frozen `Corollary17DensitySimulation`,
proved by `QuantumAlgorithm.Papers.Qubitization19.LCUConsumers.corollary17DensitySimulation`;
it feeds Lemma 7's `purificationBody` encoding of `ρ` into the Theorem 1
operator core at scale `α = 1`. -/
theorem corollary17_density_simulation :
    Qatlib.Concepts.SignalPrimitive.LCUConsumers.Corollary17DensitySimulation :=
  Qatlib.Concepts.SignalPrimitive.LCUConsumers.corollary17DensitySimulation

end Qatlib.Papers.Qubitization19.LCUConsumers
