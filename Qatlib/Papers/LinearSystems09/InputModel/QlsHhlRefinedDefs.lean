/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1ActualProgramCorrectedHarr
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SectionIIAmplifiedRuntimeCorrectedHarr
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SignedQuantizationAuxiliary
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeAmplifiedDefinitions
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HamiltonianInputModels
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.LinearSystemCostDefs
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhl
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# Explicit HHL resource and preparation data

This module defines resource ledgers and numerical quantities used to refine the linear-systems
model of [HarrowHassidimLloyd2009]. The definitions include half-grid chirps and their dyadic
approximations, dilation block extraction, Simon-reduction runtime models, and signed-spectrum
error budgets.

## Main statements

* `HhlAccessLedger`: Records oracle, synthesis, arithmetic, and workspace resources.
* `halfGridSymmetrized`: Averages a chirp with its reflected copy.
* `SignedSpectrumCondition`: Specifies the allowed nonzero signed spectral range.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.InputModel

open Matrix Qatlib
open scoped BigOperators

/-- The Simon-reduction instance-size model `36 * n * 2^(3 * n)`. -/
noncomputable def simonInstanceSize (n : ℕ) : ℝ := 36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ))

/-- The Simon-reduction condition-number parameter `4 * n`. -/
noncomputable def simonConditionNumber (n : ℕ) : ℝ := 4 * (n : ℝ)

/-- The runtime model `simonInstanceSize n ^ α * 2 ^ (β * simonConditionNumber n)`. -/
noncomputable def simonReductionRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n)

/-- The combined Simon-reduction exponent `3 * α + 4 * β`. -/
noncomputable def simonReductionExponent (α β : ℝ) : ℝ := 3 * α + 4 * β

/-- The positive-definite runtime model `simonInstanceSize n ^ α * 2 ^ (β * Real.sqrt
(simonConditionNumber n))`. -/
noncomputable def simonPositiveDefiniteRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α * (2 : ℝ) ^ (β * Real.sqrt (simonConditionNumber n))

/-- A record of HHL rounds, phase steps, oracle calls, controlled synthesis, integer bit time,
and peak workspace. -/
structure HhlAccessLedger where

  rounds : ℕ

  phaseSteps : ℕ

  oracleCalls : ℕ

  controlledSynthesis : ℕ

  integerBitTime : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

/-- The HHL access ledger with `m` rounds, `d` phase steps, `m * d` oracle and synthesis
operations, and the supplied arithmetic and workspace counts. -/
def hhlAccessLedger (m d : ℕ) (bitTime workspace : ℕ) : HhlAccessLedger where
  rounds := m
  phaseSteps := d
  oracleCalls := m * d
  controlledSynthesis := m * d
  integerBitTime := bitTime
  peakWorkspace := workspace

/-- The cumulative error model `n * ε` for `n` quantization steps. -/
noncomputable def cumulativeQuantizationError (n : ℕ) (ε : ℝ) : ℝ := (n : ℝ) * ε

/-- The preparation gate labels: uniform preparation, a ramp with a bit-precision parameter, and
reflection. -/
inductive PrepGate where

  | uniform

  | ramp (bits : ℕ)

  | mirror
  deriving DecidableEq, Repr

/-- The half-grid angle `π * (2 * τ + 1) / (2 * M)`. -/
noncomputable def halfGridAngle (M : ℕ) (τ : Fin M) : ℝ :=
  Real.pi * ((2 * (τ.val : ℝ) + 1)) / (2 * (M : ℝ))

/-- The integer obtained by flooring the half-grid fraction scaled by `2^k`. -/
def halfGridParam (M k : ℕ) (τ : Fin M) : ℕ :=
  Nat.floor (((2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))) * 2 ^ k)

/-- The dyadic approximation `π * halfGridParam M k τ / 2^k` to the half-grid angle. -/
noncomputable def halfGridAngleDyadic (M k : ℕ) (τ : Fin M) : ℝ :=
  Real.pi * ((halfGridParam M k τ : ℝ) / 2 ^ k)

/-- The reflected half-grid index with value `M - 1 - τ.val`. -/
def halfGridMirrorIndex (M : ℕ) (τ : Fin M) : Fin M := ⟨M - 1 - τ.val, by omega⟩

/-- The complex uniform amplitude given by the reciprocal of `sqrt M`. -/
noncomputable def halfGridAmplitude (M : ℕ) : ℂ := (Real.sqrt (M : ℝ) : ℂ)⁻¹

/-- The matrix whose every entry is the uniform amplitude `halfGridAmplitude M`. -/
noncomputable def uniformSuperposition (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun _ _ => halfGridAmplitude M

/-- The permutation matrix reflecting half-grid indices. -/
def halfGridMirrorGate (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun p q => if q = halfGridMirrorIndex M p then 1 else 0

/-- The uniformly scaled complex phase vector at the exact half-grid angles. -/
noncomputable def halfGridChirp (M : ℕ) : QState (Fin M) :=
  fun τ =>
    halfGridAmplitude M *
      ((Real.cos (halfGridAngle M τ) : ℝ) + (Real.sin (halfGridAngle M τ) : ℝ) * Complex.I)

/-- The uniformly scaled complex phase vector at the dyadically approximated half-grid angles. -/
noncomputable def halfGridChirpDyadic (M k : ℕ) : QState (Fin M) :=
  fun τ =>
    halfGridAmplitude M *
      ((Real.cos (halfGridAngleDyadic M k τ) : ℝ) +
        (Real.sin (halfGridAngleDyadic M k τ) : ℝ) * Complex.I)

/-- The average of the half-grid chirp and its reflected copy. -/
noncomputable def halfGridSymmetrized (M : ℕ) : QState (Fin M) :=
  fun τ => (halfGridChirp M τ + halfGridChirp M (halfGridMirrorIndex M τ)) / 2

/-- The preparation gate-count model `3 * M`. -/
def prepGateCount (M k : ℕ) : ℕ := 3 * M

/-- The preparation workspace model `M`. -/
def prepWorkspace (M : ℕ) : ℕ := M

/-- The preparation parameter-bit count `M * k`. -/
def prepParamBits (M k : ℕ) : ℕ := M * k

/-- The dilation dimension `m + n`. -/
def dilationSize (m n : ℕ) : ℕ := m + n

/-- The restriction of a sum-indexed vector to its solution block. -/
def dilationSolutionBlock {O I : Type} (x : QState (O ⊕ I)) : QState I := fun i => x (Sum.inr i)

/-- The restriction of a sum-indexed vector to its right-hand-side block. -/
def dilationRhsBlock {O I : Type} (x : QState (O ⊕ I)) : QState O := fun o => x (Sum.inl o)

/-- A record of preparation gates, Hamiltonian levels, extraction levels, and total gates for
the dilation route. -/
structure DilationRouteLedger where

  prepareGates : ℕ

  hamiltonianLevels : ℕ

  extractionLevels : ℕ

  totalGates : ℕ
  deriving DecidableEq, Repr

/-- The dilation route ledger with `m + n` Hamiltonian levels, `n` extraction levels, and total
count `prepareGates + m + n + n`. -/
def dilationRouteLedger (m n prepareGates : ℕ) : DilationRouteLedger where
  prepareGates := prepareGates
  hamiltonianLevels := dilationSize m n
  extractionLevels := n
  totalGates := prepareGates + dilationSize m n + n

/-- The condition that each eigenvalue is zero or has absolute value between `d` and `1 / 4`. -/
def SignedSpectrumCondition {D : ℕ} (eig : Fin D → ℝ) (d : ℝ) : Prop :=
  ∀ i, eig i = 0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1 / 4)

/-- The first-order signed-filter error budget `C / (d * M)`. -/
noncomputable def signedFirstOrderBudget (C d M : ℝ) : ℝ := C / (d * M)

/-- The total signed-filter budget formed from the first-order error, `32 / 2^k`, and `2 * (M -
1) * δ`. -/
noncomputable def signedErrorBudget (C d M : ℝ) (k : ℕ) (δ : ℝ) : ℝ :=
  signedFirstOrderBudget C d M + 32 / 2 ^ k + 2 * (M - 1) * δ

end Qatlib.Papers.LinearSystems09.InputModel
