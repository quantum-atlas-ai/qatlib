/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Mathlib.Data.Fintype.Pi
import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Qatlib.Concepts.GradientOracle.ReadoutWindow.ValueOracleGradientPrecision
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientLaws
import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineGradient
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout

/-!
# Probability phase oracle definitions

`cleanFrame`, `goodReflection`, and `probabilityMass` specify the clean ancillary embedding,
marking reflection, and associated measurement mass. The reflection and simulation words
implement the substitutions used to turn this probability information into a diagonal phase.

The module also defines precision, dyadic decoding, and readout resource quantities. The
projected encoding and signal processing context is given in [GilyenSuLowWiebe2019].

## Main statements

* `probabilityPhaseWord`: adds a scalar correction to the half-time simulation.
* `cleanProbabilityPhaseWord`: surrounds the phase word by signal preparation and its adjoint.
* `phasePrecision`: chooses an integer precision from a rational tolerance.
* `readoutErrorBudget`: combines grid and phase errors.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.FullRange
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators

/-- The matrix embedding each label basis vector with ancillary value fixed to `a₀`. -/
def cleanFrame {X A : Type*} [DecidableEq X] [DecidableEq A] (a₀ : A) :
    Matrix (X × A) X ℂ := fun xa x => if xa = (x,a₀) then 1 else 0

/-- The diagonal matrix with sign `-1` on good ancillary values and sign `1` elsewhere. -/
def goodReflection {X A : Type*} [DecidableEq X] [DecidableEq A] (good : Finset A) :
    Matrix (X × A) (X × A) ℂ := Matrix.diagonal (fun xa => if xa.2 ∈ good then -1 else 1)

/-- The sum of squared oracle amplitudes from `(x, a₀)` to `(x, a)` over good ancillary values. -/
def probabilityMass {X A : Type*} (U : Matrix (X × A) (X × A) ℂ)
    (a₀ : A) (good : Finset A) (x : X) : ℝ :=
  ∑ a ∈ good, Complex.normSq (U (x,a) (x,a₀))

/-- The adjoint-query word representing the oracle-conjugated good reflection. -/
def reflectionWord {X A : Type*} [DecidableEq X] [DecidableEq A] (good : Finset A) :
    List (AdjointStep (X × A)) := [.backward, .gate (goodReflection good), .forward]

/-- The reflection word using a controlled good reflection between backward and forward queries. -/
def controlledReflectionWord {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A) :
    List (AdjointStep (Bool × (X × A))) :=
  [.backward, .gate (controlOracle (goodReflection good)), .forward]

/-- The word obtained by substituting the reflection word for oracle queries in an adjoint
circuit. -/
def expandReflection {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A)
    (word : List (AdjointStep (X × A))) : List (AdjointStep (X × A)) :=
  substituteAdjointCircuit (reflectionWord good) word

/-- The oracle `U` lifted to the three Boolean registers used by the probability simulation. -/
def probabilityPrimitiveOracle {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ) :
    Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ :=
  TensorGate 1 (parallelOracle (J := Bool) (parallelOracle (J := Bool) U))

/-- The lifted reflection body substituted into the signal processing simulation. -/
def probabilitySimulationBody {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  [.backward, .gate (TensorGate 1
    (controlOracle (parallelOracle (J := Bool) (goodReflection (X := X) good)))), .forward]

/-- The computed signal word with its queries replaced by probability reflection bodies. -/
def probabilitySimulationWord {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) (good : Finset A) (t : ℚ) (k : ℕ) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  substituteAdjointCircuit (probabilitySimulationBody good)
    (computedSignalWord (cleanFrame (X := X) a₀) t k)

/-- The half-time probability simulation word prefixed by the scalar phase correction `exp (I /
2)`. -/
def probabilityPhaseWord {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) (good : Finset A) (k : ℕ) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  .gate (Complex.exp (Complex.I/2) • 1) :: probabilitySimulationWord (X := X) a₀ good (1/2) k

/-- The Boolean matrix with row amplitudes `realPartAmplitude` and a negative sign only when
both indices are true. -/
def averagePreparation : Matrix Bool Bool ℂ := fun b c =>
  realPartAmplitude b * if b && c then -1 else 1

/-- The two-gate word preparing the signal ancillary registers by average preparation matrices. -/
def signalPreparationWord (H : Type) [Fintype H] [DecidableEq H] :
    List (AdjointStep (Bool × (Bool × (Bool × H)))) :=
  [.gate (TensorGate 1 (TensorGate averagePreparation (1 : Matrix (Bool × H) (Bool × H) ℂ))),
   .gate (TensorGate 1 (TensorGate 1 (TensorGate averagePreparation (1 : Matrix H H ℂ))))]

/-- The clean input frame extended by three zero Boolean flags. -/
def zeroSignalFrame {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) :
    Matrix (Bool × (Bool × (Bool × (X × A)))) X ℂ :=
  scaleEightFrame (scaleEightFrame (scaleEightFrame (cleanFrame (X := X) a₀)))

/-- The probability phase word surrounded by signal preparation and its adjoint. -/
def cleanProbabilityPhaseWord {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) (good : Finset A) (k : ℕ) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  adjointCircuit (signalPreparationWord (X × A)) ++
    probabilityPhaseWord (X := X) a₀ good k ++ signalPreparationWord (X × A)

/-- The base-two ceiling logarithm of the positive natural ceiling of the reciprocal tolerance. -/
def phasePrecision (ε : ℚ) : ℕ := Nat.clog 2 (max 1 ⌈ε⁻¹⌉₊)

end Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.Reduction.GradientOracle

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The real phase `z.val / M` associated with a finite grid point. -/
noncomputable def dyadicGridPhase (M : ℕ) (z : Fin M) : ℝ := (z.val : ℝ) / (M : ℝ)

/-- The predicate that `θ` is an integer multiple of `2^(-k)`. -/
def HasDyadicRecord (k : ℕ) (θ : ℝ) : Prop := ∃ n : ℤ, θ = n / (2 : ℝ) ^ k

/-- The affine decoding `lo + v.val / (s * 2^k)` of a modular dyadic record. -/
noncomputable def dyadicDecode (lo s : ℝ) (K k : ℕ) (v : ZMod (2 ^ (K + k))) : ℝ :=
  lo + (v.val : ℝ) / (s * (2 : ℝ) ^ k)

/-- The readout error expression `16 * d / (M * w) + 4 * Real.pi * δ`. -/
noncomputable def readoutErrorBudget (d M : ℕ) (w δ : ℝ) : ℝ :=
  16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * δ

/-- The sum of the counted median comparisons over all gradient coordinates. -/
noncomputable def medianComparisonCount (d M : ℕ) (r : ℕ)
    (ω : Fin (2 * r + 1) → GradientGrid d M) : ℕ :=
  ∑ j : Fin d, (gradientMedianCounted r ω j).2

/-- The integer readout bit count `K + k`. -/
def readoutIntegerBits (K k : ℕ) : ℕ := K + k

/-- The readout space count `d * Nat.clog 2 (max 2 M) + K + k`. -/
def readoutSpaceBits (d M K k : ℕ) : ℕ :=
  d * Nat.clog 2 (max 2 M) + K + k

end Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
