/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.UnitaryGroup
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1ActualProgramCorrectedStat
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# HHL amplification events and runtime specifications

`sinEnvelopeAmplifiedWord` evaluates the sine-envelope HHL preparation circuit, and
`sinEnvelopeCleanInputPoint` specifies its initial workspace index. The module defines both
`sinEnvelopeWellSet` on the Boolean ancilla and `sinEnvelopeWellSetCorrected` on the three-state
filter label for amplification in the setting of [HarrowHassidimLloyd2009].

`SectionIIAmplifiedRuntime` states the unitarity, amplification-success, depth, and cost
requirements using `sinEnvelopeWellSet`.

## Main statements

* `sinEnvelopeWellSetCorrected`: the event selecting filter label one.
* `sinEnvelopeAmplifiedWord`: the evaluated preparation matrix used by amplification.
* `SectionIIAmplifiedRuntime`: the proposition using the Boolean-ancilla event.

## References

* [Harrow et al., 2009, Section II][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions.HHL2009

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

/-- The workspace indices whose Boolean ancilla is true. -/
def sinEnvelopeWellSet (D M : ℕ) :
    Finset (Fin M × (Bool × (Fin 3 × Fin D))) :=
  Finset.univ.filter (fun p => p.2.1 = 1)

/-- The workspace indices whose three-state filter register has label one. -/
def sinEnvelopeWellSetCorrected (D M : ℕ) :
    Finset (Fin M × (Bool × (Fin 3 × Fin D))) :=
  Finset.univ.filter (fun p => p.2.2.1 = 1)

/-- The evaluated sine-envelope HHL preparation matrix used as the input to amplitude
amplification. -/
noncomputable def sinEnvelopeAmplifiedWord {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U : Operator D) (d : ℝ) (B : Operator D) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D)))
      (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
  evaluate (sinEnvelopeOracleLift U) (sinEnvelopeHHLWord M hM d B)

/-- The workspace basis index with zero phase, false Boolean ancilla, filter label zero, and
data index `j`. -/
def sinEnvelopeCleanInputPoint {D M : ℕ} (hM : 2 ≤ M) (j : Fin D) :
    Fin M × (Bool × (Fin 3 × Fin D)) :=
  (⟨0, by omega⟩, false, (0, j))

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

/-- The amplification proposition using `sinEnvelopeWellSet`, specifying unitarity, success
probability at least `1 / 4`, bounded amplification depth, and an explicit cost inequality. -/
def SectionIIAmplifiedRuntime : Prop :=
  ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d η : ℝ),
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    0 < d → 2 * d ≤ 1 / 4 → 0 < η → η ≤ 1 →
    (∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4) → 420 / (d * η) ≤ (M : ℝ) →
    sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B ∈
        Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
      ∃ k : ℕ,
        k ≤ Nat.ceil (1 / (5 * d)) + 1 ∧
        MeasureProb (Run (preparedMark (sinEnvelopeWellSet D M))
            (preparedAACircuit (sinEnvelopeAmplifiedWord M hM
              (continuousHHLOracle eig V) d B)
              (sinEnvelopeCleanInputPoint hM j) k)
            (Ket (sinEnvelopeCleanInputPoint hM j)))
            (sinEnvelopeWellSet D M) ≥ 1 / 4 ∧
        ((2 * (k : ℝ) + 1) * (2 * ((M : ℝ) - 1)) + (k : ℝ) ≤
          (2 * ((Nat.ceil (1 / (5 * d)) : ℝ) + 1) + 1) * (2 * (M : ℝ)) +
            ((Nat.ceil (1 / (5 * d)) : ℝ) + 1))

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
