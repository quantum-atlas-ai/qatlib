/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeAmplifiedDefinitions

/-!
# Specification of corrected HHL amplification bounds

`SectionIIAmplifiedRuntimeCorrected` uses the well-conditioned label of the three-state filter
as its selected event. Under the stated spectral gap and grid assumptions, it requires unitary
preparation and an amplification depth at most `⌈1 / (5 * d)⌉₊ + 1` with success probability at
least `1 / 4` and an explicit cost bound, in the setting of [HarrowHassidimLloyd2009].

## Main statements

* `SectionIIAmplifiedRuntimeCorrected`: the corrected event, amplification, and cost
  specification.

## References

* [Harrow et al., 2009, Section II][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

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

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

/-- The corrected sine-envelope amplification specification using `sinEnvelopeWellSetCorrected`,
with success probability at least `1 / 4`, depth at most `⌈1 / (5 * d)⌉₊ + 1`, and an
explicit cost bound. See [Harrow et al., Section II][HarrowHassidimLloyd2009]. -/
def SectionIIAmplifiedRuntimeCorrected : Prop :=
  ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d η : ℝ),
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    0 < d → 2 * d ≤ 1 / 4 → 0 < η → η ≤ 1 →
    (∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4) → 420 / (d * η) ≤ (M : ℝ) →
    sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B ∈
        Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
      ∃ k : ℕ,
        k ≤ Nat.ceil (1 / (5 * d)) + 1 ∧
        MeasureProb (Run (preparedMark (sinEnvelopeWellSetCorrected D M))
            (preparedAACircuit (sinEnvelopeAmplifiedWord M hM
              (continuousHHLOracle eig V) d B)
              (sinEnvelopeCleanInputPoint hM j) k)
            (Ket (sinEnvelopeCleanInputPoint hM j)))
            (sinEnvelopeWellSetCorrected D M) ≥ 1 / 4 ∧
        ((2 * (k : ℝ) + 1) * (2 * ((M : ℝ) - 1)) + (k : ℝ) ≤
          (2 * ((Nat.ceil (1 / (5 * d)) : ℝ) + 1) + 1) * (2 * (M : ℝ)) +
            ((Nat.ceil (1 / (5 * d)) : ℝ) + 1))

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
