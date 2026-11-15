/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

namespace Qatlib.Concepts.AmplitudeCore.InvFreeSampling

open Qatlib

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def invFreeAmplitude (P : Matrix I I ℂ) (j₀ : I) (U : Matrix I I ℂ) : ℝ :=
  ProjectiveBranchMass P true (ApplyGate U (Ket j₀))

def invFreeRoundCircuit : Circuit I := [Step.query]

/-- Shows that the inverse-free round circuit makes exactly one query. -/
@[simp] theorem invFreeRoundCircuit_queryCount (I : Type) [Fintype I] [DecidableEq I] :
    QueryCount (invFreeRoundCircuit : Circuit I) = 1 := rfl

/-- Shows that running the inverse-free round circuit on a basis state applies the queried
matrix once. -/
@[simp] theorem invFreeRoundCircuit_run (I : Type) [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (j₀ : I) :
    Run U (invFreeRoundCircuit : Circuit I) (Ket j₀) = ApplyGate U (Ket j₀) := rfl

def invFreeReadout (b : Bool) : ℝ := if b then 1 else 0

noncomputable def invFreeBranchDist (P : Matrix I I ℂ) (j₀ : I)
    (hP : IsOrthogonalProjector P) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : FinDist Bool where
  prob b := ProjectiveBranchMass P b (Run U invFreeRoundCircuit (Ket j₀))
  nonneg b := projectiveBranchMass_nonneg P b _
  sum_one := by
    have hsplit := projectiveBranchMass_add hP (Run U invFreeRoundCircuit (Ket j₀))
    have hbool : ∀ g : Bool → ℝ, ∑ b, g b = g false + g true := by
      intro g
      simp
      ring
    rw [hbool, hsplit, invFreeRoundCircuit_run]
    exact measureProb_univ (normalized_applyGate hU (normalized_ket j₀))

/-- Identifies the expected inverse-free readout with the projected amplitude. -/
theorem invFree_expect_amplitude (P : Matrix I I ℂ) (j₀ : I)
    (hP : IsOrthogonalProjector P) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (invFreeBranchDist P j₀ hP U hU).expect invFreeReadout =
      invFreeAmplitude P j₀ U := by
  simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, invFreeBranchDist, invFreeReadout, invFreeAmplitude,
    invFreeRoundCircuit_run]

noncomputable def invFreeSampleCount (ε : ℝ) : ℕ := ⌈3 / (4 * ε ^ 2)⌉₊

end Qatlib.Concepts.AmplitudeCore.InvFreeSampling
