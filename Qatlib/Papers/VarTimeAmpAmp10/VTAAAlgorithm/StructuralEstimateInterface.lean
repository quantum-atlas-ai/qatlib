/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgram
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.MedianEstimate

/-!
# Structural estimation words and record laws

This module defines `CompiledVtStep`, its matrix semantics, weighted time, and legality
conditions. It also defines physical fresh estimation kernels and the product record law,
together with the set of records whose median estimates satisfy the prescribed error radius.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `compiledVtCircuit`: circuit semantics for compiled words.
* `dataFreshKernel`: fresh estimation outcome mass.
* `dataRecordGood`: records with accurate median estimates.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical

/-- A compiled estimation instruction consisting of a plain data step, a controlled data step,
or a gate on the phase and Boolean workspace registers. -/
inductive CompiledVtStep (M : ℕ) where
  | plain : DataVtStep → CompiledVtStep M
  | controlled : DataVtStep → CompiledVtStep M
  | workspace : Matrix (Fin M × Bool) (Fin M × Bool) ℂ → CompiledVtStep M

variable {C : Type} [Fintype C] [DecidableEq C]
/-- The matrix semantics of a compiled estimation step on the phase, Boolean, and variable-time
data registers. -/
def compiledVtStepMatrix (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) :
    CompiledVtStep M → Matrix (Fin M × (Bool × VtSpace C)) (Fin M × (Bool × VtSpace C)) ℂ
  | .plain s => TensorGate 1 (TensorGate 1 (dataVtStepMatrix stages history j₀ s))
  | .controlled s => aeControlledGate M (dataVtStepMatrix stages history j₀ s)
  | .workspace U => fun p q => U (p.1,p.2.1) (q.1,q.2.1) *
      (1 : Matrix (VtSpace C) (VtSpace C) ℂ) p.2.2 q.2.2

/-- The weighted time of a compiled step, charging data steps their original time and workspace
steps zero. -/
def compiledVtStepTime {M : ℕ} : CompiledVtStep M → ℕ
  | .plain s | .controlled s => dataVtStepTime s
  | .workspace _ => 0

/-- The sum of the weighted times of all steps in a compiled word. -/
def compiledVtWordTime {M : ℕ} (word : List (CompiledVtStep M)) : ℕ :=
  (word.map compiledVtStepTime).sum

/-- Legality of a compiled step, requiring legal data access for data steps and unitarity for
workspace gates. -/
def CompiledVtStepLegal {M : ℕ}
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) : CompiledVtStep M → Prop
  | .plain s | .controlled s => DataVtStepLegal stages s
  | .workspace U => U ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ

/-- The condition that every step in a compiled word is legal. -/
def CompiledVtWordLegal {M : ℕ}
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (word : List (CompiledVtStep M)) : Prop :=
  ∀ s ∈ word, CompiledVtStepLegal stages s

/-- The circuit obtained by replacing each compiled step by its matrix gate. -/
def compiledVtCircuit (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List (CompiledVtStep M)) :
    Circuit (Fin M × (Bool × VtSpace C)) :=
  Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.Circuit.ofGates (word.map (compiledVtStepMatrix M stages history j₀))

/-- The measurement mass of a label record from `2 * r + 1` fresh amplitude-estimation runs for
a data word's live mass. -/
def dataFreshKernel (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep)
    (ω : Fin (2*r+1) → Fin M) : ℝ :=
  MeasureProb (Run 1
    (vtFreshAECircuit M (dataVtWordMatrix stages history j₀ word) j₀ (liveSet C) (2*r+1))
    (vtFreshAEInput M hM j₀ (2*r+1)))
    (Finset.univ.filter (fun p => vtFreshLabel (2*r+1) p = ω))

/-- The product of fresh estimation kernel values along a record, allowing each queried word to
depend on the record. -/
def dataRecordLaw (M : ℕ) (hM : 2 ≤ M) (r n : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C)
    (words : (Fin n → (Fin (2*r+1) → Fin M)) → Fin n → List DataVtStep)
    (ω : Fin n → (Fin (2*r+1) → Fin M)) : ℝ :=
  ∏ i, dataFreshKernel M hM r stages history j₀ (words ω i) (ω i)

/-- The amplitude-estimation radius `2 * π * sqrt (a * (1 - a)) / M + π² / M²`. -/
def dataEstimateRadius (a : ℝ) (M : ℕ) : ℝ :=
  2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2

/-- The finite set of records for which every median estimate differs from its selected word's
live mass by at most `dataEstimateRadius`. -/
def dataRecordGood (M r n : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C)
    (words : (Fin n → (Fin (2*r+1) → Fin M)) → Fin n → List DataVtStep) :
    Finset (Fin n → (Fin (2*r+1) → Fin M)) :=
  Finset.univ.filter fun ω => ∀ i,
    let a := MeasureProb (dataVtWordState stages history j₀ (words ω i)) (liveSet C)
    |vtMedianEstimate M r (ω i)-a| ≤ dataEstimateRadius a M
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
