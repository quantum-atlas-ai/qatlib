/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StructuralEstimateInterface

/-!
# Structural compilation of variable-time estimation

This module defines `StructuralEstimateCompilation`, a statement linking legal variable-time
data words to amplitude-estimation circuits in the development of [Ambainis2012]. It requires
unitary word matrices, equivalent compiled executions with exact weighted-time formulas, and
normalized adaptive record laws whose good-event mass is at least `1 - n * (8 / 9)^r`.

## Main statements

* `StructuralEstimateCompilation`: Unitary data words, exact estimation compilation, and
  adaptive-record probability bounds.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The proposition that growing legal variable-time stages yield unitary legal data words and
equivalent compiled estimation circuits with the specified exact time and repetition
formulas. It also requires causal adaptive record laws to be normalized, nonnegative, and to
assign mass at least `1 - n * (8 / 9)^r` to the good records. -/
def StructuralEstimateCompilation : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C),
    GrowingVtLegal stages history → ∀ (j₀ : VtSpace C),
    (∀ word, DataVtWordLegal stages word →
      dataVtWordMatrix stages history j₀ word ∈ Matrix.unitaryGroup (VtSpace C) ℂ) ∧
    (∀ (M : ℕ), 2 ≤ M → ∀ word, DataVtWordLegal stages word →
      ∃ cs : List (CompiledVtStep M), CompiledVtWordLegal stages cs ∧
        compiledVtWordTime cs = (2*(M-1)+1)*dataVtWordTime word ∧
        (∀ ψ, Run 1 (compiledVtCircuit M stages history j₀ cs) ψ =
          Run (aeControlledGate M (preparedMark (liveSet C)))
            (countedAECircuit M (dataVtWordMatrix stages history j₀ word) j₀) ψ) ∧
        (∀ n, (∀ ψ, Run 1 (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.Circuit.ofGates
          (vtFreshGates (cs.map (compiledVtStepMatrix M stages history j₀)) n)) ψ =
          Run 1 (vtFreshAECircuit M (dataVtWordMatrix stages history j₀ word) j₀
            (liveSet C) n) ψ) ∧
          (List.replicate n cs).flatten.length = n*cs.length ∧
          compiledVtWordTime (List.replicate n cs).flatten =
            n*(2*(M-1)+1)*dataVtWordTime word)) ∧
    (∀ (M : ℕ) (hM : 2 ≤ M) (r n : ℕ)
      (words : (Fin n → (Fin (2*r+1) → Fin M)) → Fin n → List DataVtStep),
      (∀ ω i, DataVtWordLegal stages (words ω i)) →
      (∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → words ω i = words ω' i) →
      (∑ ω, dataRecordLaw M hM r n stages history j₀ words ω = 1) ∧
      (∀ ω, 0 ≤ dataRecordLaw M hM r n stages history j₀ words ω) ∧
      (1-(n : ℝ)*(8/9 : ℝ)^r ≤
        ∑ ω ∈ dataRecordGood M r n stages history j₀ words,
          dataRecordLaw M hM r n stages history j₀ words ω))
end Qatlib.Papers.VarTimeAmpAmp10.Estimate
