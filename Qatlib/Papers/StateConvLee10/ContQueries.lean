/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.ContinuousProgram
import Qatlib.Concepts.ConversionCore.WitnessCompile.ConversionBridges

/-!
# Continuous and fractional query comparisons

This module bounds the filtered Gram change caused by legal continuous query programs and by a
single nonnegative fractional Boolean query. It also compares continuous and discrete coherent
and noncoherent costs, with explicit error parameters and constants, in the setting of
[LeeEtAl2011].

## Main statements

* `source_continuous_gram_budget`: total query time bounds filtered Gram change.
* `source_bounded_error_models`: continuous and discrete bounded-error costs satisfy the
  displayed comparisons.
* `source_fractional_query_bound`: a fractional Boolean query has a linear filtered-norm bound.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.ModelSemantics Qatlib.Concepts.QueryComplexity.StateConversion
open MeasureTheory Set Filter
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.StateConversion
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.StateConvLee10.ContQueries

/-- For normalized input states, the filtered Gram change of a legal continuous program is at
most `(1 + π²)` times its total query time [LeeEtAl2011]. -/
theorem source_continuous_gram_budget {X W : Type}
    [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (C : List (SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W)))
    (hC : sourceContinuousLegal C)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    sourceRectValue (gramStateMatrix ψ - gramStateMatrix
      (fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ ψ x))
      (sourceAlphabetDelta input) ≤ ENNReal.ofReal ((1+Real.pi^2) * sourceContinuousTime C) := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.stageB_state_conversion_clause92 (X := X)
      (W := W) (n := n) (q := q) (input := input) (C := C) (hC := hC) (ψ := ψ) (hψ := hψ)

/-- For normalized state families, continuous coherent and noncoherent costs are bounded by
their discrete counterparts, and discrete costs at error `1 / 3` satisfy the displayed
constant-factor bounds using continuous costs at error `1 / 13436928` [LeeEtAl2011]. -/
theorem source_bounded_error_models {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) :
    (∀ ε : ℝ, sourceContinuousCoherentQ input ρ σ ε ≤ sourceCoherentQ input ρ σ ε) ∧
    (∀ ε : ℝ, sourceContinuousNoncoherentQ input ρ σ ε ≤ sourceNoncoherentQ input ρ σ ε) ∧
    sourceCoherentQ input ρ σ (1/3) ≤
      ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))*
        sourceContinuousCoherentQ input ρ σ (1/13436928) ∧
    sourceNoncoherentQ input ρ σ (1/3) ≤
      ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))*
        sourceContinuousNoncoherentQ input ρ σ (1/13436928) := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.stageB_state_conversion_clause93 (X := X)
      (H := H) (n := n) (q := q) (input := input) (ρ := ρ) (σ := σ) (hn := hn)

/-- A fractional Boolean oracle query of strength `lam ≥ 0` changes the Gram matrix by filtered
norm at most `lam * π * sqrt 2` [LeeEtAl2011]. -/
theorem source_fractional_query_bound {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam : ℝ) (hlam : 0 ≤ lam)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (hρ : ∀ x, Normalized (ρ x)) :
    sourceRectValue (gramStateMatrix ρ - gramStateMatrix
      (fun x => sourceFractionalOracle input x lam *ᵥ ρ x))
      (sourceAlphabetDelta (fun x j => sourceBooleanSymbol (input x j))) ≤
      ENNReal.ofReal (lam * Real.pi * Real.sqrt 2) := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.source_single_step_distance (X := X) (W := W)
      (n := n) (input := input) (lam := lam) (hlam := hlam) (ρ := ρ) (hρ := hρ)

end Qatlib.Papers.StateConvLee10.ContQueries
