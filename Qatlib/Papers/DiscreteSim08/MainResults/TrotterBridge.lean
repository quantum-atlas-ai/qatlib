/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.Defs
import Qatlib.Concepts.ConversionCore.WitnessCompile.ConversionBridges

/-!
# Gram-distance bounds for source evolution

Continuous source programs and fractional Boolean oracle steps are connected to
`sourceRectValue` bounds for the change in their Gram matrices. The bounds use total continuous
time and fractional-query angle, respectively, with normalization hypotheses on the state
families.

This development follows [CleveEtAl2009].

## Main statements

* `source_trotter_suzuki_distance`: continuous evolution has Gram-distance bound `(1 + π ^ 2) *
  sourceContinuousTime C`.
* `source_fractional_query_distance`: a fractional Boolean oracle step has bound `lam * π * sqrt
  2`.

## References

* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- For a legal continuous source program and normalized input state family, the
`sourceRectValue` of the Gram-matrix change is at most `ENNReal.ofReal ((1 + π ^ 2) *
sourceContinuousTime C)`. See [CleveEtAl2009]. -/
theorem source_trotter_suzuki_distance {X W : Type}
    [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1))
    (C : List (SourceContinuousStep ((Fin (n + 1) × Fin (q + 1)) × W)))
    (hC : sourceContinuousLegal C)
    (ψ : X → QState ((Fin (n + 1) × Fin (q + 1)) × W))
    (hψ : ∀ x, Normalized (ψ x)) :
    sourceRectValue
      (gramStateMatrix ψ - gramStateMatrix
        (fun x => (sourceContinuousMatrix (sourceLogOracle input x) C).mulVec (ψ x)))
      (sourceAlphabetDelta input) ≤ ENNReal.ofReal ((1 + Real.pi ^ 2) * sourceContinuousTime C) :=
  Qatlib.Concepts.ConversionCore.WitnessCompile.continuousConversion_source_program_distance
    input C hC ψ hψ

/-- For a nonnegative fractional Boolean query parameter and a normalized state family, the
`sourceRectValue` of the Gram-matrix change is at most `ENNReal.ofReal (lam * π * sqrt 2)`. -/
theorem source_fractional_query_distance {X W : Type}
    [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam : ℝ) (hlam : 0 ≤ lam)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (hρ : ∀ x, Normalized (ρ x)) :
    sourceRectValue
      (gramStateMatrix ρ - gramStateMatrix
        (fun x => (sourceFractionalOracle input x lam).mulVec (ρ x)))
      (sourceAlphabetDelta (fun x j => sourceBooleanSymbol (input x j))) ≤
      ENNReal.ofReal (lam * Real.pi * Real.sqrt 2) :=
  Qatlib.Concepts.ConversionCore.WitnessCompile.source_single_step_distance
    input lam hlam ρ hρ

end Qatlib.Papers.DiscreteSim08.MainResults
