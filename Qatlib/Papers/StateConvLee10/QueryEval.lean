/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan

/-!
# Function evaluation from adversary bounds

This module relates bounded-error function-evaluation query cost to the adversary quantity up to
a universal positive constant. A finite adversary bound also gives a legal query word that
returns the function value with probability at least two thirds, following [LeeEtAl2011].

## Main statements

* `source_function_queries`: adversary and query cost bound each other, with legal witnessing
  words for finite budgets.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.StateConversion
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.ConversionCore.WitnessCompile

namespace Qatlib.Papers.StateConvLee10.QueryEval

/-- A universal positive constant compares function-evaluation query cost with the adversary
quantity in both directions; an adversary bound `W ≥ 0` also yields a legal word using at
most `ceil (c * W)` queries and succeeding with probability at least two thirds
[LeeEtAl2011]. -/
theorem source_function_queries :
  ∃ c : ℕ, 0<c ∧ ∀ (X E : Type) [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (n q : ℕ) (input : X → Fin n → Fin (q+1)) (f : X → E),
    sourceAdversary (sourceAlphabetDelta input) f ≤ c*sourceFunctionQ input f ∧
    sourceFunctionQ input f ≤ c*sourceAdversary (sourceAlphabetDelta input) f ∧
    (∀ W : ℝ, 0 ≤ W → sourceAdversary (sourceAlphabetDelta input) f ≤ ENNReal.ofReal W →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q (Option E) r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*W) ∧ ∀ x,
        MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (Ket none))
          (Finset.univ.filter (fun p => p.2.1.2=some (f x))) ≥ 2/3) := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.functionEvaluationAdversaryAlgorithm

end Qatlib.Papers.StateConvLee10.QueryEval
