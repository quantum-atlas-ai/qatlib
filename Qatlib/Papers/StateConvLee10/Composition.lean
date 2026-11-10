/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.QueryDirectSumConsumerQuan
import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.ConversionCore.WitnessCompile

namespace Qatlib.Papers.StateConvLee10.Composition

theorem source_function_composition :
  (∀ (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
      [Fintype E] [DecidableEq E] (n m q a : ℕ)
      (inner : X → Fin n → Fin (q+1)) (g : X → Fin (a+1))
      (outer : Y → Fin m → Fin (a+1)) (f : Y → E),
      let D := {p : Y × (Fin m → X) // ∀ j, outer p.1 j=g (p.2 j)}
      let input := fun p : D => sourceIndependentInput inner m p.1.2
      let result := fun p : D => f p.1.1
      (sourceAdversary (sourceAlphabetDelta outer) f < ⊤ ∨
        sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner) ≠ 0) →
      sourceAdversary (sourceAlphabetDelta input) result ≤
        sourceAdversary (sourceAlphabetDelta outer) f *
          sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner)) ∧
  (∀ (X E : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
      (n m q : ℕ) (inner : X → Fin n → Fin (q+1)) (g : X → Bool)
      (f : (Fin m → Bool) → E),
      sourceAdversary (sourceAlphabetDelta (sourceIndependentInput inner m))
        (fun xs => f (fun j => g (xs j))) ≥
        sourceAdversary (sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j))) f *
          sourceAdversary (sourceAlphabetDelta inner) g) := by
  exact Qatlib.Concepts.GramQueryCore.GammaDuality.functionCompositionBounds

theorem source_query_direct_sum :
  ∃ c : ℕ, 0<c ∧ ∀ (X E : Type) [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (n m q : ℕ)
    (input : X → Fin n → Fin (q+1)) (f : X → E),
    let many := fun xs : Fin m → X => fun j => f (xs j)
    let allInput := sourceIndependentInput input m
    (m : ℝ≥0∞)*sourceFunctionQ input f ≤ c*sourceFunctionQ allInput many ∧
    sourceFunctionQ allInput many ≤ c*(m : ℝ≥0∞)*sourceFunctionQ input f ∧
    (∀ Q : ℝ, 0 ≤ Q → sourceFunctionQ input f ≤ ENNReal.ofReal Q →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace (m*n) q (Option (Fin m → E)) r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*m*Q) ∧ ∀ xs,
        MeasureProb (sourceWordMatrix (sourceAlphabetOracle allInput xs) C *ᵥ
          sourceClean (m*n) q r hr false (Ket none))
          (Finset.univ.filter (fun p => p.2.1.2=some (many xs))) ≥ 2/3) := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.queryDirectSumConsumer

end Qatlib.Papers.StateConvLee10.Composition
