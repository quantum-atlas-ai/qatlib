/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def FunctionEvaluationAdversaryAlgorithm : Prop :=
  ∃ c : ℕ, 0<c ∧ ∀ (X E : Type) [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (n q : ℕ) (input : X → Fin n → Fin (q+1)) (f : X → E),
    sourceAdversary (sourceAlphabetDelta input) f ≤ c*sourceFunctionQ input f ∧
    sourceFunctionQ input f ≤ c*sourceAdversary (sourceAlphabetDelta input) f ∧
    (∀ W : ℝ, 0 ≤ W → sourceAdversary (sourceAlphabetDelta input) f ≤ ENNReal.ofReal W →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q (Option E) r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*W) ∧ ∀ x,
        MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (Ket none))
          (Finset.univ.filter (fun p => p.2.1.2=some (f x))) ≥ 2/3)
end Qatlib.Concepts.ConversionCore.WitnessCompile
