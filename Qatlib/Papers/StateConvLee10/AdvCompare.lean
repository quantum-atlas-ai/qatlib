/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.GramQueryCore.FilteredNorm

namespace Qatlib.Papers.StateConvLee10.AdvCompare

def source_real_adversary {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) : ℝ≥0∞ :=
  sourceAdversary (sourceAlphabetDelta input) f

theorem source_adversary_comparison :
  ∀ (X E : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    (n q : ℕ) (input : X → Fin n → Fin (q+1)) (f : X → E),
    let A := gramFunctionEvaluationMatrix f
    let Z := sourceAlphabetDelta input
    sourceUnfiltered A ≤ ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ))) ∧
    sourceAdversary Z f = sourceRectValue A (fun j => Z j ⊙ A) ∧
    sourceAdversary Z f ≤ sourceRectValue A Z ∧
    sourceRectValue A Z ≤ ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ)))*sourceAdversary Z f := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.functionEvaluationNormSandwich

end Qatlib.Papers.StateConvLee10.AdvCompare
