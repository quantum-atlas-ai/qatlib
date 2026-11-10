/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterOrderedCommutatorStat
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem trotterOrderedCommutator_coefficients (I : Type) [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (n : ℕ) :
    pfConjCoeff xs B n =
      ∑ q ∈ pfCompositions xs.length n,
        (∏ i, ((q i).factorial : ℝ))⁻¹ •
          pfNestedCommList (B :: pfOrderedCompositionWord xs q) :=
  pfConjCoeff_ordered xs B n

theorem trotterOrderedCommutator_skew_budget (I : Type) [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hxs : ∀ X∈xs, Xᴴ=-X) :
    ‖pfConjWord xs B t-pfConjTrunc xs B p t‖ ≤
      pfOrderedAdBudget xs B p LinearMap.id * |t|^p := by
  simpa only [pfWordInflation_true, mul_one] using!
    pfConjWord_ordered_remainder_norm_mode true xs B p t (fun _ => hxs)

theorem trotterOrderedCommutator_general_budget (I : Type) [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    ‖pfConjWord xs B t-pfConjTrunc xs B p t‖ ≤
      pfOrderedAdBudget xs B p LinearMap.id * |t|^p * Real.exp (2 * |t| * suzukiMass xs) := by
  simpa only [pfWordInflation_false] using!
    pfConjWord_ordered_remainder_norm_mode false xs B p t (by simp)

theorem trotterOrderedCommutator_empty_counterexample :
    ‖pfConjWord [] ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 -
      pfConjTrunc [] ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0‖ = 2 ∧
    pfCommAlphaOrdered [] ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 = 1 := by
  constructor
  · simp [pfConjWord, pfConjTrunc, norm_smul]
  · exact pfCommAlphaOrdered_nil_zero _

theorem trotterOrderedCommutator_refuted : ¬ TrotterOrderedCommutatorLegacy := by
  intro h
  have hs := (h (Fin 1) [] ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0).2.1 0 (by simp)
  rw [trotterOrderedCommutator_empty_counterexample.1,
    trotterOrderedCommutator_empty_counterexample.2] at hs
  norm_num at hs

theorem trotterOrderedCommutator : TrotterOrderedCommutator := by
  intro I _ _ xs B p
  refine ⟨fun n => trotterOrderedCommutator_coefficients I xs B n, ?_, ?_⟩
  · intro t hxs
    rw [pfCommAlphaOrderedV2_scaled]
    exact trotterOrderedCommutator_skew_budget I xs B p t hxs
  · intro t
    rw [pfCommAlphaOrderedV2_scaled]
    exact trotterOrderedCommutator_general_budget I xs B p t

end Qatlib.Concepts.TrotterFormula.GeneralOrder
