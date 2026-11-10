/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedOpExp08.MainResults.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

namespace Qatlib.Papers.OrderedOpExp08.MainResults

theorem lemma1_taylor_remainder {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (μ Δ : ℝ) (P : ℕ) (Λ : ℝ)
    (hA : Continuous A) (hΛ : 0 ≤ Λ)
    (hbound : ∀ u ∈ Set.uIcc μ (μ + Δ), ‖A u‖ ≤ Λ) :
    ‖orderedEvolution A μ (μ + Δ) - dysonPrefix A μ (μ + Δ) P‖ ≤
      Real.exp (Λ * |Δ|) * (Λ * |Δ|) ^ (P + 1) / (Nat.factorial (P + 1) : ℝ) := by
  have h := dyson_finite_prefix_explicit_factorial_tail I A μ (μ + Δ) Λ P hA hΛ hbound
  have hsub : (μ + Δ) - μ = Δ := by ring
  simpa [hsub] using! h

theorem lemma2_uk_taylor_remainder {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (k : ℕ) :
    ‖suzukiExponentialWord xs t -
        ∑ n ∈ Finset.range (2 * k + 1), t ^ n • suzukiSeries xs n‖ ≤
      Real.exp (|t| * suzukiMass xs) * (|t| * suzukiMass xs) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ) :=
  general_trotter_taylor_tail xs t (2 * k + 1)

end Qatlib.Papers.OrderedOpExp08.MainResults
