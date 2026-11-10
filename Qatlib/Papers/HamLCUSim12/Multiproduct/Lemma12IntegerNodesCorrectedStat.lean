/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesAuxiliary
set_option warningAsError false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Real
open scoped BigOperators

noncomputable def Lemma12IntegerNodesCorrected : Prop :=
  ∀ η : ℝ, 305 / 1000 < η → η < 312 / 1000 →
  ∀ k : ℕ, 1 ≤ k →
  ∀ m h t ε β : ℝ, 1 ≤ m → 0 < h → 0 < t → 0 < ε → 0 < β → β < 1 →
  ∀ C : ℕ → ℝ,
    (∑ q ∈ Finset.Icc 1 (k + 1), C q = 1) →
    (∀ q ∈ Finset.Icc 1 k,
      |C q| ≤ 2^(1 / 2 : ℝ) * (k : ℝ)^(3 / 2 : ℝ)
        * exp (2 * (k : ℝ) * (1 + log η / 2 - correctedGamma η k))) →
    1 ≤ integerNode η k
    ∧ (k : ℝ) < ((integerNode η k : ℤ) : ℝ)
    ∧ exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ)) = ((integerNode η k : ℤ) : ℝ)
    ∧ gammaReq η k ≤ correctedGamma η k
    ∧ correctedGamma η k ≤ 2
    ∧ exp (correctedGamma η k * (k : ℝ))
      ≤ 2^(11 / 4 : ℝ) * (k : ℝ)^(5 / 4 : ℝ) * exp ((k : ℝ) * (1 + log η / 2))
    ∧ 2 * (k : ℝ)^2 ≤ ((integerNode η k : ℤ) : ℝ)^2
    ∧ (∑ q ∈ Finset.Icc 1 k, |C q| ≤ 1 / 8)
    ∧ (∀ q ∈ Finset.Icc 1 (k + 1), |C q| ≤ 2)
    ∧ (8 * ∑ q ∈ Finset.filter (fun q => C q < 0) (Finset.Icc 1 (k + 1)), |C q|
      ≤ ∑ q ∈ Finset.filter (fun q => 0 < C q) (Finset.Icc 1 (k + 1)), C q)
    ∧ (1 ≤ retryCount m h t ε β k
      ∧ ((4 * m * ((5 : ℝ) / 3)^(k - 1) * h * t)^(1 + 1 / ((4 : ℝ) * (k : ℝ)))
        / ((errorBudget m h t ε β k / 5)^(1 / ((4 : ℝ) * (k : ℝ))))
        ≤ ((retryCount m h t ε β k : ℤ) : ℝ))
      ∧ (13 * log (2 / β) ≤ ((retryCount m h t ε β k : ℤ) : ℝ))
      ∧ (10 * m * ((5 : ℝ)^(k - 1)) * (k : ℝ) * ((integerNode η k : ℤ) : ℝ)
        * ((retryCount m h t ε β k : ℤ) : ℝ)
        ≤ 1000 * m * ((5 : ℝ)^(k - 1)) * (k : ℝ)^(9 / 4 : ℝ)
        * exp ((1 + log η / 2) * (k : ℝ)) * ((retryCount m h t ε β k : ℤ) : ℝ)))

end Qatlib.Papers.HamLCUSim12.Multiproduct
