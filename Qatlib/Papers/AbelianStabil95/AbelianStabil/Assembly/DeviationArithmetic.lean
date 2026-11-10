/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.Assembly
open scoped BigOperators

theorem lemma_cauchy_schwarz_l1 {Ω : Type} [Fintype Ω] (x : Ω → ℝ)
    (hx : ∀ V, 0 ≤ x V) :
    (∑ V, x V) ≤ Real.sqrt ((Fintype.card Ω : ℝ) * ∑ V, (x V) ^ 2) := by
  have hnn : 0 ≤ ∑ V, x V := Finset.sum_nonneg (fun V _ => hx V)
  have hsq : (∑ V, x V) ^ 2 ≤ (Fintype.card Ω : ℝ) * ∑ V, (x V) ^ 2 := by
    simpa [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Ω)) (f := x))
  calc (∑ V, x V) = Real.sqrt ((∑ V, x V) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card Ω : ℝ) * ∑ V, (x V) ^ 2) := Real.sqrt_le_sqrt hsq

def ScalarDeviationBound : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (x : Ω → ℝ) (ε : ℝ),
    (∀ V, 0 ≤ x V) → 0 ≤ ε →
    (∑ V, (x V) ^ 2) ≤ 4 * ε →
    (∑ V, x V) ≤ 2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε)

theorem scalar_deviation_bound : ScalarDeviationBound := by
  intro Ω _ x ε hx hε hS
  have hcard : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := by positivity
  have hcs := lemma_cauchy_schwarz_l1 x hx
  have hbound : (Fintype.card Ω : ℝ) * ∑ V, (x V) ^ 2
      ≤ (Fintype.card Ω : ℝ) * (4 * ε) :=
    mul_le_mul_of_nonneg_left hS hcard
  have hsqrt : Real.sqrt ((Fintype.card Ω : ℝ) * (4 * ε))
      = 2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε) := by
    rw [show (Fintype.card Ω : ℝ) * (4 * ε) = 4 * ((Fintype.card Ω : ℝ) * ε) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc (∑ V, x V) ≤ Real.sqrt ((Fintype.card Ω : ℝ) * ∑ V, (x V) ^ 2) := hcs
    _ ≤ Real.sqrt ((Fintype.card Ω : ℝ) * (4 * ε)) := Real.sqrt_le_sqrt hbound
    _ = 2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε) := hsqrt

end Qatlib.Papers.AbelianStabil95.AbelianStabil.Assembly
