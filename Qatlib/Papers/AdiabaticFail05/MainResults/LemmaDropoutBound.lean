/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.MainResults

open scoped BigOperators ComplexInnerProductSpace
open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem lemma2_sum_sq_dist_lower_bound
    (L : ℕ) (e : Fin L → V) (he : Orthonormal ℂ e)
    (ψ : Fin L → V) (hψ : ∀ i, ‖ψ i‖ = 1)
    (b : ℝ) (hproj : ∀ i, b ≤ ‖⟪e i, ψ i⟫‖ ^ 2)
    (φ : V) (hφ : ‖φ‖ = 1) :
    b * (L : ℝ) - 2 * Real.sqrt (L : ℝ) ≤ ∑ i : Fin L, ‖ψ i - φ‖ ^ 2 := by

  let a : Fin L → ℝ := fun i => ‖⟪e i, ψ i⟫‖
  let c : Fin L → ℝ := fun i => ‖⟪e i, φ⟫‖

  have hstep : ∀ i : Fin L, a i ^ 2 - 2 * a i * c i ≤ ‖ψ i - φ‖ ^ 2 := by
    intro i
    have hei : ‖e i‖ = 1 := he.1 i

    have hinner : ‖⟪e i, ψ i - φ⟫‖ ≤ ‖ψ i - φ‖ := by
      calc ‖⟪e i, ψ i - φ⟫‖ ≤ ‖e i‖ * ‖ψ i - φ‖ := norm_inner_le_norm _ _
        _ = ‖ψ i - φ‖ := by rw [hei, one_mul]

    have hbound : |a i - c i| ≤ ‖ψ i - φ‖ := by
      have hsplit : ⟪e i, ψ i - φ⟫ = ⟪e i, ψ i⟫ - ⟪e i, φ⟫ := inner_sub_right _ _ _
      calc |a i - c i| = |‖⟪e i, ψ i⟫‖ - ‖⟪e i, φ⟫‖| := rfl
        _ ≤ ‖⟪e i, ψ i⟫ - ⟪e i, φ⟫‖ := abs_norm_sub_norm_le _ _
        _ = ‖⟪e i, ψ i - φ⟫‖ := by rw [hsplit]
        _ ≤ ‖ψ i - φ‖ := hinner

    have hsq : (a i - c i) ^ 2 ≤ ‖ψ i - φ‖ ^ 2 := by
      calc (a i - c i) ^ 2 = |a i - c i| ^ 2 := (sq_abs _).symm
        _ ≤ ‖ψ i - φ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbound 2

    have hexp : (a i - c i) ^ 2 = a i ^ 2 - 2 * a i * c i + c i ^ 2 := by ring
    nlinarith [hsq, hexp, sq_nonneg (c i)]

  have hsum_step : ∑ i : Fin L, (a i ^ 2 - 2 * a i * c i) ≤ ∑ i : Fin L, ‖ψ i - φ‖ ^ 2 :=
    sum_le_sum (fun i _ => hstep i)

  have hsum_a_ge : b * (L : ℝ) ≤ ∑ i : Fin L, a i ^ 2 := by
    have hb : ∑ _i : Fin L, b ≤ ∑ i : Fin L, a i ^ 2 := sum_le_sum (fun i _ => hproj i)
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hb

  have hsum_a_le : ∑ i : Fin L, a i ^ 2 ≤ (L : ℝ) := by
    have hone : ∀ i : Fin L, a i ^ 2 ≤ (1 : ℝ) := by
      intro i
      have hai : a i = ‖⟪e i, ψ i⟫‖ := rfl
      have hle : a i ≤ 1 := by
        rw [hai]
        calc ‖⟪e i, ψ i⟫‖ ≤ ‖e i‖ * ‖ψ i‖ := norm_inner_le_norm _ _
          _ = 1 := by rw [he.1 i, hψ i, mul_one]
      have hnn : 0 ≤ a i := by rw [hai]; exact norm_nonneg _
      nlinarith [hle, hnn]
    calc ∑ i : Fin L, a i ^ 2 ≤ ∑ _i : Fin L, (1 : ℝ) := sum_le_sum (fun i _ => hone i)
      _ = (L : ℝ) := by simp

  have hsum_c_le : ∑ i : Fin L, c i ^ 2 ≤ (1 : ℝ) := by
    have hbessel := he.sum_inner_products_le (𝕜 := ℂ) (x := φ) (s := Finset.univ)
    have hb : ∑ i : Fin L, c i ^ 2 ≤ ‖φ‖ ^ 2 := by simpa [c] using hbessel
    simpa [hφ] using hb

  have hcs : ∑ i : Fin L, a i * c i ≤ Real.sqrt (L : ℝ) := by
    have hSnn : 0 ≤ ∑ i : Fin L, a i * c i :=
      sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hAn : 0 ≤ ∑ i : Fin L, a i ^ 2 := sum_nonneg (fun i _ => sq_nonneg (a i))
    have hBn : 0 ≤ ∑ i : Fin L, c i ^ 2 := sum_nonneg (fun i _ => sq_nonneg (c i))
    have hsq : (∑ i : Fin L, a i * c i) ^ 2 ≤ (∑ i : Fin L, a i ^ 2) * ∑ i : Fin L, c i ^ 2 := by
      simpa using sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin L)) a c
    have hsqrt : ∑ i : Fin L, a i * c i ≤ Real.sqrt ((∑ i : Fin L, a i ^ 2) * ∑ i : Fin L, c i ^ 2) := by
      rw [← Real.sqrt_sq hSnn]
      exact Real.sqrt_le_sqrt hsq
    have hprod : Real.sqrt ((∑ i : Fin L, a i ^ 2) * ∑ i : Fin L, c i ^ 2) =
        Real.sqrt (∑ i : Fin L, a i ^ 2) * Real.sqrt (∑ i : Fin L, c i ^ 2) := Real.sqrt_mul hAn _
    rw [hprod] at hsqrt
    have h1 : Real.sqrt (∑ i : Fin L, a i ^ 2) ≤ Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt hsum_a_le
    have h2 : Real.sqrt (∑ i : Fin L, c i ^ 2) ≤ 1 := by
      have : Real.sqrt (∑ i : Fin L, c i ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum_c_le
      simpa using this
    calc ∑ i : Fin L, a i * c i
        ≤ Real.sqrt (∑ i : Fin L, a i ^ 2) * Real.sqrt (∑ i : Fin L, c i ^ 2) := hsqrt
      _ ≤ Real.sqrt (L : ℝ) * 1 :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (L : ℝ) := mul_one _

  have h2sum : 2 * (∑ i : Fin L, a i * c i) = ∑ i : Fin L, 2 * a i * c i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsplit_sum : ∑ i : Fin L, (a i ^ 2 - 2 * a i * c i)
      = (∑ i : Fin L, a i ^ 2) - 2 * ∑ i : Fin L, a i * c i := by
    rw [Finset.sum_sub_distrib, h2sum]
  have hmain : b * (L : ℝ) - 2 * Real.sqrt (L : ℝ) ≤ ∑ i : Fin L, (a i ^ 2 - 2 * a i * c i) := by
    rw [hsplit_sum]
    nlinarith [hsum_a_ge, hcs]
  calc b * (L : ℝ) - 2 * Real.sqrt (L : ℝ)
      ≤ ∑ i : Fin L, (a i ^ 2 - 2 * a i * c i) := hmain
    _ ≤ ∑ i : Fin L, ‖ψ i - φ‖ ^ 2 := hsum_step

end Qatlib.Papers.AdiabaticFail05.MainResults
