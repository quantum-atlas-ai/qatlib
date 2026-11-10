/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QComplexity97.PrecisionModel

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

theorem one_opNorm {d : ℕ} [NeZero d] :
    ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ = 1 := by
  rw [Matrix.cstar_norm_def]
  have h : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (1 : Matrix (Fin d) (Fin d) ℂ) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) := by
    ext x
    simp [Matrix.toEuclideanCLM]
  rw [h, ContinuousLinearMap.norm_id]

theorem unitary_opNorm_eq_one {d : ℕ} [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) : ‖U‖ = 1 := by
  have h : ‖U‖ * ‖U‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hU, one_opNorm]
  have hnn : (0 : ℝ) ≤ ‖U‖ := norm_nonneg _
  have hsq : ‖U‖ ^ 2 = 1 := by rw [pow_two]; exact h
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · exact h1
  · rw [h1] at hnn; linarith

theorem unitary_adjoint_opNorm_eq_one {d : ℕ} [NeZero d]
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) : ‖Uᴴ‖ = 1 := by
  rw [Matrix.l2_opNorm_conjTranspose, unitary_opNorm_eq_one U hU]

theorem entrywise_opNorm_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i j, ‖M i j‖ ≤ ε) : ‖M‖ ≤ (d : ℝ) * ε := by
  classical
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg d) hε) (fun x => ?_)
  have hcoord : ∀ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) i‖ ≤ ε * ∑ j, ‖x j‖ := by
    intro i
    have hxi : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) i = ∑ j, M i j * x j := by
      have hx := congrFun (Matrix.ofLp_toEuclideanCLM (n := Fin d) M x) i
      simp only [Matrix.mulVec, dotProduct] at hx
      exact hx
    rw [hxi]
    calc ‖∑ j, M i j * x j‖ ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
      _ = ∑ j, ‖M i j‖ * ‖x j‖ := by simp
      _ ≤ ∑ j, ε * ‖x j‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = ε * ∑ j, ‖x j‖ := by rw [Finset.mul_sum]
  set S : ℝ := ∑ j, ‖x j‖ with hS
  have hsq : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ ^ 2 ≤ ((d : ℝ) * ε) ^ 2 * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) i‖ ^ 2
        ≤ ∑ _i : Fin d, (ε * S) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hcoord i
          have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          simpa [hS] using h2
      _ = (d : ℝ) * (ε * S) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = (d : ℝ) * ε ^ 2 * S ^ 2 := by ring
      _ ≤ (d : ℝ) * ε ^ 2 * ((d : ℝ) * ∑ j, ‖x j‖ ^ 2) := by
          have hCS : S ^ 2 ≤ (d : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
            have := sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (Fin d))) (f := fun j => ‖x j‖)
            simpa [hS, Finset.card_univ] using this
          have hcoef : (0 : ℝ) ≤ (d : ℝ) * ε ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left hCS hcoef
      _ = ((d : ℝ) * ε) ^ 2 * ‖x‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]; ring
  have hnonneg : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ (d : ℝ) * ε * ‖x‖ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hε) (norm_nonneg _)
  have hle := (sq_le_sq₀ hnonneg hrhs).mp ?_
  · calc ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ := rfl
      _ ≤ (d : ℝ) * ε * ‖x‖ := hle
  · calc ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ ^ 2
        ≤ ((d : ℝ) * ε) ^ 2 * ‖x‖ ^ 2 := hsq
      _ = ((d : ℝ) * ε * ‖x‖) ^ 2 := by ring

theorem norm_mul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U₁ U₁' U₂ U₂' : E →L[ℂ] E)
    (h₁ : ∀ x, ‖U₁' x‖ = ‖x‖) (h₂ : ∀ x, ‖U₂ x‖ = ‖x‖) :
    ‖U₁' * U₂' - U₁ * U₂‖ ≤ ‖U₁' - U₁‖ + ‖U₂' - U₂‖ := by
  have hfac : U₁' * U₂' - U₁ * U₂ = U₁' * (U₂' - U₂) + (U₁' - U₁) * U₂ := by
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, map_sub]
    abel
  have hnorm₁ : ‖U₁'‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using (h₁ x).le)
  have hnorm₂ : ‖U₂‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using (h₂ x).le)
  calc ‖U₁' * U₂' - U₁ * U₂‖ = ‖U₁' * (U₂' - U₂) + (U₁' - U₁) * U₂‖ := by rw [hfac]
    _ ≤ ‖U₁' * (U₂' - U₂)‖ + ‖(U₁' - U₁) * U₂‖ := norm_add_le _ _
    _ ≤ ‖U₁'‖ * ‖U₂' - U₂‖ + ‖U₁' - U₁‖ * ‖U₂‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * ‖U₂' - U₂‖ + ‖U₁' - U₁‖ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hnorm₁ (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hnorm₂ (norm_nonneg _))
    _ = ‖U₂' - U₂‖ + ‖U₁' - U₁‖ := by rw [one_mul, mul_one]
    _ = ‖U₁' - U₁‖ + ‖U₂' - U₂‖ := by ring

theorem norm_preserving_iff_adjoint_comp_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : H →L[ℂ] H) :
    (∀ x, ‖u x‖ = ‖x‖) ↔ ContinuousLinearMap.adjoint u ∘L u = 1 :=
  ContinuousLinearMap.norm_map_iff_adjoint_comp_self u

theorem norm_preserving_iff_inner_preserving
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : H →L[ℂ] H) :
    (∀ x, ‖u x‖ = ‖x‖) ↔
      (∀ x y : H, ⟪u x, u y⟫_ℂ = ⟪x, y⟫_ℂ) := by
  rw [LinearMap.norm_map_iff_inner_map_map]

theorem norm_preserving_iff_two_sided_unitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [CompleteSpace H] (u : H →L[ℂ] H) :
    (∀ x, ‖u x‖ = ‖x‖) ↔
      (ContinuousLinearMap.adjoint u ∘L u = 1 ∧
        u ∘L ContinuousLinearMap.adjoint u = 1) := by
  constructor
  · intro h
    have hleft := (norm_preserving_iff_adjoint_comp_self u).mp h
    refine ⟨hleft, ?_⟩
    have hinj : Function.Injective u := by
      intro x y hxy
      have h2 : (ContinuousLinearMap.adjoint u ∘L u) x =
          (ContinuousLinearMap.adjoint u ∘L u) y := by
        simp only [ContinuousLinearMap.comp_apply, hxy]
      rw [hleft] at h2
      simpa using h2
    have hsurj : Function.Surjective u :=
      LinearMap.injective_iff_surjective.mp hinj
    ext z
    obtain ⟨w, rfl⟩ := hsurj z
    have hfix : (u ∘L ContinuousLinearMap.adjoint u) (u w) = u w := by
      have h2 : ContinuousLinearMap.adjoint u (u w) =
          (ContinuousLinearMap.adjoint u ∘L u) w := rfl
      simp only [ContinuousLinearMap.comp_apply]
      rw [h2, hleft]
      simp
    simpa using hfix
  · rintro ⟨hleft, -⟩
    exact (norm_preserving_iff_adjoint_comp_self u).mpr hleft

end Qatlib.Papers.QComplexity97.PrecisionModel
