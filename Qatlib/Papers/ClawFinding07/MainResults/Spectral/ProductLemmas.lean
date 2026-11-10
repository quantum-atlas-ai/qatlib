/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.Spectral.ChainProduct
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower (IsTransitionMatrix)
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem sqNorm_nonneg (v : I → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

theorem dot_comm (u v : I → ℝ) : dot u v = dot v u := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot_add_right (u v w : I → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem col_sum_of_symm_row_sum {P : I → I → ℝ} (hsym : ∀ i j, P i j = P j i)
    (hrow : ∀ i, ∑ j, P i j = 1) : ∀ j, ∑ i, P i j = 1 := by
  intro j
  rw [← hrow j]
  exact Finset.sum_congr rfl fun i _ => hsym i j

theorem sum_snd_fst (V : I × J → ℝ) : ∑ y, ∑ x, V (x, y) = ∑ p : I × J, V p := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem act_prod_apply (P : I → I → ℝ) (Q : J → J → ℝ) (V : I × J → ℝ) (x : I) (y : J) :
    act (chainProduct P Q) V (x, y) = ∑ x', ∑ y', P x x' * Q y y' * V (x', y') := by
  simp only [act, chainProduct, Fintype.sum_prod_type]

theorem act_prod_twoStage (P : I → I → ℝ) (Q : J → J → ℝ) (V : I × J → ℝ) (x : I) (y : J) :
    act (chainProduct P Q) V (x, y)
      = act P (fun x' => act Q (fun y' => V (x', y')) y) x := by
  rw [act_prod_apply]
  simp only [act, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by ring

theorem act_prod_right {P : I → I → ℝ} {Q : J → J → ℝ}
    (hProw : ∀ x, ∑ x', P x x' = 1) (u : J → ℝ) :
    act (chainProduct P Q) (fun p : I × J => u p.2) = fun p => act Q u p.2 := by
  funext p
  obtain ⟨x, y⟩ := p
  rw [act_prod_apply]
  simp only [act]
  calc ∑ x', ∑ y', P x x' * Q y y' * u y'
      = ∑ x', P x x' * (∑ y', Q y y' * u y') := by
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y' _ => by ring
    _ = (∑ x', P x x') * (∑ y', Q y y' * u y') := by rw [← Finset.sum_mul]
    _ = ∑ y', Q y y' * u y' := by rw [hProw x, one_mul]

theorem act_prod_left {P : I → I → ℝ} {Q : J → J → ℝ}
    (hQrow : ∀ y, ∑ y', Q y y' = 1) (v : I → ℝ) :
    act (chainProduct P Q) (fun p : I × J => v p.1) = fun p => act P v p.1 := by
  funext p
  obtain ⟨x, y⟩ := p
  rw [act_prod_apply]
  simp only [act]
  calc ∑ x', ∑ y', P x x' * Q y y' * v x'
      = ∑ x', (∑ y', P x x' * Q y y') * v x' := by
        refine Finset.sum_congr rfl fun x' _ => ?_
        exact (Finset.sum_mul ..).symm
    _ = ∑ x', (P x x' * (∑ y', Q y y')) * v x' := by
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [← Finset.mul_sum]
    _ = ∑ x', P x x' * v x' := by simp [hQrow]

theorem act_prod_row_sum_zero {P : I → I → ℝ} {Q : J → J → ℝ}
    (hQcol : ∀ y', ∑ y, Q y y' = 1)
    {W : I × J → ℝ} (hWrow : ∀ x, ∑ y, W (x, y) = 0) :
    ∀ x, ∑ y, act (chainProduct P Q) W (x, y) = 0 := by
  intro x
  have hstage : ∀ y, act (chainProduct P Q) W (x, y)
      = act P (fun x' => act Q (fun y' => W (x', y')) y) x := fun y =>
    act_prod_twoStage P Q W x y
  calc ∑ y, act (chainProduct P Q) W (x, y)
      = ∑ y, act P (fun x' => act Q (fun y' => W (x', y')) y) x := by
        refine Finset.sum_congr rfl fun y _ => hstage y
    _ = ∑ y, ∑ x', P x x' * act Q (fun y' => W (x', y')) y := by simp only [act]
    _ = ∑ x', ∑ y, P x x' * act Q (fun y' => W (x', y')) y := Finset.sum_comm
    _ = ∑ x', P x x' * ∑ y, act Q (fun y' => W (x', y')) y := by
          refine Finset.sum_congr rfl fun x' _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ x', P x x' * ∑ y, W (x', y) := by
          refine Finset.sum_congr rfl fun x' _ => ?_
          rw [sum_act (P := Q) hQcol (fun y' => W (x', y'))]
    _ = 0 := by simp [hWrow]

theorem act_prod_col_sum_zero {P : I → I → ℝ} {Q : J → J → ℝ}
    (hPcol : ∀ x', ∑ x, P x x' = 1)
    {W : I × J → ℝ} (hWcol : ∀ y, ∑ x, W (x, y) = 0) :
    ∀ y, ∑ x, act (chainProduct P Q) W (x, y) = 0 := by
  intro y
  have hstage : ∀ x, act (chainProduct P Q) W (x, y)
      = act P (fun x' => act Q (fun y' => W (x', y')) y) x := fun x =>
    act_prod_twoStage P Q W x y
  calc ∑ x, act (chainProduct P Q) W (x, y)
      = ∑ x, act P (fun x' => act Q (fun y' => W (x', y')) y) x := by
        refine Finset.sum_congr rfl fun x _ => hstage x
    _ = ∑ x, ∑ x', P x x' * act Q (fun y' => W (x', y')) y := by simp only [act]
    _ = ∑ x', ∑ x, P x x' * act Q (fun y' => W (x', y')) y := Finset.sum_comm
    _ = ∑ x', (∑ x, P x x') * act Q (fun y' => W (x', y')) y := by
          refine Finset.sum_congr rfl fun x' _ => ?_
          exact (Finset.sum_mul ..).symm
    _ = ∑ x', act Q (fun y' => W (x', y')) y := by simp [hPcol]
    _ = ∑ x', ∑ y', Q y y' * W (x', y') := by simp only [act]
    _ = ∑ y', Q y y' * ∑ x', W (x', y') := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [Finset.mul_sum]
    _ = 0 := by simp [hWcol]

theorem sqNorm_act_of_doublyZero {P : I → I → ℝ} {Q : J → J → ℝ} {δ₁ δ₂ : ℝ}
    (hP : SpectralGapAtLeast P δ₁) (hQ : SpectralGapAtLeast Q δ₂)
    {W : I × J → ℝ} (hWrow : ∀ x, ∑ y, W (x, y) = 0)
    (hWcol : ∀ y, ∑ x, W (x, y) = 0) :
    sqNorm (act (chainProduct P Q) W) ≤ (1 - δ₁) ^ 2 * (1 - δ₂) ^ 2 * sqNorm W := by
  obtain ⟨hPstruct, hPsym, hPgap⟩ := hP
  obtain ⟨hQstruct, hQsym, hQgap⟩ := hQ
  obtain ⟨hQ0, hQrow⟩ := hQstruct
  have hQcol : ∀ y', ∑ y, Q y y' = 1 := col_sum_of_symm_row_sum hQsym hQrow
  set U : I × J → ℝ := fun p => act Q (fun y' => W (p.1, y')) p.2 with hU
  have hUbound : sqNorm U ≤ (1 - δ₂) ^ 2 * sqNorm W := by
    have h1 : sqNorm U = ∑ x, sqNorm (act Q (fun y' => W (x, y'))) := by
      simp only [sqNorm, hU, Fintype.sum_prod_type]
    have h2 : sqNorm W = ∑ x, sqNorm (fun y' => W (x, y')) := by
      simp only [sqNorm, Fintype.sum_prod_type]
    rw [h1, h2, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hQgap _ (hWrow x)
  have hUcol : ∀ y, ∑ x, U (x, y) = 0 := by
    intro y
    calc ∑ x, U (x, y) = ∑ x, ∑ y', Q y y' * W (x, y') := by simp only [hU, act]
      _ = ∑ y', ∑ x, Q y y' * W (x, y') := Finset.sum_comm
      _ = ∑ y', Q y y' * ∑ x, W (x, y') := by
            refine Finset.sum_congr rfl fun y' _ => ?_
            rw [Finset.mul_sum]
      _ = 0 := by simp [hWcol]
  have hfun : act (chainProduct P Q) W = fun p => act P (fun x' => U (x', p.2)) p.1 := by
    funext p
    obtain ⟨x, y⟩ := p
    have := act_prod_twoStage P Q W x y
    simpa [hU] using this
  have hstage : sqNorm (act (chainProduct P Q) W)
      = ∑ y, sqNorm (act P (fun x' => U (x', y))) := by
    rw [hfun]
    simp only [sqNorm, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hUswap : sqNorm U = ∑ y, sqNorm (fun x' => U (x', y)) := by
    simp only [sqNorm, Fintype.sum_prod_type]
    exact Finset.sum_comm
  calc sqNorm (act (chainProduct P Q) W)
      = ∑ y, sqNorm (act P (fun x' => U (x', y))) := hstage
    _ ≤ ∑ y, (1 - δ₁) ^ 2 * sqNorm (fun x' => U (x', y)) :=
        Finset.sum_le_sum fun y _ => hPgap _ (hUcol y)
    _ = (1 - δ₁) ^ 2 * sqNorm U := by
        rw [hUswap, Finset.mul_sum]
    _ ≤ (1 - δ₁) ^ 2 * ((1 - δ₂) ^ 2 * sqNorm W) :=
        mul_le_mul_of_nonneg_left hUbound (sq_nonneg _)
    _ = (1 - δ₁) ^ 2 * (1 - δ₂) ^ 2 * sqNorm W := by ring

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
