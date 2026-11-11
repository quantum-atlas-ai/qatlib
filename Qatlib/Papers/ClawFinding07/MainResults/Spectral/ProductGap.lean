/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.Spectral.ProductLemmas

/-!
# Spectral gap bounds for product chains

This module decomposes a function on a finite product into its coordinate means and a residual
with vanishing row and column sums. The decomposition proves that product chains inherit the
minimum of two gap bounds in `[0,1]`, supporting the product-walk analysis of [Tani2009].

## Main statements

* `resid_row_sum` and `resid_col_sum`: vanishing sums for the residual.
* `spectralGap_chainProduct`: the minimum lower bound.
* `spectralGap_chainProduct_eq`: equality under the predicates `SpectralGapEquals` for both
  factors.

## References

* [Tani, 2009][Tani2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower (IsTransitionMatrix)
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

section Means

variable [Nonempty I] [Nonempty J]

/-- The real cardinality of the finite nonempty type `I` is nonzero. -/
theorem card_I_ne_zero : (Fintype.card I : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fintype.card_pos (α := I)).ne'

/-- The real cardinality of the finite nonempty type `J` is nonzero. -/
theorem card_J_ne_zero : (Fintype.card J : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fintype.card_pos (α := J)).ne'

/-- The mean of a function on `I × J` over the first coordinate, viewed as a function on `J`. -/
def colMean (V : I × J → ℝ) : J → ℝ :=
  fun y => (∑ x, V (x, y)) / (Fintype.card I : ℝ)

/-- The mean of a function on `I × J` over the second coordinate, viewed as a function on `I`. -/
def rowMean (V : I × J → ℝ) : I → ℝ :=
  fun x => (∑ y, V (x, y)) / (Fintype.card J : ℝ)

/-- The residual obtained by subtracting both coordinate means from a function on `I × J`. -/
def resid (V : I × J → ℝ) : I × J → ℝ :=
  fun p => V p - colMean V p.2 - rowMean V p.1

/-- The column means sum to zero if the original function on the product sums to zero. -/
theorem sum_colMean {V : I × J → ℝ} (hV : ∑ p, V p = 0) : ∑ y, colMean V y = 0 := by
  simp only [colMean]
  rw [← Finset.sum_div, sum_snd_fst V, hV, zero_div]

/-- The row means sum to zero if the original function on the product sums to zero. -/
theorem sum_rowMean {V : I × J → ℝ} (hV : ∑ p, V p = 0) : ∑ x, rowMean V x = 0 := by
  simp only [rowMean]
  rw [← Finset.sum_div, ← Fintype.sum_prod_type V, hV, zero_div]

/-- If the original function sums to zero, every row of its residual sums to zero. -/
theorem resid_row_sum {V : I × J → ℝ} (hV : ∑ p, V p = 0) (x : I) :
    ∑ y, resid V (x, y) = 0 := by
  have hc := sum_colMean hV
  simp only [resid, Finset.sum_sub_distrib, hc, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, rowMean]
  rw [mul_comm, div_mul_cancel₀ _ card_J_ne_zero]
  ring

/-- If the original function sums to zero, every column of its residual sums to zero. -/
theorem resid_col_sum {V : I × J → ℝ} (hV : ∑ p, V p = 0) (y : J) :
    ∑ x, resid V (x, y) = 0 := by
  have hr := sum_rowMean hV
  simp only [resid, Finset.sum_sub_distrib, hr, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, colMean]
  rw [mul_comm, div_mul_cancel₀ _ card_I_ne_zero]
  ring

end Means

/-- For finite nonempty state spaces and gap parameters in `[0,1]`, the product chain satisfies
`SpectralGapAtLeast` with the minimum of the two factor parameters. -/
theorem spectralGap_chainProduct [Nonempty I] [Nonempty J]
    {P : I → I → ℝ} {Q : J → J → ℝ} {δ₁ δ₂ : ℝ}
    (hδ₁0 : 0 ≤ δ₁) (hδ₁1 : δ₁ ≤ 1) (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1)
    (hP : SpectralGapAtLeast P δ₁) (hQ : SpectralGapAtLeast Q δ₂) :
    SpectralGapAtLeast (chainProduct P Q) (min δ₁ δ₂) := by
  have hPstruct := hP.1
  have hPsym := hP.2.1
  have hPgap := hP.2.2
  have hQstruct := hQ.1
  have hQsym := hQ.2.1
  have hQgap := hQ.2.2
  have hP0 := hPstruct.1
  have hProw := hPstruct.2
  have hQ0 := hQstruct.1
  have hQrow := hQstruct.2
  have hPcol : ∀ x', ∑ x, P x x' = 1 := col_sum_of_symm_row_sum hPsym hProw
  have hQcol : ∀ y', ∑ y, Q y y' = 1 := col_sum_of_symm_row_sum hQsym hQrow
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro p q
    exact mul_nonneg (hP0 p.1 q.1) (hQ0 p.2 q.2)
  · intro p
    obtain ⟨x, y⟩ := p
    simp only [chainProduct, Fintype.sum_prod_type]
    have h : ∀ x' : I, (∑ y' : J, P x x' * Q y y') = P x x' := by
      intro x'
      rw [← Finset.mul_sum, hQrow y, mul_one]
    simp only [h, hProw x]
  · intro p q
    simp only [chainProduct, hPsym p.1 q.1, hQsym p.2 q.2]
  · intro V hV
    have hc0 : ∑ y, colMean V y = 0 := sum_colMean hV
    have hr0 : ∑ x, rowMean V x = 0 := sum_rowMean hV
    set C : I × J → ℝ := fun p => colMean V p.2 with hC
    set R : I × J → ℝ := fun p => rowMean V p.1 with hR
    set W : I × J → ℝ := resid V with hW
    have hWrow : ∀ x, ∑ y, W (x, y) = 0 := by
      intro x
      rw [hW]
      exact resid_row_sum hV x
    have hWcol : ∀ y, ∑ x, W (x, y) = 0 := by
      intro y
      rw [hW]
      exact resid_col_sum hV y
    have hVdecomp : V = C + R + W := by
      rw [hC, hR, hW]
      funext p
      simp only [Pi.add_apply, resid]
      ring
    set AC : I × J → ℝ := act (chainProduct P Q) C with hAC
    set AR : I × J → ℝ := act (chainProduct P Q) R with hAR
    set AW : I × J → ℝ := act (chainProduct P Q) W with hAW
    have hACeq : AC = fun p => act Q (colMean V) p.2 := by
      rw [hAC, hC]
      exact act_prod_right hProw (colMean V)
    have hAReq : AR = fun p => act P (rowMean V) p.1 := by
      rw [hAR, hR]
      exact act_prod_left hQrow (rowMean V)
    have hact : act (chainProduct P Q) V = AC + AR + AW := by
      rw [hVdecomp, act_add, act_add, ← hAC, ← hAR, ← hAW]

    have hbAC : sqNorm AC ≤ (1 - δ₂) ^ 2 * sqNorm C := by
      have hACsq : sqNorm AC = (Fintype.card I : ℝ) * sqNorm (act Q (colMean V)) := by
        rw [hACeq]
        exact sqNorm_prod_right
      have hCsq : sqNorm C = (Fintype.card I : ℝ) * sqNorm (colMean V) := by
        rw [hC]
        exact sqNorm_prod_right
      rw [hACsq, hCsq]
      calc (Fintype.card I : ℝ) * sqNorm (act Q (colMean V))
          ≤ (Fintype.card I : ℝ) * ((1 - δ₂) ^ 2 * sqNorm (colMean V)) :=
            mul_le_mul_of_nonneg_left (hQgap (colMean V) hc0) (by positivity)
        _ = (1 - δ₂) ^ 2 * ((Fintype.card I : ℝ) * sqNorm (colMean V)) := by ring
    have hbAR : sqNorm AR ≤ (1 - δ₁) ^ 2 * sqNorm R := by
      have hARsq : sqNorm AR = (Fintype.card J : ℝ) * sqNorm (act P (rowMean V)) := by
        rw [hAReq]
        exact sqNorm_prod_left
      have hRsq : sqNorm R = (Fintype.card J : ℝ) * sqNorm (rowMean V) := by
        rw [hR]
        exact sqNorm_prod_left
      rw [hARsq, hRsq]
      calc (Fintype.card J : ℝ) * sqNorm (act P (rowMean V))
          ≤ (Fintype.card J : ℝ) * ((1 - δ₁) ^ 2 * sqNorm (rowMean V)) :=
            mul_le_mul_of_nonneg_left (hPgap (rowMean V) hr0) (by positivity)
        _ = (1 - δ₁) ^ 2 * ((Fintype.card J : ℝ) * sqNorm (rowMean V)) := by ring
    have hbAW : sqNorm AW ≤ (1 - δ₁) ^ 2 * (1 - δ₂) ^ 2 * sqNorm W := by
      rw [hAW]
      exact sqNorm_act_of_doublyZero hP hQ hWrow hWcol

    have hsumAC : ∑ y, act Q (colMean V) y = 0 := by
      rw [sum_act (P := Q) hQcol (colMean V)]
      exact hc0
    have hdot_AC_AR : dot AC AR = 0 := by
      rw [dot_comm, hACeq, hAReq]
      exact dot_prod_split hsumAC
    have hdot_AC_AW : dot AC AW = 0 := by
      rw [hACeq]
      have hcolAW : ∀ y, ∑ x, AW (x, y) = 0 := by
        intro y
        rw [hAW]
        exact act_prod_col_sum_zero hPcol hWcol y
      simp only [dot, Fintype.sum_prod_type]
      calc ∑ x, ∑ y, act Q (colMean V) y * AW (x, y)
          = ∑ y, ∑ x, act Q (colMean V) y * AW (x, y) := Finset.sum_comm
        _ = ∑ y, act Q (colMean V) y * ∑ x, AW (x, y) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.mul_sum]
        _ = 0 := by simp [hcolAW]
    have hdot_AR_AW : dot AR AW = 0 := by
      rw [hAReq]
      have hrowAW : ∀ x, ∑ y, AW (x, y) = 0 := by
        intro x
        rw [hAW]
        exact act_prod_row_sum_zero hQcol hWrow x
      simp only [dot, Fintype.sum_prod_type]
      calc ∑ x, ∑ y, act P (rowMean V) x * AW (x, y)
          = ∑ x, act P (rowMean V) x * ∑ y, AW (x, y) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
        _ = 0 := by simp [hrowAW]
    have hdot_C_R : dot C R = 0 := by
      rw [dot_comm, hC, hR]
      exact dot_prod_split hc0
    have hdot_C_W : dot C W = 0 := by
      rw [hC]
      simp only [dot, Fintype.sum_prod_type]
      calc ∑ x, ∑ y, colMean V y * W (x, y)
          = ∑ y, ∑ x, colMean V y * W (x, y) := Finset.sum_comm
        _ = ∑ y, colMean V y * ∑ x, W (x, y) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.mul_sum]
        _ = 0 := by simp [hWcol]
    have hdot_R_W : dot R W = 0 := by
      rw [hR]
      simp only [dot, Fintype.sum_prod_type]
      calc ∑ x, ∑ y, rowMean V x * W (x, y)
          = ∑ x, rowMean V x * ∑ y, W (x, y) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
        _ = 0 := by simp [hWrow]
    have himgnorm : sqNorm (act (chainProduct P Q) V) = sqNorm AC + sqNorm AR + sqNorm AW := by
      have h1 : dot AC (AR + AW) = 0 := by
        rw [dot_add_right, hdot_AC_AR, hdot_AC_AW, add_zero]
      have h2 : dot AR AW = 0 := hdot_AR_AW
      rw [hact]
      calc sqNorm ((AC + AR) + AW) = sqNorm (AC + (AR + AW)) := by rw [add_assoc]
        _ = sqNorm AC + sqNorm (AR + AW) := sqNorm_add_of_dot_zero h1
        _ = sqNorm AC + (sqNorm AR + sqNorm AW) := by rw [sqNorm_add_of_dot_zero h2]
        _ = sqNorm AC + sqNorm AR + sqNorm AW := by ring
    have hVnorm : sqNorm V = sqNorm C + sqNorm R + sqNorm W := by
      have h1 : dot C (R + W) = 0 := by
        rw [dot_add_right, hdot_C_R, hdot_C_W, add_zero]
      have h2 : dot R W = 0 := hdot_R_W
      rw [hVdecomp]
      calc sqNorm ((C + R) + W) = sqNorm (C + (R + W)) := by rw [add_assoc]
        _ = sqNorm C + sqNorm (R + W) := sqNorm_add_of_dot_zero h1
        _ = sqNorm C + (sqNorm R + sqNorm W) := by rw [sqNorm_add_of_dot_zero h2]
        _ = sqNorm C + sqNorm R + sqNorm W := by ring

    have sqmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2 := by
      intro a b ha hab
      have h := mul_self_le_mul_self ha hab
      simpa [sq] using h
    have hcoef₁ : (1 - δ₁) ^ 2 ≤ (1 - min δ₁ δ₂) ^ 2 := by
      refine sqmono _ _ ?_ ?_
      · linarith
      · linarith [min_le_left δ₁ δ₂]
    have hcoef₂ : (1 - δ₂) ^ 2 ≤ (1 - min δ₁ δ₂) ^ 2 := by
      refine sqmono _ _ ?_ ?_
      · linarith
      · linarith [min_le_right δ₁ δ₂]
    have hcoefW : (1 - δ₁) ^ 2 * (1 - δ₂) ^ 2 ≤ (1 - min δ₁ δ₂) ^ 2 := by
      have h1le : 1 - δ₁ ≤ 1 := by linarith
      have h2le : 1 - δ₂ ≤ 1 - min δ₁ δ₂ := by linarith [min_le_right δ₁ δ₂]
      have h20 : 0 ≤ 1 - δ₂ := by linarith
      have hprod_le : (1 - δ₁) * (1 - δ₂) ≤ 1 - min δ₁ δ₂ := by
        have h := mul_le_mul h1le h2le h20 (by norm_num : (0 : ℝ) ≤ 1)
        simpa using h
      have hprod0 : 0 ≤ (1 - δ₁) * (1 - δ₂) := by
        apply mul_nonneg <;> linarith
      have h := sqmono _ _ hprod0 hprod_le
      simpa only [mul_pow] using h
    have hAC' : sqNorm AC ≤ (1 - min δ₁ δ₂) ^ 2 * sqNorm C :=
      le_trans hbAC (mul_le_mul_of_nonneg_right hcoef₂ (sqNorm_nonneg C))
    have hAR' : sqNorm AR ≤ (1 - min δ₁ δ₂) ^ 2 * sqNorm R :=
      le_trans hbAR (mul_le_mul_of_nonneg_right hcoef₁ (sqNorm_nonneg R))
    have hAW' : sqNorm AW ≤ (1 - min δ₁ δ₂) ^ 2 * sqNorm W :=
      le_trans hbAW (mul_le_mul_of_nonneg_right hcoefW (sqNorm_nonneg W))
    change sqNorm (act (chainProduct P Q) V) ≤ (1 - min δ₁ δ₂) ^ 2 * sqNorm V
    rw [himgnorm]
    calc sqNorm AC + sqNorm AR + sqNorm AW
        ≤ (1 - min δ₁ δ₂) ^ 2 * sqNorm C + (1 - min δ₁ δ₂) ^ 2 * sqNorm R
            + (1 - min δ₁ δ₂) ^ 2 * sqNorm W := by linarith
      _ = (1 - min δ₁ δ₂) ^ 2 * (sqNorm C + sqNorm R + sqNorm W) := by ring
      _ = (1 - min δ₁ δ₂) ^ 2 * sqNorm V := by rw [hVnorm]

/-- If both factor gap parameters satisfy `SpectralGapEquals`, every parameter satisfying
`SpectralGapAtLeast` for the product is at most their minimum; see [Tani2009]. -/
theorem spectralGap_chainProduct_le [Nonempty I] [Nonempty J]
    {P : I → I → ℝ} {Q : J → J → ℝ} {δ₁ δ₂ δ : ℝ}
    (hP : SpectralGapEquals P δ₁) (hQ : SpectralGapEquals Q δ₂)
    (hprod : SpectralGapAtLeast (chainProduct P Q) δ) : δ ≤ min δ₁ δ₂ := by
  have hPgap := hP.1
  have hPmax := hP.2
  have hQgap := hQ.1
  have hQmax := hQ.2
  have hPstruct := hPgap.1
  have hPsym := hPgap.2.1
  have hQstruct := hQgap.1
  have hQsym := hQgap.2.1
  have hProw := hPstruct.2
  have hQrow := hQstruct.2
  obtain ⟨-, -, hprodgap⟩ := hprod
  have hPle : SpectralGapAtLeast P δ := by
    refine ⟨hPstruct, hPsym, ?_⟩
    intro v hv
    have hVsum : ∑ p : I × J, v p.1 = 0 := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, hv, mul_zero]
    have hprod_v : sqNorm (act (chainProduct P Q) (fun p : I × J => v p.1))
        ≤ (1 - δ) ^ 2 * sqNorm (fun p : I × J => v p.1) :=
      hprodgap (fun p : I × J => v p.1) hVsum
    rw [act_prod_left hQrow v, sqNorm_prod_left, sqNorm_prod_left] at hprod_v
    have hpos : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos (α := J)
    have hprod' : (Fintype.card J : ℝ) * sqNorm (act P v)
        ≤ (Fintype.card J : ℝ) * ((1 - δ) ^ 2 * sqNorm v) := by
      calc (Fintype.card J : ℝ) * sqNorm (act P v)
          ≤ (1 - δ) ^ 2 * ((Fintype.card J : ℝ) * sqNorm v) := hprod_v
        _ = (Fintype.card J : ℝ) * ((1 - δ) ^ 2 * sqNorm v) := by ring
    exact le_of_mul_le_mul_left hprod' hpos
  have hQle : SpectralGapAtLeast Q δ := by
    refine ⟨hQstruct, hQsym, ?_⟩
    intro u hu
    have hVsum : ∑ p : I × J, u p.2 = 0 := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hu, mul_zero]
    have hprod_u : sqNorm (act (chainProduct P Q) (fun p : I × J => u p.2))
        ≤ (1 - δ) ^ 2 * sqNorm (fun p : I × J => u p.2) :=
      hprodgap (fun p : I × J => u p.2) hVsum
    rw [act_prod_right hProw u, sqNorm_prod_right, sqNorm_prod_right] at hprod_u
    have hpos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
    have hprod' : (Fintype.card I : ℝ) * sqNorm (act Q u)
        ≤ (Fintype.card I : ℝ) * ((1 - δ) ^ 2 * sqNorm u) := by
      calc (Fintype.card I : ℝ) * sqNorm (act Q u)
          ≤ (1 - δ) ^ 2 * ((Fintype.card I : ℝ) * sqNorm u) := hprod_u
        _ = (Fintype.card I : ℝ) * ((1 - δ) ^ 2 * sqNorm u) := by ring
    exact le_of_mul_le_mul_left hprod' hpos
  exact le_min (hPmax δ hPle) (hQmax δ hQle)

/-- For finite nonempty state spaces and exact factor parameters in `[0,1]`, the product
satisfies `SpectralGapEquals` with their minimum. -/
theorem spectralGap_chainProduct_eq [Nonempty I] [Nonempty J]
    {P : I → I → ℝ} {Q : J → J → ℝ} {δ₁ δ₂ : ℝ}
    (hδ₁0 : 0 ≤ δ₁) (hδ₁1 : δ₁ ≤ 1) (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1)
    (hP : SpectralGapEquals P δ₁) (hQ : SpectralGapEquals Q δ₂) :
    SpectralGapEquals (chainProduct P Q) (min δ₁ δ₂) := by
  refine ⟨spectralGap_chainProduct hδ₁0 hδ₁1 hδ₂0 hδ₂1 hP.1 hQ.1, ?_⟩
  intro δ h
  exact spectralGap_chainProduct_le hP hQ h

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
