/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix Exponential Norm Bound for Lower-Triangular Block Matrices

This module formalizes Lemma 6 of Krovi bounding the supremum exponential norm
`Csup (blockA F₁ 0 F₂ F₃) T` of a `2 × 2` block-triangular matrix in terms of
its diagonal block suprema `Cd F₁ T`, `Cd F₃ T` and off-diagonal block norm
`‖F₂‖`.

## Main statements

* `lemma6_block_split`: decomposition `blockA F₁ 0 F₂ F₃ = diag(F₁, F₃) + A₂`.
* `lemma6_A2_sq_zero`: nilpotence `A₂ * A₂ = 0` of the strictly lower block.
* `lemma6_Csup_diagonal`: `Csup (fromBlocks F₁ 0 0 F₃) T = max (Cd F₁ T) (Cd F₃ T)`.
* `lemma6_Csup_bound`: Lemma 6, `Csup (blockA F₁ 0 F₂ F₃) T ≤ C_d * (1 + C_d * ‖F₂‖ * T)`.

## References

* [Krovi, 2024][Krovi2024], Section 3.3, Lemma 6, Eqs. (3.19)--(3.28), pp. 18--19.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

/-- Lemma 6, Eq. (3.22): `A = A₁ + A₂` with `A₁ = diag(F₁, F₃)` and
`A₂ = [[0, 0], [F₂, 0]]`. -/
theorem lemma6_block_split
    (F₁ : Matrix N N ℂ) (F₂ : Matrix M N ℂ) (F₃ : Matrix M M ℂ) :
    blockA F₁ 0 F₂ F₃ =
      fromBlocks F₁ 0 0 F₃ + fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ 0 := by
  rw [← Matrix.one_mul F₁, ← Matrix.one_mul F₃]
  unfold blockA
  rw [Matrix.fromBlocks_add]
  simp

/-- Lemma 6, Eq. (3.26): the strictly lower block `A₂` squares to zero. -/
theorem lemma6_A2_sq_zero (F₂ : Matrix M N ℂ) :
    (fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ (0 : Matrix M M ℂ)) *
        (fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ (0 : Matrix M M ℂ)) =
      (0 : Matrix (N ⊕ M) (N ⊕ M) ℂ) := by
  rw [Matrix.fromBlocks_multiply]
  simp

omit [DecidableEq N] [DecidableEq M] in
private lemma norm_sum_sq (z : EuclideanSpace ℂ (N ⊕ M)) :
    ‖z‖ ^ 2 = ‖(WithLp.toLp 2 (z ∘ Sum.inl) : EuclideanSpace ℂ N)‖ ^ 2 +
      ‖(WithLp.toLp 2 (z ∘ Sum.inr) : EuclideanSpace ℂ M)‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Function.comp_def]

omit [DecidableEq N] [DecidableEq M] in
private lemma norm_sum_elim (x : EuclideanSpace ℂ N) (y : EuclideanSpace ℂ M) :
    ‖(WithLp.toLp 2 (Sum.elim x y) : EuclideanSpace ℂ (N ⊕ M))‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

private lemma norm_block_diagonal (X : Matrix N N ℂ) (Y : Matrix M M ℂ) :
    ‖fromBlocks X 0 0 Y‖ = max ‖X‖ ‖Y‖ := by
  let B := fromBlocks X 0 0 Y
  let L := toEuclideanCLM (𝕜 := ℂ) (n := N ⊕ M)
  let LX := toEuclideanCLM (𝕜 := ℂ) (n := N)
  let LY := toEuclideanCLM (𝕜 := ℂ) (n := M)
  have happ (z : EuclideanSpace ℂ (N ⊕ M)) :
      L B z = WithLp.toLp 2
        (Sum.elim (LX X (WithLp.toLp 2 (z ∘ Sum.inl)))
          (LY Y (WithLp.toLp 2 (z ∘ Sum.inr)))) := by
    apply WithLp.ofLp_injective
    simp [B, L, LX, LY, fromBlocks_mulVec]
  change ‖B‖ = max ‖X‖ ‖Y‖
  refine le_antisymm ?_ (max_le ?_ ?_)
  · rw [← l2_opNorm_toEuclideanCLM]
    change ‖L B‖ ≤ _
    refine ContinuousLinearMap.opNorm_le_bound _ (le_trans (norm_nonneg X) (le_max_left _ _))
      fun z => ?_
    rw [happ]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_sum_elim, mul_pow, norm_sum_sq, mul_add]
    apply add_le_add
    · simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        ((LX X).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_right (le_max_left ‖X‖ ‖Y‖) (norm_nonneg _)))
    · simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        ((LY Y).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_right (le_max_right ‖X‖ ‖Y‖) (norm_nonneg _)))
  · rw [← l2_opNorm_toEuclideanCLM]
    change ‖LX X‖ ≤ _
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun x => ?_
    have h := (L B).le_opNorm
      (WithLp.toLp 2 (Sum.elim x 0))
    rw [happ] at h
    have hin : ‖(WithLp.toLp 2 (Sum.elim x 0) : EuclideanSpace ℂ (N ⊕ M))‖ = ‖x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(WithLp.toLp 2 (Sum.elim x (0 : EuclideanSpace ℂ M)) :
        EuclideanSpace ℂ (N ⊕ M))‖ ^ 2 = ‖x‖ ^ 2
      rw [norm_sum_elim]
      simp
    have hout : ‖LX X x‖ =
        ‖(WithLp.toLp 2 (Sum.elim
          (LX X (WithLp.toLp 2 ((WithLp.toLp 2 (Sum.elim x 0) :
            EuclideanSpace ℂ (N ⊕ M)) ∘ Sum.inl)))
          (LY Y (WithLp.toLp 2 ((WithLp.toLp 2 (Sum.elim x 0) :
            EuclideanSpace ℂ (N ⊕ M)) ∘ Sum.inr)))) : EuclideanSpace ℂ (N ⊕ M))‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖LX X x‖ ^ 2 = ‖(WithLp.toLp 2 (Sum.elim (LX X x) (LY Y 0)) :
        EuclideanSpace ℂ (N ⊕ M))‖ ^ 2
      rw [map_zero, norm_sum_elim]
      simp
    rwa [← hout, hin] at h
  · rw [← l2_opNorm_toEuclideanCLM]
    change ‖LY Y‖ ≤ _
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun y => ?_
    have h := (L B).le_opNorm
      (WithLp.toLp 2 (Sum.elim 0 y))
    rw [happ] at h
    have hin : ‖(WithLp.toLp 2 (Sum.elim 0 y) : EuclideanSpace ℂ (N ⊕ M))‖ = ‖y‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(WithLp.toLp 2 (Sum.elim (0 : EuclideanSpace ℂ N) y) :
        EuclideanSpace ℂ (N ⊕ M))‖ ^ 2 = ‖y‖ ^ 2
      rw [norm_sum_elim]
      simp
    have hout : ‖LY Y y‖ =
        ‖(WithLp.toLp 2 (Sum.elim
          (LX X (WithLp.toLp 2 ((WithLp.toLp 2 (Sum.elim 0 y) :
            EuclideanSpace ℂ (N ⊕ M)) ∘ Sum.inl)))
          (LY Y (WithLp.toLp 2 ((WithLp.toLp 2 (Sum.elim 0 y) :
            EuclideanSpace ℂ (N ⊕ M)) ∘ Sum.inr)))) : EuclideanSpace ℂ (N ⊕ M))‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖LY Y y‖ ^ 2 = ‖(WithLp.toLp 2 (Sum.elim (LX X 0) (LY Y y)) :
        EuclideanSpace ℂ (N ⊕ M))‖ ^ 2
      rw [map_zero, norm_sum_elim]
      simp
    rwa [← hout, hin] at h

private lemma exp_block_diagonal (X : Matrix N N ℂ) (Y : Matrix M M ℂ) (t : ℝ) :
    NormedSpace.exp (t • fromBlocks X 0 0 Y) =
      fromBlocks (NormedSpace.exp (t • X)) 0 0 (NormedSpace.exp (t • Y)) := by
  let f : (Matrix N N ℂ × Matrix M M ℂ) →+* Matrix (N ⊕ M) (N ⊕ M) ℂ :=
    { toFun := fun p => fromBlocks p.1 0 0 p.2
      map_one' := fromBlocks_one
      map_mul' := fun p q => by simp [fromBlocks_multiply]
      map_zero' := by simp
      map_add' := fun p q => by simp [fromBlocks_add] }
  have hf : Continuous f :=
    continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd
  have hball : (t • X, t • Y) ∈ Metric.eball 0
      (NormedSpace.expSeries ℂ (Matrix N N ℂ × Matrix M M ℂ)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hfst := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ)
    (RingHom.fst (Matrix N N ℂ) (Matrix M M ℂ)) continuous_fst _ hball
  have hsnd := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ)
    (RingHom.snd (Matrix N N ℂ) (Matrix M M ℂ)) continuous_snd _ hball
  have h := (NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) f hf _ hball).symm
  change (NormedSpace.exp (t • X, t • Y)).1 = NormedSpace.exp (t • X) at hfst
  change (NormedSpace.exp (t • X, t • Y)).2 = NormedSpace.exp (t • Y) at hsnd
  change NormedSpace.exp (fromBlocks (t • X) 0 0 (t • Y)) =
    fromBlocks (NormedSpace.exp (t • X, t • Y)).1 0 0
      (NormedSpace.exp (t • X, t • Y)).2 at h
  rw [hfst, hsnd] at h
  simpa only [fromBlocks_smul, smul_zero] using h

private lemma exp_norm_bdd {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (T : ℝ) :
    BddAbove ((fun t : ℝ => ‖NormedSpace.exp (t • A)‖) '' Set.Icc 0 T) := by
  exact (isCompact_Icc.image
    ((differentiable_exp_smul_const ℝ A).continuous.norm)).bddAbove

private lemma norm_lower_block (F : Matrix M N ℂ) :
    ‖fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F (0 : Matrix M M ℂ)‖ =
      ‖F‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := l2_opNorm_conjTranspose_mul_self
    (fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F (0 : Matrix M M ℂ))
  rw [fromBlocks_conjTranspose, fromBlocks_multiply] at h
  simpa [norm_block_diagonal, l2_opNorm_conjTranspose_mul_self, pow_two,
    mul_self_nonneg] using h.symm

private lemma exp_product_deriv {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t s : ℝ) :
    HasDerivAt (fun r : ℝ =>
      NormedSpace.exp ((t - r) • A) * NormedSpace.exp (r • (A + B)))
      (NormedSpace.exp ((t - s) • A) * B * NormedSpace.exp (s • (A + B))) s := by
  have hl := (hasDerivAt_exp_smul_const A (t - s)).scomp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have hr := hasDerivAt_exp_smul_const' (A + B) s
  convert hl.mul hr using 1 <;> first
    | rfl
    | simp only [Function.comp_apply, zero_sub, neg_smul, one_smul]
      noncomm_ring

private lemma lower_exp_identity {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ)
    (hnil : ∀ u : ℝ, B * NormedSpace.exp (u • A) * B = 0) (s : ℝ) :
    B * NormedSpace.exp (s • (A + B)) = B * NormedSpace.exp (s • A) := by
  let h := fun r : ℝ =>
    B * (NormedSpace.exp ((s - r) • A) * NormedSpace.exp (r • (A + B)))
  have hd (r : ℝ) : HasDerivAt h 0 r := by
    convert (exp_product_deriv A B s r).const_mul B using 1
    rw [← mul_assoc, ← mul_assoc, hnil, zero_mul]
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) s 0
  simpa [h] using hc

/-- Lemma 6, Eq. (3.21): the block-diagonal part satisfies
`Csup (fromBlocks F₁ 0 0 F₃) T = max (Cd F₁ T) (Cd F₃ T)`. -/
theorem lemma6_Csup_diagonal (F₁ : Matrix N N ℂ) (F₃ : Matrix M M ℂ) (T : ℝ) :
    Csup (fromBlocks F₁ 0 0 F₃) T = max (Cd F₁ T) (Cd F₃ T) := by
  by_cases hT : 0 ≤ T
  · have hn : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, hT⟩
    have he (t : ℝ) : ‖NormedSpace.exp (t • fromBlocks F₁ 0 0 F₃)‖ =
        max ‖NormedSpace.exp (t • F₁)‖ ‖NormedSpace.exp (t • F₃)‖ := by
      rw [exp_block_diagonal, norm_block_diagonal]
    unfold Csup Cd
    refine le_antisymm (csSup_le (hn.image _) ?_) (max_le ?_ ?_)
    · rintro _ ⟨t, ht, rfl⟩
      dsimp only
      rw [he]
      exact max_le_max (le_csSup (exp_norm_bdd F₁ T) ⟨t, ht, rfl⟩)
        (le_csSup (exp_norm_bdd F₃ T) ⟨t, ht, rfl⟩)
    · refine csSup_le (hn.image _) ?_
      rintro _ ⟨t, ht, rfl⟩
      exact (le_max_left _ _).trans (by simpa only [he] using
        (le_csSup (exp_norm_bdd (fromBlocks F₁ 0 0 F₃) T) ⟨t, ht, rfl⟩))
    · refine csSup_le (hn.image _) ?_
      rintro _ ⟨t, ht, rfl⟩
      exact (le_max_right _ _).trans (by simpa only [he] using
        (le_csSup (exp_norm_bdd (fromBlocks F₁ 0 0 F₃) T) ⟨t, ht, rfl⟩))
  · simp [Csup, Cd, Set.Icc_eq_empty_of_lt (lt_of_not_ge hT), Real.sSup_empty]

/-- Lemma 6, Eqs. (3.19)--(3.21): for `A = [[F₁, 0], [F₂, F₃]]`,
`Csup A T ≤ C_d * (1 + C_d * ‖F₂‖ * T)` where `C_d = max (Cd F₁ T) (Cd F₃ T)`. -/
theorem lemma6_Csup_bound
    (F₁ : Matrix N N ℂ) (F₂ : Matrix M N ℂ) (F₃ : Matrix M M ℂ) (T : ℝ) :
    Csup (blockA F₁ 0 F₂ F₃) T ≤
      max (Cd F₁ T) (Cd F₃ T) * (1 + max (Cd F₁ T) (Cd F₃ T) * ‖F₂‖ * T) := by
  by_cases hT : 0 ≤ T
  · let A := fromBlocks F₁ (0 : Matrix N M ℂ) (0 : Matrix M N ℂ) F₃
    let B := fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ (0 : Matrix M M ℂ)
    let C := max (Cd F₁ T) (Cd F₃ T)
    have hC : C = Csup A T := (lemma6_Csup_diagonal F₁ F₃ T).symm
    have hexp (u : ℝ) (hu : u ∈ Set.Icc 0 T) :
        ‖NormedSpace.exp (u • A)‖ ≤ C := by
      rw [hC]
      exact le_csSup (exp_norm_bdd A T) ⟨u, hu, rfl⟩
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hexp 0 ⟨le_rfl, hT⟩)
    have hB : ‖B‖ = ‖F₂‖ := norm_lower_block F₂
    have hnil (u : ℝ) : B * NormedSpace.exp (u • A) * B = 0 := by
      dsimp [A, B]
      rw [exp_block_diagonal, fromBlocks_multiply, fromBlocks_multiply]
      simp
    rw [lemma6_block_split]
    change Csup (A + B) T ≤ C * (1 + C * ‖F₂‖ * T)
    refine csSup_le (Set.Nonempty.image _ ⟨0, le_rfl, hT⟩) ?_
    rintro _ ⟨t, ht, rfl⟩
    dsimp only
    let g := fun s : ℝ =>
      NormedSpace.exp ((t - s) • A) * NormedSpace.exp (s • (A + B))
    let g' := fun s : ℝ =>
      NormedSpace.exp ((t - s) • A) * B * NormedSpace.exp (s • A)
    have hd (s : ℝ) : HasDerivAt g (g' s) s := by
      have he := lower_exp_identity A B hnil s
      simpa only [g, g', mul_assoc, he] using exp_product_deriv A B t s
    have hb (s : ℝ) (hs : s ∈ Set.Icc 0 t) : ‖g' s‖ ≤ C ^ 2 * ‖F₂‖ := by
      have h₁ := hexp (t - s) ⟨sub_nonneg.mpr hs.2, by linarith [ht.2, hs.1]⟩
      have h₂ := hexp s ⟨hs.1, hs.2.trans ht.2⟩
      calc
        ‖g' s‖ ≤ ‖NormedSpace.exp ((t - s) • A)‖ * ‖B‖ *
            ‖NormedSpace.exp (s • A)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))
        _ ≤ C * ‖F₂‖ * C := by
          rw [hB]
          exact mul_le_mul (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)) h₂
            (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
        _ = C ^ 2 * ‖F₂‖ := by ring
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s (_ : s ∈ Set.Icc 0 t) => (hd s).hasDerivWithinAt) hb (convex_Icc 0 t)
      (show 0 ∈ Set.Icc 0 t from ⟨le_rfl, ht.1⟩)
      (show t ∈ Set.Icc 0 t from ⟨ht.1, le_rfl⟩)
    have hdiff : ‖NormedSpace.exp (t • (A + B)) - NormedSpace.exp (t • A)‖ ≤
        C ^ 2 * ‖F₂‖ * T := by
      have hm' : ‖NormedSpace.exp (t • (A + B)) - NormedSpace.exp (t • A)‖ ≤
          C ^ 2 * ‖F₂‖ * t := by
        simpa [g, Real.norm_eq_abs, abs_of_nonneg ht.1] using hm
      exact hm'.trans
        (mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ C ^ 2 * ‖F₂‖))
    calc
      ‖NormedSpace.exp (t • (A + B))‖ ≤
          ‖NormedSpace.exp (t • (A + B)) - NormedSpace.exp (t • A)‖ +
            ‖NormedSpace.exp (t • A)‖ := by
              have := norm_sub_norm_le (NormedSpace.exp (t • (A + B)))
                (NormedSpace.exp (t • A))
              linarith
      _ ≤ C ^ 2 * ‖F₂‖ * T + C := add_le_add hdiff (hexp t ht)
      _ = C * (1 + C * ‖F₂‖ * T) := by ring
  · simp [Csup, Cd, Set.Icc_eq_empty_of_lt (lt_of_not_ge hT), Real.sSup_empty]

end Qatlib.Papers.QuadHamilton24.MainResults
