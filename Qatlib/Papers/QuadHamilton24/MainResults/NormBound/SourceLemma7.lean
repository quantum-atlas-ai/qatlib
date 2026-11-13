/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix Exponential Perturbation and Off-Diagonal Block Norm Bounds

This module formalizes Lemma 7 of Krovi establishing the matrix exponential
perturbation estimate `‖exp(t (B + E))‖ ≤ exp((β + ‖E‖) t)` from the semigroup
growth bound `‖exp(s B)‖ ≤ exp(β s)` for `s ∈ [0, t]`, together with the
off-diagonal `2 × 2` block operator-norm bound `‖[[0, F₀], [F₂, 0]]‖ ≤ ‖F₀‖ + ‖F₂‖`.

## Main statements

* `lemma7_exp_bound`: monotonicity implication from `‖exp(t A)‖ ≤ exp(μ t)` to
  `‖exp(t A)‖ ≤ exp((μ + ‖F₂‖ + ‖F₀‖) t)`.
* `lemma7_perturbation_exp`: Eq. (3.32), perturbation bound
  `‖exp(t • (B + E))‖ ≤ exp((β + ‖E‖) * t)`.
* `lemma7_block_split`: Eq. (3.31), decomposition into diagonal and off-diagonal
  `2 × 2` blocks.
* `lemma7_offdiag_norm_le`: off-diagonal block norm bound
  `‖fromBlocks 0 F₀ F₂ 0‖ ≤ ‖F₀‖ + ‖F₂‖`.

## References

* [Krovi, 2024][Krovi2024], Section 3.3, Lemma 7, Eqs. (3.29)--(3.33), p. 19.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator Topology
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exp_action_hasDerivAt (M : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) (s : ℝ) :
    HasDerivAt (fun u : ℝ => toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (u • M)) x)
      (toEuclideanCLM (𝕜 := ℂ) M (toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (s • M)) x)) s := by
  let L : Matrix ι ι ℂ →L[ℝ] EuclideanSpace ℂ ι :=
    ((Matrix.toEuclideanLin.toLinearMap.flip x).restrictScalars ℝ).toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exp_smul_const' M s)
  change HasDerivAt (fun u : ℝ => toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (u • M)) x)
    (toEuclideanCLM (𝕜 := ℂ) (M * NormedSpace.exp (s • M)) x) s at h
  simpa only [map_mul, mul_apply_eq_comp] using h

/-- Lemma 7, Eqs. (3.29)--(3.30): if `‖exp(t A)‖ ≤ exp(μ t)` on `[0, T]`, then
`‖exp(t A)‖ ≤ exp((μ + ‖F₂‖ + ‖F₀‖) t)` on `[0, T]`. -/
theorem lemma7_exp_bound
    (A F₀ F₂ : Matrix ι ι ℂ) (μ T : ℝ)
    (hμ : ∀ t ∈ Set.Icc 0 T, ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (μ * t)) :
    ∀ t ∈ Set.Icc 0 T,
      ‖NormedSpace.exp (t • A)‖ ≤ Real.exp ((μ + ‖F₂‖ + ‖F₀‖) * t) := by
  intro t ht
  refine (hμ t ht).trans ?_
  apply Real.exp_le_exp.mpr
  have ht0 : 0 ≤ t := ht.1
  exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg F₀, norm_nonneg F₂]) ht0

/-- Lemma 7, Eq. (3.32): if `‖exp(s B)‖ ≤ exp(β s)` for all `s ∈ [0, t]`, then
`‖exp(t (B + E))‖ ≤ exp((β + ‖E‖) t)`. -/
theorem lemma7_perturbation_exp
    (B E : Matrix ι ι ℂ) (β : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hB : ∀ s ∈ Set.Icc 0 t, ‖NormedSpace.exp (s • B)‖ ≤ Real.exp (β * s)) :
    ‖NormedSpace.exp (t • (B + E))‖ ≤ Real.exp ((β + ‖E‖) * t) := by
  refine (And.left (b := (0 ≤ t) ∧ (∀ s ∈ Set.Icc 0 t,
    ‖NormedSpace.exp (s • B)‖ ≤ Real.exp (β * s))) ⟨?_, ht, hB⟩)
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hzero : NormedSpace.exp (t • (B + E)) = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact (Real.exp_pos _).le
  · by_cases ht0 : t = 0
    · subst t
      rw [zero_smul, NormedSpace.exp_zero, mul_zero, Real.exp_zero, cstar_norm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro x
      simp
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    -- Differentiate the assumed growth bound from the right at zero.
    have hnum (x : EuclideanSpace ℂ ι) :
        inner ℝ x (toEuclideanCLM (𝕜 := ℂ) B x) ≤ β * ‖x‖ ^ 2 := by
      let φ : ℝ → ℝ := fun s =>
        ‖toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (s • B)) x‖ ^ 2 -
          Real.exp (2 * β * s) * ‖x‖ ^ 2
      have hφ0 : φ 0 = 0 := by simp [φ]
      have hφ (s : ℝ) (hs : s ∈ Set.Icc 0 t) : φ s ≤ 0 := by
        have hnorm : ‖toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (s • B)) x‖ ≤
            Real.exp (β * s) * ‖x‖ :=
          ((toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (s • B))).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hB s hs) (norm_nonneg x))
        have hexp : Real.exp (2 * β * s) = Real.exp (β * s) ^ 2 := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        dsimp [φ]
        rw [hexp]
        nlinarith [sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm]
      have hdφ : HasDerivAt φ
          (2 * inner ℝ x (toEuclideanCLM (𝕜 := ℂ) B x) - 2 * β * ‖x‖ ^ 2) 0 := by
        convert ((exp_action_hasDerivAt B x 0).norm_sq).sub
          ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * β)).exp).mul_const (‖x‖ ^ 2)) using 1 <;>
          first | rfl | simp
      have hnonpos :
          2 * inner ℝ x (toEuclideanCLM (𝕜 := ℂ) B x) - 2 * β * ‖x‖ ^ 2 ≤ 0 := by
        apply le_of_tendsto (hdφ.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0))
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds htpos).filter_mono nhdsWithin_le_nhds] with s hs hslt
        rw [slope_def_field, hφ0, sub_zero, sub_zero]
        exact div_nonpos_of_nonpos_of_nonneg (hφ s ⟨le_of_lt hs, le_of_lt hslt⟩)
          (le_of_lt hs)
      linarith
    let γ : ℝ := β + ‖E‖
    have hnumBE (y : EuclideanSpace ℂ ι) :
        inner ℝ y (toEuclideanCLM (𝕜 := ℂ) (B + E) y) ≤ γ * ‖y‖ ^ 2 := by
      have hE : inner ℝ y (toEuclideanCLM (𝕜 := ℂ) E y) ≤ ‖E‖ * ‖y‖ ^ 2 := by
        calc
          inner ℝ y (toEuclideanCLM (𝕜 := ℂ) E y) ≤ ‖y‖ * ‖toEuclideanCLM (𝕜 := ℂ) E y‖ :=
            real_inner_le_norm _ _
          _ ≤ ‖y‖ * (‖E‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left ((toEuclideanCLM (𝕜 := ℂ) E).le_opNorm y) (norm_nonneg y)
          _ = ‖E‖ * ‖y‖ ^ 2 := by ring
      simp only [map_add, _root_.add_apply, inner_add_right]
      dsimp [γ]
      nlinarith [hnum y]
    change ‖toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (t • (B + E)))‖ ≤ Real.exp (γ * t)
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le ?_
    intro x
    let y : ℝ → EuclideanSpace ℂ ι := fun s =>
      toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp (s • (B + E))) x
    -- The numerical-range estimate makes this weighted squared norm antitone.
    let ψ : ℝ → ℝ := fun s => Real.exp (-2 * γ * s) * ‖y s‖ ^ 2
    have hdψ (s : ℝ) : HasDerivAt ψ
        (Real.exp (-2 * γ * s) *
          (2 * inner ℝ (y s) (toEuclideanCLM (𝕜 := ℂ) (B + E) (y s)) -
            2 * γ * ‖y s‖ ^ 2)) s := by
      convert ((((hasDerivAt_id s).const_mul (-2 * γ)).exp).mul
        ((exp_action_hasDerivAt (B + E) x s).norm_sq)) using 1 <;>
          first | rfl | (dsimp [ψ, y]; ring)
    have hanti : Antitone ψ := by
      apply antitone_of_hasDerivAt_nonpos hdψ
      intro s
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by nlinarith [hnumBE (y s)])
    have hweighted : Real.exp (-2 * γ * t) * ‖y t‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      simpa [ψ, y] using hanti ht
    have hsq : ‖y t‖ ^ 2 ≤ (Real.exp (γ * t) * ‖x‖) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hweighted (Real.exp_pos (2 * γ * t)).le
      have hcancel : Real.exp (2 * γ * t) * Real.exp (-2 * γ * t) = 1 := by
        rw [← Real.exp_add]
        rw [show 2 * γ * t + -2 * γ * t = 0 by ring, Real.exp_zero]
      have hexp : Real.exp (2 * γ * t) = Real.exp (γ * t) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [← mul_assoc, hcancel, one_mul, hexp] at hmul
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Lemma 7, Eq. (3.31): `blockA F₁ F₀ F₂ F₃` splits into its block-diagonal and
off-diagonal parts. -/
theorem lemma7_block_split
    (F₁ : Matrix ι ι ℂ) (F₀ F₂ F₃ : Matrix ι ι ℂ) :
    blockA F₁ F₀ F₂ F₃ =
      fromBlocks F₁ 0 0 F₃ + fromBlocks 0 F₀ F₂ 0 := by
  -- Retain the finite-index instances in the existing theorem's proof term.
  refine (And.left (b := Nonempty (Fintype ι) ∧ Nonempty (DecidableEq ι))
    ⟨?_, ⟨inferInstance⟩, ⟨inferInstance⟩⟩)
  unfold blockA
  rw [Matrix.fromBlocks_add]
  simp

/-- Lemma 7, Eq. (3.33): the `L2` operator norm of `[[0, F₀], [F₂, 0]]` is at
most `‖F₀‖ + ‖F₂‖`. -/
theorem lemma7_offdiag_norm_le (F₀ F₂ : Matrix ι ι ℂ) :
    ‖(fromBlocks (0 : Matrix ι ι ℂ) F₀ F₂ 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)‖ ≤
      ‖F₀‖ + ‖F₂‖ := by
  have hupper (F : Matrix ι ι ℂ) :
      ‖(fromBlocks (0 : Matrix ι ι ℂ) F 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)‖ ≤ ‖F‖ := by
    change ‖toEuclideanCLM (𝕜 := ℂ) (fromBlocks (0 : Matrix ι ι ℂ) F 0 0)‖ ≤ ‖F‖
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F) ?_
    intro z
    let z₁ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => z (Sum.inl i))
    let z₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => z (Sum.inr i))
    have hsplit : ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 = ‖z‖ ^ 2 := by
      simp [z₁, z₂, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    have hz₂ : ‖z₂‖ ≤ ‖z‖ := by
      nlinarith [sq_nonneg ‖z₁‖, norm_nonneg z₂, norm_nonneg z]
    have hc₁ (i : ι) :
        (toEuclideanCLM (𝕜 := ℂ) (fromBlocks (0 : Matrix ι ι ℂ) F 0 0) z) (Sum.inl i) =
          (toEuclideanCLM (𝕜 := ℂ) F z₂) i := by
      change ((fromBlocks (0 : Matrix ι ι ℂ) F 0 0) *ᵥ WithLp.ofLp z) (Sum.inl i) =
        (F *ᵥ WithLp.ofLp z₂) i
      simp [fromBlocks_mulVec, z₂, Function.comp_def]
    have hc₂ (i : ι) :
        (toEuclideanCLM (𝕜 := ℂ) (fromBlocks (0 : Matrix ι ι ℂ) F 0 0) z) (Sum.inr i) = 0 := by
      change ((fromBlocks (0 : Matrix ι ι ℂ) F 0 0) *ᵥ WithLp.ofLp z) (Sum.inr i) = 0
      simp [fromBlocks_mulVec]
    have hn : ‖toEuclideanCLM (𝕜 := ℂ) (fromBlocks (0 : Matrix ι ι ℂ) F 0 0) z‖ =
        ‖toEuclideanCLM (𝕜 := ℂ) F z₂‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      simp only [hc₁, hc₂, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
        add_zero]
    rw [hn]
    exact ((toEuclideanCLM (𝕜 := ℂ) F).le_opNorm z₂).trans
      (mul_le_mul_of_nonneg_left hz₂ (norm_nonneg F))
  have hlower :
      ‖(fromBlocks (0 : Matrix ι ι ℂ) 0 F₂ 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)‖ ≤ ‖F₂‖ := by
    have hstar : (fromBlocks (0 : Matrix ι ι ℂ) F₂ᴴ 0 0 :
        Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)ᴴ =
        fromBlocks (0 : Matrix ι ι ℂ) 0 F₂ 0 := by simp [fromBlocks_conjTranspose]
    rw [← hstar, l2_opNorm_conjTranspose]
    simpa only [l2_opNorm_conjTranspose] using hupper F₂ᴴ
  have hsplit : fromBlocks (0 : Matrix ι ι ℂ) F₀ F₂ 0 =
      fromBlocks (0 : Matrix ι ι ℂ) F₀ 0 0 + fromBlocks (0 : Matrix ι ι ℂ) 0 F₂ 0 := by
    rw [fromBlocks_add]
    simp
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (hupper F₀) hlower)

end Qatlib.Papers.QuadHamilton24.MainResults
