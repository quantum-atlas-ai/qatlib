/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySourceOptimizers
public import Qatlib.Concepts.SignedWeights.Representations.Composition.Corollary14

/-!
# Lower bound for nonnegative adversary composition

The lower inequality of [HoyerLeeSpalek2007], Corollary 14, follows by
composing nonnegative optimal witnesses. Real matrices and their complex
extensions have the same Euclidean operator norm, so the spectral and
filter identities for the paper's composition apply to the real witness.
The bounds use nonconstant outer and inner Boolean functions and observable
inner outputs on finite input domains.

See the [fixed preprint](https://arxiv.org/abs/quant-ph/0611054v2), §6.
-/

@[expose] public section

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComposition

namespace Qatlib.Papers.NegWeights06.MainResults

set_option maxHeartbeats 400000 in
/-- Extending real coefficients to complex coefficients preserves the Euclidean operator norm. -/
private theorem norm_complexification {X : Type} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℝ) : ‖M.map Complex.ofReal‖ = ‖M‖ := by
  let C := M.map Complex.ofReal
  let T := Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) C
  let S := Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) M
  let realPart (w : EuclideanSpace ℂ X) : EuclideanSpace ℝ X := WithLp.toLp 2 (fun i => (w i).re)
  let imagPart (w : EuclideanSpace ℂ X) : EuclideanSpace ℝ X := WithLp.toLp 2 (fun i => (w i).im)
  have hnorm (w : EuclideanSpace ℂ X) : ‖w‖ ^ 2 = ‖realPart w‖ ^ 2 + ‖imagPart w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖w i‖ ^ 2 = (w i).re ^ 2 + (w i).im ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, pow_two, pow_two]
  have hre (w : EuclideanSpace ℂ X) :
      realPart (T w) = S (realPart w) := by
    ext i
    change ((C *ᵥ w.ofLp) i).re = (M *ᵥ (realPart w).ofLp) i
    simp [C, realPart, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]
  have him (w : EuclideanSpace ℂ X) :
      imagPart (T w) = S (imagPart w) := by
    ext i
    change ((C *ᵥ w.ofLp) i).im = (M *ᵥ (imagPart w).ofLp) i
    simp [C, imagPart, Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]
  apply le_antisymm
  · change ‖T‖ ≤ ‖M‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow,
      hnorm (T w), hre, him, hnorm w, mul_add, ← mul_pow, ← mul_pow]
    exact add_le_add
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (M.l2_opNorm_mulVec (realPart w)))
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (M.l2_opNorm_mulVec (imagPart w)))
  · let castVec (w : EuclideanSpace ℝ X) : EuclideanSpace ℂ X :=
      WithLp.toLp 2 (fun i => (w i : ℂ))
    have hcast (w : EuclideanSpace ℝ X) : ‖castVec w‖ = ‖w‖ := by
      simp [EuclideanSpace.norm_eq, castVec]
    have hmul (w : EuclideanSpace ℝ X) : T (castVec w) = castVec (S w) := by
      ext i
      change (C *ᵥ (castVec w).ofLp) i = ((M *ᵥ w.ofLp) i : ℂ)
      simp [C, castVec, Matrix.mulVec, dotProduct]
    change ‖S‖ ≤ ‖C‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    have h := C.l2_opNorm_mulVec (castVec w)
    change ‖T (castVec w)‖ ≤ ‖C‖ * ‖castVec w‖ at h
    simpa only [hmul, hcast] using h

/-- Extending matrix coefficients to the complex numbers commutes with disagreement filtering. -/
private theorem filter_map_ofReal {X K : Type} (input : X → K → Bool)
    (M : Matrix X X ℝ) (i : K) :
    (genAdvFilter input M i).map Complex.ofReal = genAdvFilter input (M.map Complex.ofReal) i := by
  ext x y
  by_cases h : input x i = input y i <;> simp [genAdvFilter, h]

/-- The complex extension of a real symmetric matrix is Hermitian. -/
private theorem isHermitian_map_ofReal {X : Type} {M : Matrix X X ℝ} (hM : M.IsSymm) :
    (M.map Complex.ofReal).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  simpa using congrArg Complex.ofReal (hM.apply x y)

/-- Composing nonnegative adversary matrices gives the lower inequality of Corollary 14 on
observable finite Boolean blocks. Each block may have a different finite input domain. -/
theorem nonnegative_adversary_composition_lower
    {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (input : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (f : (Fin k → Bool) → Bool) (a : ℝ)
    (hf : ∃ u v, f u ≠ f v) (hg : ∀ i, ∃ x y, g i x ≠ g i y)
    (hobs : ∀ i, OutputObservable (input i) (g i))
    (hlo : ∀ i, ENNReal.ofReal a ≤ advValue (input i) (g i)) :
    ENNReal.ofReal a * advValue (fun u : Fin k → Bool => u) f ≤
      advValue (composedInput input) (composedFunction g f) := by
  classical
  by_cases ha : 0 < a
  swap
  · simp [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt ha)]
  obtain ⟨A, hA, hAne, _, hAval⟩ := advAlphaR_optimal_exists_of_observable
    id f (fun _ => 1) (fun _ => zero_lt_one) (outputObservable_of_injective id f Function.injective_id) hf
  choose R hR hRne _ hRval using fun i => advAlphaR_optimal_exists_of_observable
    (input i) (g i) (fun _ => 1) (fun _ => zero_lt_one) (hobs i) (hg i)
  let AC := A.map Complex.ofReal
  let RC (i : Fin k) := (R i).map Complex.ofReal
  let e (x : (i : Fin k) → X i) : Fin k → Bool := fun i => g i (x i)
  let F (i : Fin k) := Matrix.diagonal (fun _ : X i => ‖R i‖) + R i
  let C : Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℝ :=
    fun x y => A (e x) (e y) * ∏ i, F i (x i) (y i)
  let P : ℝ := ∏ i, ‖R i‖
  have hP : 0 < P := Finset.prod_pos fun i _ => norm_pos_iff.mpr (hRne i)
  have hnAC : ‖AC‖ = ‖A‖ := norm_complexification A
  have hnRC (i : Fin k) : ‖RC i‖ = ‖R i‖ := norm_complexification (R i)
  have hF (i : Fin k) (x y : X i) : (F i x y : ℂ) =
      (Matrix.diagonal (fun _ : X i => (‖RC i‖ : ℂ)) + RC i) x y := by
    by_cases h : x = y <;> simp [F, RC, h, norm_complexification]
  have hCmap : C.map Complex.ofReal = weightedAdvGamma g f AC RC := by
    ext x y
    change ↑(A (e x) (e y) * ∏ i, F i (x i) (y i)) = weightedAdvGamma g f AC RC x y
    simp only [Complex.ofReal_mul, Complex.ofReal_prod, weightedAdvGamma, AC, Matrix.map_apply, e]
    simp_rw [hF]
  have hAC := isHermitian_map_ofReal hA.1
  have hRC (i : Fin k) := isHermitian_map_ofReal (hR i).1
  have hzAC (x y : Fin k → Bool) (h : f x = f y) : AC x y = 0 := by
    simp [AC, hA.2.2.1 x y h]
  have hzRC (i : Fin k) (x y : X i) (h : g i x = g i y) : RC i x y = 0 := by
    simp [RC, (hR i).2.2.1 x y h]
  have hnC : ‖C‖ = ‖A‖ * P := by
    rw [← norm_complexification C, hCmap, weightedAdvGamma_norm_eq g f AC RC hAC hRC hzRC, hnAC]
    simp only [P, hnRC]
  have hCa (p : Fin k) : a ≤ ‖R p‖ := by
    have hp := hlo p
    change ENNReal.ofReal a ≤ advAlphaR (input p) (g p) (fun _ => 1) at hp
    rw [hRval p] at hp
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp hp
  have hfilter (i : (p : Fin k) × Fin (n p)) :
      ‖genAdvFilter (composedInput input) C i‖ ≤ P / a := by
    obtain ⟨p, q⟩ := i
    rw [← norm_complexification, filter_map_ofReal, hCmap]
    change ‖weightedAdvFilter (weightedAdvInput input) (weightedAdvGamma g f AC RC) ⟨p, q⟩‖ ≤ _
    rw [weightedAdvGamma_filter_norm_eq g f AC RC input hAC hRC hzAC hzRC]
    have haFilter : ‖Qatlib.Concepts.QueryWordCore.QueryMachinery.advFilter id AC p‖ ≤ 1 := by
      change ‖genAdvFilter id (A.map Complex.ofReal) p‖ ≤ 1
      rw [← filter_map_ofReal, norm_complexification]
      exact hA.2.2.2 p
    have hrFilter : ‖Qatlib.Concepts.QueryWordCore.QueryMachinery.advFilter (input p) (RC p) q‖ ≤ 1 := by
      change ‖genAdvFilter (input p) ((R p).map Complex.ofReal) q‖ ≤ 1
      rw [← filter_map_ofReal, norm_complexification]
      exact (hR p).2.2.2 q
    simp only [hnRC]
    let D := ∏ i ∈ Finset.univ.erase p, ‖R i‖
    have hD : 0 ≤ D := Finset.prod_nonneg fun _ _ => norm_nonneg _
    calc
      _ ≤ 1 * 1 * D := mul_le_mul_of_nonneg_right
        (mul_le_mul haFilter hrFilter (norm_nonneg _) zero_le_one) hD
      _ = D := by simp
      _ ≤ P / a := (le_div_iff₀ ha).mpr (calc
        D * a ≤ ‖R p‖ * D := by rw [mul_comm D a]; exact mul_le_mul_of_nonneg_right (hCa p) hD
        _ = P := Finset.mul_prod_erase Finset.univ (fun i => ‖R i‖) (Finset.mem_univ p))
  let t := a / P
  let Γ := t • C
  have ht : 0 < t := div_pos ha hP
  have hnΓ : ‖Γ‖ = a * ‖A‖ := by
    rw [show ‖Γ‖ = ‖t‖ * ‖C‖ from norm_smul _ _, Real.norm_of_nonneg ht.le, hnC]
    dsimp [t]
    field_simp
  have hΓ : CostAdversaryFeasible (composedInput input) (composedFunction g f) (fun _ => 1) Γ := by
    refine ⟨Matrix.IsSymm.ext ?_, ?_, ?_, ?_⟩
    · intro x y
      change t * (A (e y) (e x) * ∏ i, F i (y i) (x i)) = _
      have hFs (i : Fin k) : (F i).IsSymm := (Matrix.isSymm_diagonal _).add (hR i).1
      simp_rw [hA.1.apply (e x) (e y), (hFs _).apply (x _) (y _)]
      rfl
    · intro x y
      change 0 ≤ t * (A (e x) (e y) * ∏ i, F i (x i) (y i))
      refine mul_nonneg ht.le (mul_nonneg (hA.2.1 _ _) (Finset.prod_nonneg fun i _ => ?_))
      exact add_nonneg (by simp [Matrix.diagonal_apply]; split <;> positivity) ((hR i).2.1 _ _)
    · intro x y hxy
      change t * (A (e x) (e y) * ∏ i, F i (x i) (y i)) = 0
      rw [hA.2.2.1 _ _ hxy, zero_mul, mul_zero]
    · intro i
      have hs : genAdvFilter (composedInput input) Γ i = t • genAdvFilter (composedInput input) C i := by
        ext x y
        by_cases h : composedInput input x i = composedInput input y i <;> simp [Γ, genAdvFilter, h]
      rw [hs, norm_smul, Real.norm_of_nonneg ht.le]
      calc
        _ ≤ t * (P / a) := mul_le_mul_of_nonneg_left (hfilter i) ht.le
        _ = 1 := by dsimp [t]; field_simp
  have hΓne : Γ ≠ 0 := norm_pos_iff.mp (by rw [hnΓ]; exact mul_pos ha (norm_pos_iff.mpr hAne))
  change ENNReal.ofReal a * advAlphaR id f (fun _ => 1) ≤ _
  rw [hAval, ← ENNReal.ofReal_mul ha.le, ← hnΓ]
  exact (costAdversary_norm_le_witness _ _ _ (fun _ => zero_lt_one) Γ hΓ).trans
    (le_iSup_of_le ⟨Γ, hΓ.1, hΓ.2.1, hΓ.2.2.1, hΓne⟩ le_rfl)

/-- Corollary 14 holds on nonconstant finite Boolean blocks when their nonnegative adversary
values lie between the uniform real bounds `a` and `b`. -/
theorem nonnegative_adversary_composition_sandwich
    {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (input : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (f : (Fin k → Bool) → Bool) (a b : ℝ)
    (hf : ∃ u v, f u ≠ f v) (hg : ∀ i, ∃ x y, g i x ≠ g i y)
    (hlo : ∀ i, ENNReal.ofReal a ≤ advValue (input i) (g i))
    (hhi : ∀ i, advValue (input i) (g i) ≤ ENNReal.ofReal b) :
    ENNReal.ofReal a * advValue (fun u : Fin k → Bool => u) f ≤
        advValue (composedInput input) (composedFunction g f) ∧
      advValue (composedInput input) (composedFunction g f) ≤
        ENNReal.ofReal b * advValue (fun u : Fin k → Bool => u) f := by
  have hobs (i : Fin k) : OutputObservable (input i) (g i) :=
    (advAlphaR_finite_iff_observable (input i) (g i) (fun _ => 1) (fun _ => zero_lt_one) (hg i)).mp
      ((hhi i).trans_lt ENNReal.ofReal_lt_top)
  exact ⟨nonnegative_adversary_composition_lower input g f a hf hg hobs hlo,
    Qatlib.Concepts.SignedWeights.Representations.Composition.corollary14_upper input g f b hf hg hhi⟩

end Qatlib.Papers.NegWeights06.MainResults
