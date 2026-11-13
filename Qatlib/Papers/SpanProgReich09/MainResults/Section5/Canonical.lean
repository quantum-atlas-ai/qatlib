/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option backward.isDefEq.respectTransparency false

/-!
# Conversion of Span Programs to Canonical Form Without Increasing Witness Size

This module proves Theorem 5.2: for any nonnegative input-cost vector `s`, every
span program `P` can be converted into a canonical span program `P̂` computing the
same Boolean function `f_{P̂} = f_P` with `wsize_s(P̂, x) ≤ wsize_s(P, x)` on every
input `x`.

## Main statements

* `theorem_5_2_canonical`: canonical span-program conversion preserving computed
  function and non-increasing pointwise weighted witness size.

## References

* [Reichardt, 2009][Reichardt2009SpanPrograms], Definition 5.1 and Theorem 5.2, pp. 25--26.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.SpanProgReich09.MainResults.Section5

open Qatlib.Papers.SpanProgReich09.MainResults
open Qatlib.Foundations.PureStateMath
open WithLp

variable {n : ℕ}

private lemma inner_euclidean {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) :
    inner ℂ v w = Inner v.ofLp w.ofLp := by
  simp [PiLp.inner_apply, inner_apply, RCLike.inner_apply, mul_comm]

/-- A linear image of a finite-dimensional affine space has a point of least norm. -/
private lemma least_image_norm {d k : ℕ}
    (K : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin k))
    (v : EuclideanSpace ℂ (Fin d)) :
    ∃ w, w - v ∈ K ∧ ∀ w', w' - v ∈ K → ‖T w‖ ≤ ‖T w'‖ := by
  let U := K.map T
  obtain ⟨u, hu, hTu⟩ := U.starProjection_apply_mem (T v)
  refine ⟨v - u, by simpa using K.neg_mem hu, ?_⟩
  intro w hw
  have hm : T v - T w ∈ U := by
    exact ⟨v - w, by simpa using K.neg_mem hw, by simp⟩
  have hle := ciInf_le (show BddBelow (Set.range (fun z : U => ‖T v - z‖)) from
    ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩) (⟨T v - T w, hm⟩ : U)
  rw [← Submodule.starProjection_minimal] at hle
  simpa [map_sub, hTu] using hle

private def innerLinear {d : ℕ} (v : Fin d → ℂ) :
    EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ :=
  (innerSL ℂ (toLp 2 v)).toLinearMap

private lemma innerLinear_apply {d : ℕ} (v : Fin d → ℂ)
    (w : EuclideanSpace ℂ (Fin d)) : innerLinear v w = Inner v w.ofLp :=
  inner_euclidean (toLp 2 v) w

private lemma exists_negative (P : SpanProgram n) (x : BitString n)
    (hx : P.fP x = false) :
    ∃ w : Fin P.dim → ℂ, Inner P.target w = 1 ∧
      ∀ i, P.Available x i → P.dualCoord w i = 0 := by
  classical
  let t : EuclideanSpace ℂ (Fin P.dim) := toLp 2 P.target
  let v : Fin P.idx → EuclideanSpace ℂ (Fin P.dim) :=
    fun i => P.piCoeff x i • toLp 2 (P.vec i)
  let U := Submodule.span ℂ (Set.range v)
  have ht : t ∉ U := by
    intro ht
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ht
    have hc : P.combo x w = P.target := by
      funext r
      have h := congrArg (fun z : EuclideanSpace ℂ (Fin P.dim) => z r) hw
      simpa [v, t, SpanProgram.combo, Finset.sum_apply, mul_comm, mul_left_comm,
        mul_assoc] using h
    have he : ∃ w, P.combo x w = P.target := ⟨w, hc⟩
    have : P.fP x = true := by simp [SpanProgram.fP, he]
    simp_all
  let z := t - U.starProjection t
  have hz : z ≠ 0 := by
    intro hz
    have he : t = U.starProjection t := sub_eq_zero.mp hz
    exact ht (he ▸ U.starProjection_apply_mem t)
  have hzo : z ∈ Uᗮ := U.sub_starProjection_mem_orthogonal t
  have htz : inner ℂ t z ≠ 0 := by
    have hzinner : inner ℂ z z = inner ℂ t z := by
      dsimp only [z]
      rw [inner_sub_left, U.inner_right_of_mem_orthogonal
        (U.starProjection_apply_mem t) hzo, sub_zero]
    rw [← hzinner]
    exact inner_self_ne_zero.mpr hz
  let w : EuclideanSpace ℂ (Fin P.dim) := (inner ℂ t z)⁻¹ • z
  refine ⟨w.ofLp, ?_, ?_⟩
  · rw [← inner_euclidean (toLp 2 P.target) w]
    change inner ℂ t w = 1
    simp [w, inner_smul_right, htz]
  · intro i hi
    rw [SpanProgram.dualCoord, ← inner_euclidean (toLp 2 (P.vec i)) w]
    change inner ℂ (toLp 2 (P.vec i)) w = 0
    have hv : toLp 2 (P.vec i) ∈ U := by
      have hv : v i ∈ U := Submodule.subset_span (Set.mem_range_self i)
      simpa [v, SpanProgram.piCoeff, hi] using hv
    simp [w, inner_smul_right, U.inner_right_of_mem_orthogonal hv hzo]

private lemma optimal_negative_of_exists (P : SpanProgram n) (s : Fin n → ℝ)
    (hs : ∀ j, 0 ≤ s j) (x : BitString n) (hx : P.fP x = false)
    (hex : ∃ w, Inner P.target w = 1 ∧
      ∀ i, P.Available x i → P.dualCoord w i = 0) :
    ∃ w, Inner P.target w = 1 ∧
      (∀ i, P.Available x i → P.dualCoord w i = 0) ∧
      ENNReal.ofReal (∑ i, P.costScale s i * ‖P.dualCoord w i‖ ^ 2) =
        P.witnessSize s x := by
  classical
  obtain ⟨w₀, ht, ha⟩ := hex
  -- Valid negative witnesses form the affine space `w₀ + K`.
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin P.dim)) :=
    (innerLinear P.target).ker ⊓
      ⨅ i : {i : Fin P.idx // P.Available x i}, (innerLinear (P.vec i.1)).ker
  have hK (u : EuclideanSpace ℂ (Fin P.dim)) : u ∈ K ↔
      Inner P.target u.ofLp = 0 ∧
        ∀ i, P.Available x i → P.dualCoord u.ofLp i = 0 := by
    simp [K, Submodule.mem_iInf, innerLinear_apply, SpanProgram.dualCoord]
  -- Minimize in the image of the weighted adjoint, allowing zero input costs.
  let T : EuclideanSpace ℂ (Fin P.dim) →ₗ[ℂ] EuclideanSpace ℂ (Fin P.idx) :=
    (WithLp.linearEquiv 2 ℂ (Fin P.idx → ℂ)).symm.toLinearMap.comp
      (LinearMap.pi fun i => (Real.sqrt (P.costScale s i) : ℂ) • innerLinear (P.vec i))
  have hcost (u : EuclideanSpace ℂ (Fin P.dim)) :
      ‖T u‖ ^ 2 = ∑ i, P.costScale s i * ‖P.dualCoord u.ofLp i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hn : 0 ≤ P.costScale s i := by
      unfold SpanProgram.costScale
      split <;> simp_all
    change ‖(Real.sqrt (P.costScale s i) : ℂ) * innerLinear (P.vec i) u‖ ^ 2 = _
    rw [innerLinear_apply]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hn]
    rfl
  obtain ⟨u, hu, hmin⟩ := least_image_norm K T (toLp 2 w₀)
  have hvalid (v : EuclideanSpace ℂ (Fin P.dim)) :
      v - toLp 2 w₀ ∈ K ↔ Inner P.target v.ofLp = 1 ∧
        ∀ i, P.Available x i → P.dualCoord v.ofLp i = 0 := by
    rw [hK]
    have hsub (a : Fin P.dim → ℂ) :
        Inner a (v - toLp 2 w₀).ofLp = Inner a v.ofLp - Inner a w₀ := by
      rw [← innerLinear_apply, map_sub]
      simp only [innerLinear_apply]
    simp only [SpanProgram.dualCoord] at ha ⊢
    simp only [hsub, ht, sub_eq_zero]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> refine ⟨h₁, ?_⟩ <;> intro i hi
    · simpa [ha i hi] using h₂ i hi
    · simpa [ha i hi] using h₂ i hi
  obtain ⟨hut, hua⟩ := (hvalid u).mp hu
  refine ⟨u.ofLp, hut, hua, le_antisymm ?_ ?_⟩
  · simp only [SpanProgram.witnessSize, hx, Bool.false_eq_true, ↓reduceIte]
    apply le_sInf
    rintro _ ⟨w, hwt, hwa, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    rw [← hcost u, ← hcost (toLp 2 w)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin _ ((hvalid _).mpr ⟨hwt, hwa⟩)) 2
  · simp only [SpanProgram.witnessSize, hx, Bool.false_eq_true, ↓reduceIte]
    exact sInf_le ⟨u.ofLp, hut, hua, rfl⟩

private lemma sum_nonfree {M : Type*} [AddCommMonoid M] (P : SpanProgram n)
    (g : Fin P.idx → M) (hg : ∀ i, P.label i = none → g i = 0) :
    (∑ i : {i : Fin P.idx // P.label i ≠ none}, g i.1) = ∑ i, g i := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => P.label i ≠ none), g i :=
      (Finset.sum_subtype _ (by simp) g).symm
    _ = _ := Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hg i hi)

private lemma star_inner_combo (P : SpanProgram n) (x : BitString n)
    (w : Fin P.idx → ℂ) (u : Fin P.dim → ℂ) :
    star (Inner (P.combo x w) u) =
      ∑ i, P.piCoeff x i * w i * star (P.dualCoord u i) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, SpanProgram.combo,
    SpanProgram.dualCoord, star_sum, star_mul', star_star,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- **Theorem 5.2**: for any nonnegative cost vector `s`, every span program `P`
admits a canonical span program `Phat` computing the same Boolean function with
`Phat.witnessSize s x ≤ P.witnessSize s x` for all `x`. -/
theorem theorem_5_2_canonical (P : SpanProgram n) (s : Fin n → ℝ)
    (hs : ∀ j : Fin n, 0 ≤ s j) :
    ∃ (Phat : SpanProgram n)
      (e : {x : BitString n // Phat.fP x = false} ≃ Fin Phat.dim),
      Phat.CanonicalWith e ∧
        (∀ x : BitString n, Phat.fP x = P.fP x) ∧
          ∀ x : BitString n, Phat.witnessSize s x ≤ P.witnessSize s x := by
  classical
  let F₀ := {x : BitString n // P.fP x = false}
  let e₀ : F₀ ≃ Fin (Fintype.card F₀) := Fintype.equivFin F₀
  let I := {i : Fin P.idx // P.label i ≠ none}
  let ι : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  -- Each false input supplies one row, using an optimal negative witness.
  choose w ht ha hopt using fun x : F₀ =>
    optimal_negative_of_exists P s hs x.1 x.2 (exists_negative P x.1 x.2)
  let Q : SpanProgram n := {
    dim := Fintype.card F₀
    idx := Fintype.card I
    target := fun _ => 1
    label := fun i => P.label (ι i).1
    vec := fun i r => star (P.dualCoord (w (e₀.symm r)) (ι i).1) }
  have hav (x : BitString n) (i : Fin Q.idx) :
      Q.Available x i ↔ P.Available x (ι i).1 := Iff.rfl
  have hpi (x : BitString n) (i : Fin Q.idx) :
      Q.piCoeff x i = P.piCoeff x (ι i).1 := rfl
  have hcs (i : Fin Q.idx) : Q.costScale s i = P.costScale s (ι i).1 := rfl
  have hz (x : F₀) (i : Fin Q.idx) (hi : Q.Available x.1 i) :
      Q.vec i (e₀ x) = 0 := by
    change star (P.dualCoord (w (e₀.symm (e₀ x))) (ι i).1) = 0
    rw [e₀.symm_apply_apply, ha x _ ((hav _ _).mp hi), star_zero]
  have hf (x : F₀) : Q.fP x.1 = false := by
    have hn : ¬ ∃ a, Q.combo x.1 a = Q.target := by
      rintro ⟨a, he⟩
      have hzero : Q.combo x.1 a (e₀ x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : Q.Available x.1 i
        · simp [SpanProgram.piCoeff, hi, hz x i hi]
        · simp [SpanProgram.piCoeff, hi]
      have he' := congrFun he (e₀ x)
      change Q.combo x.1 a (e₀ x) = 1 at he'
      exact zero_ne_one (hzero.symm.trans he')
    simp [SpanProgram.fP, hn]
  have hcombo (y : BitString n) (a : Fin P.idx → ℂ)
      (he : P.combo y a = P.target) :
      Q.combo y (fun i => a (ι i).1) = Q.target := by
    funext r
    change (∑ i, Q.piCoeff y i * a (ι i).1 *
      star (P.dualCoord (w (e₀.symm r)) (ι i).1)) = 1
    simp only [hpi]
    rw [ι.sum_comp (fun i : I =>
      P.piCoeff y i.1 * a i.1 * star (P.dualCoord (w (e₀.symm r)) i.1))]
    rw [sum_nonfree P (fun i =>
      P.piCoeff y i * a i * star (P.dualCoord (w (e₀.symm r)) i)) (by
      intro i hi
      have hai : P.Available (e₀.symm r).1 i := Or.inl hi
      rw [ha _ i hai, star_zero, mul_zero])]
    rw [← star_inner_combo, he, ht, star_one]
  have hcost (a : Fin P.idx → ℂ) :
      (∑ i, Q.costScale s i * ‖a (ι i).1‖ ^ 2) =
        ∑ i, P.costScale s i * ‖a i‖ ^ 2 := by
    simp only [hcs]
    rw [ι.sum_comp (fun i : I => P.costScale s i.1 * ‖a i.1‖ ^ 2)]
    apply sum_nonfree P (fun i => P.costScale s i * ‖a i‖ ^ 2)
    intro i hi
    simp [SpanProgram.costScale, hi]
  have heq (x : BitString n) : Q.fP x = P.fP x := by
    cases hx : P.fP x with
    | false => exact hf ⟨x, hx⟩
    | true =>
      have hex : ∃ a, P.combo x a = P.target := by
        simpa only [SpanProgram.fP, ite_eq_left_iff, Bool.false_eq_true,
          imp_false, not_not] using hx
      obtain ⟨a, ha⟩ := hex
      simp [SpanProgram.fP, show ∃ b, Q.combo x b = Q.target from ⟨_, hcombo x a ha⟩]
  let e : {x : BitString n // Q.fP x = false} ≃ Fin Q.dim :=
    (Equiv.subtypeEquivRight fun x => by rw [heq x]).trans e₀
  have he (x : {x : BitString n // Q.fP x = false}) :
      e x = e₀ ⟨x.1, by rw [← heq]; exact x.2⟩ := rfl
  refine ⟨Q, e, ⟨?_, ?_, ?_⟩, heq, ?_⟩
  · intro i
    exact (ι i).2
  · intro r
    change 1 = ∑ x, if e x = r then (1 : ℂ) else 0
    rw [e.sum_comp (fun j => if j = r then (1 : ℂ) else 0)]
    simp
  · intro x i hi
    rw [he x]
    exact hz _ i hi
  · intro x
    cases hx : P.fP x with
    | true =>
      simp only [SpanProgram.witnessSize, heq, hx, ↓reduceIte]
      apply le_sInf
      rintro _ ⟨a, ha, rfl⟩
      rw [← hcost a]
      exact sInf_le ⟨_, hcombo x a ha, rfl⟩
    | false =>
      let x₀ : F₀ := ⟨x, hx⟩
      -- The corresponding basis vector is a negative witness for the new program.
      let b : Fin Q.dim → ℂ := fun r => if r = e₀ x₀ then 1 else 0
      have hbt : Inner Q.target b = 1 := by
        simp [inner_apply, Q, b]
      have hbd (i : Fin Q.idx) : Q.dualCoord b i = P.dualCoord (w x₀) (ι i).1 := by
        simp [SpanProgram.dualCoord, inner_apply, b, Q]
      have hba (i : Fin Q.idx) (hi : Q.Available x i) : Q.dualCoord b i = 0 := by
        rw [hbd]
        exact ha x₀ _ ((hav x i).mp hi)
      have hbc : (∑ i, Q.costScale s i * ‖Q.dualCoord b i‖ ^ 2) =
          ∑ i, P.costScale s i * ‖P.dualCoord (w x₀) i‖ ^ 2 := by
        simp only [hbd]
        exact hcost _
      rw [SpanProgram.witnessSize, heq, hx]
      change sInf (Q.falseCostSet s x) ≤ P.witnessSize s x
      rw [← hopt x₀, ← hbc]
      exact sInf_le ⟨b, hbt, hba, rfl⟩

end Qatlib.Papers.SpanProgReich09.MainResults.Section5
