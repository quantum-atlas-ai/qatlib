/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-!
# Stability of squared transition amplitudes

This module bounds changes in squared transition amplitudes when norm-preserving operators are
approximated in operator norm. It also proves telescoping estimates for products and powers of
contractions, yielding `compiled_amplitude_bound` for equal-length operator lists. See
[WocjanYard2006].

## Main statements

* `SourceLemma72`: If norm-preserving operators U and U' differ by at most ε in operator norm,
  with ε ≤ 1, their squared transition amplitudes between unit vectors differ by at most ε.
* `compiled_amplitude_bound`: For equal-length lists of norm-preserving operators, a total
  pairwise operator-norm error at most ε ≤ 1 bounds the difference of squared transition
  amplitudes between unit vectors by ε.

## References

* [Wocjan and Yard, 2006][WocjanYard2006]
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexInnerProductSpace

namespace Qatlib.Papers.JonesPoly06.MainResults

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Exchanging the arguments of a complex inner product preserves its norm. -/
theorem norm_inner_comm (x y : E) : ‖inner ℂ x y‖ = ‖inner ℂ y x‖ := by
  conv_lhs => rw [← inner_conj_symm x y]
  rw [Complex.norm_conj]

/-- Two orthogonal unit vectors form an orthonormal family indexed by `Fin 2`. -/
theorem orthonormal_pair (v e : E) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (hve : inner ℂ v e = 0) : Orthonormal ℂ ![v, e] := by
  rw [orthonormal_iff_ite]
  intro i j
  have hve' : inner ℂ e v = 0 := by rw [← inner_conj_symm e v, hve, map_zero]
  fin_cases i <;> fin_cases j <;> simp [hv, he, hve, hve']

/-- For unit vectors u and v and a vector φ of norm at most one, the difference ‖⟪φ, u⟫‖² − ‖⟪φ,
v⟫‖² is at most ‖u − v‖. -/
theorem inner_sq_diff_le (φ u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hφ : ‖φ‖ ≤ 1) :
    ‖inner ℂ φ u‖ ^ 2 - ‖inner ℂ φ v‖ ^ 2 ≤ ‖u - v‖ := by
  classical
  set c : ℂ := inner ℂ v u with hcdef
  set w : E := u - c • v with hwdef
  have huw : u = c • v + w := by simp [hwdef]
  have hvw : inner ℂ v w = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hcdef]
    rw [inner_self_eq_norm_sq_to_K, hv]
    simp
  have hzero : RCLike.re (inner ℂ (c • v) w) = 0 := by
    rw [inner_smul_left, hvw, mul_zero, map_zero]
  have hconst : (1 : ℝ) = ‖c‖ ^ 2 + ‖w‖ ^ 2 := by
    calc (1 : ℝ) = ‖u‖ ^ 2 := by rw [hu]; norm_num
      _ = ‖c • v + w‖ ^ 2 := by rw [← huw]
      _ = ‖c • v‖ ^ 2 + ‖w‖ ^ 2 := by
            rw [norm_add_sq (𝕜 := ℂ) (c • v) w, hzero]
            ring
      _ = ‖c‖ ^ 2 + ‖w‖ ^ 2 := by rw [norm_smul, hv, mul_one]
  by_cases hw0 : ‖w‖ = 0
  · have hwzero : w = 0 := norm_eq_zero.mp hw0
    have hc1 : ‖c‖ = 1 := by
      have h1 : (1 : ℝ) = ‖c‖ ^ 2 := by rw [hconst, hw0]; ring
      nlinarith [norm_nonneg c]
    have hu_eq : u = c • v := by rw [huw, hwzero, add_zero]
    have hval : inner ℂ φ u = c * inner ℂ φ v := by rw [hu_eq, inner_smul_right]
    have hzero2 : ‖inner ℂ φ u‖ ^ 2 - ‖inner ℂ φ v‖ ^ 2 = 0 := by
      rw [hval, norm_mul, hc1, one_mul, sub_self]
    rw [hzero2]
    exact norm_nonneg _
  · have hspos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)
    have hcne : ((‖w‖ : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hspos
    set e : E := ((‖w‖ : ℂ))⁻¹ • w with hedef
    have he : ‖e‖ = 1 := by
      rw [hedef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hspos]
      field_simp
    have hve : inner ℂ v e = 0 := by rw [hedef, inner_smul_right, hvw, mul_zero]
    have hB : ‖inner ℂ v φ‖ ^ 2 + ‖inner ℂ e φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
      have h := Orthonormal.sum_inner_products_le (𝕜 := ℂ) (s := Finset.univ) φ
        (orthonormal_pair v e hv he hve)
      simpa [Fin.sum_univ_two] using h
    have hcombo : ‖inner ℂ φ v‖ ^ 2 + ‖inner ℂ φ e‖ ^ 2 ≤ 1 := by
      have h2 := hB
      rw [norm_inner_comm v φ, norm_inner_comm e φ] at h2
      have hφ1 : ‖φ‖ ^ 2 ≤ 1 := by nlinarith [hφ, norm_nonneg φ]
      linarith
    have hwe : inner ℂ φ w = (‖w‖ : ℂ) * inner ℂ φ e := by
      rw [hedef, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
    have hsplit : inner ℂ φ u = c * inner ℂ φ v + (‖w‖ : ℂ) * inner ℂ φ e := by
      rw [huw, inner_add_right, inner_smul_right, hwe]
    have h1 : ‖inner ℂ φ u‖ ≤ ‖c‖ * ‖inner ℂ φ v‖ + ‖w‖ * ‖inner ℂ φ e‖ := by
      rw [hsplit]
      calc ‖c * inner ℂ φ v + (‖w‖ : ℂ) * inner ℂ φ e‖
          ≤ ‖c * inner ℂ φ v‖ + ‖(‖w‖ : ℂ) * inner ℂ φ e‖ := norm_add_le _ _
        _ = ‖c‖ * ‖inner ℂ φ v‖ + ‖w‖ * ‖inner ℂ φ e‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hspos]
    have hsq : ‖inner ℂ φ u‖ ^ 2
        ≤ (‖c‖ * ‖inner ℂ φ v‖ + ‖w‖ * ‖inner ℂ φ e‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hQ : 0 ≤ (1 + ‖w‖) * ‖inner ℂ φ v‖ ^ 2
        - 2 * ‖c‖ * ‖inner ℂ φ v‖ * ‖inner ℂ φ e‖
        + (1 - ‖w‖) * ‖inner ℂ φ e‖ ^ 2 := by
      have hsq0 : 0 ≤ ((1 + ‖w‖) * ‖inner ℂ φ v‖
          - ‖c‖ * ‖inner ℂ φ e‖) ^ 2 := sq_nonneg _
      have hc1 : ‖c‖ ^ 2 + ‖w‖ ^ 2 = 1 := by linarith [hconst]
      nlinarith [hsq0, hc1, hspos]
    have key : (‖c‖ * ‖inner ℂ φ v‖ + ‖w‖ * ‖inner ℂ φ e‖) ^ 2
        - ‖inner ℂ φ v‖ ^ 2 ≤ ‖w‖ := by
      have hc1 : ‖c‖ ^ 2 + ‖w‖ ^ 2 = 1 := by linarith [hconst]
      have hmid : (‖c‖ * ‖inner ℂ φ v‖ + ‖w‖ * ‖inner ℂ φ e‖) ^ 2
          - ‖inner ℂ φ v‖ ^ 2
          ≤ ‖w‖ * (‖inner ℂ φ v‖ ^ 2 + ‖inner ℂ φ e‖ ^ 2) := by
        nlinarith [hQ, hc1, hspos]
      nlinarith [hmid, hcombo, hspos]
    have hsle : ‖w‖ ≤ ‖u - v‖ := by
      have hcsq : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have h1 : ‖u - v‖ ^ 2 = 2 - 2 * c.re := by
        rw [norm_sub_sq (𝕜 := ℂ) u v, hu, hv, hcdef, inner_re_symm]
        norm_num
        ring
      have h3 : ‖w‖ ^ 2 = 1 - ‖c‖ ^ 2 := by linarith [hconst]
      have hsqle : ‖w‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
        rw [h3, h1]
        nlinarith [sq_nonneg (1 - c.re), sq_nonneg c.im, hcsq]
      have h := sq_le_sq.mp hsqle
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h
    calc ‖inner ℂ φ u‖ ^ 2 - ‖inner ℂ φ v‖ ^ 2
        ≤ (‖c‖ * ‖inner ℂ φ v‖ + ‖w‖ * ‖inner ℂ φ e‖) ^ 2
          - ‖inner ℂ φ v‖ ^ 2 := by linarith
      _ ≤ ‖w‖ := key
      _ ≤ ‖u - v‖ := hsle

/-- If norm-preserving operators U and U' differ by at most ε in operator norm, with ε ≤ 1,
their squared transition amplitudes between unit vectors differ by at most ε; see
[WocjanYard2006]. -/
theorem SourceLemma72 (U U' : E →L[ℂ] E)
    (hU : ∀ x, ‖U x‖ = ‖x‖) (hU' : ∀ x, ‖U' x‖ = ‖x‖)
    (φ ψ : E) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (ε : ℝ) (hop : ‖U - U'‖ ≤ ε) (_hε : ε ≤ 1) :
    |‖inner ℂ φ (U ψ)‖ ^ 2 - ‖inner ℂ φ (U' ψ)‖ ^ 2| ≤ ε := by
  have hu : ‖U ψ‖ = 1 := by rw [hU, hψ]
  have hv : ‖U' ψ‖ = 1 := by rw [hU', hψ]
  have hφ' : ‖φ‖ ≤ 1 := le_of_eq hφ
  have hnorm : ‖U ψ - U' ψ‖ ≤ ε := by
    calc ‖U ψ - U' ψ‖ = ‖(U - U') ψ‖ := by rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖U - U'‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖U - U'‖ := by rw [hψ, mul_one]
      _ ≤ ε := hop
  have h1 := inner_sq_diff_le (φ := φ) (u := U ψ) (v := U' ψ) hu hv hφ'
  have h2 := inner_sq_diff_le (φ := φ) (u := U' ψ) (v := U ψ) hv hu hφ'
  rw [norm_sub_rev] at h2
  rw [abs_le]
  constructor <;> linarith

end InnerProduct

section ProdNorm

variable {A : Type*} [SeminormedRing A] [NormOneClass A]

/-- The product of a list of elements of norm at most one also has norm at most one. -/
theorem list_prod_le_one : ∀ (l : List A), (∀ a ∈ l, ‖a‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simp
  | a :: l, h => by
      rw [List.prod_cons]
      calc ‖a * l.prod‖ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le _ _
        _ ≤ 1 * 1 :=
            mul_le_mul (h a (by simp))
              (list_prod_le_one l (fun b hb => h b (by simp [hb])))
              (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num

/-- For equal-length lists of contractions, the norm of the difference of their products is at
most the sum of the pairwise norm differences; see [WocjanYard2006]. -/
theorem list_prod_sub_prod_le : ∀ (l₁ l₂ : List A), l₁.length = l₂.length →
    (∀ a ∈ l₁, ‖a‖ ≤ 1) → (∀ a ∈ l₂, ‖a‖ ≤ 1) →
    ‖l₁.prod - l₂.prod‖ ≤ (l₁.zipWith (fun a b => ‖a - b‖) l₂).sum
  | [], [], _, _, _ => by simp
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | a :: l₁, b :: l₂, hlen, h1, h2 => by
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [List.prod_cons, List.prod_cons, List.zipWith_cons_cons, List.sum_cons]
      have ha : ‖a‖ ≤ 1 := h1 a (by simp)
      have hih := list_prod_sub_prod_le l₁ l₂ hlen
        (fun c hc => h1 c (by simp [hc])) (fun c hc => h2 c (by simp [hc]))
      have hb2 : ‖l₂.prod‖ ≤ 1 := list_prod_le_one l₂ (fun c hc => h2 c (by simp [hc]))
      have hid : a * l₁.prod - b * l₂.prod
          = a * (l₁.prod - l₂.prod) + (a - b) * l₂.prod := by noncomm_ring
      rw [hid]
      calc ‖a * (l₁.prod - l₂.prod) + (a - b) * l₂.prod‖
          ≤ ‖a * (l₁.prod - l₂.prod)‖ + ‖(a - b) * l₂.prod‖ := norm_add_le _ _
        _ ≤ ‖a‖ * ‖l₁.prod - l₂.prod‖ + ‖a - b‖ * ‖l₂.prod‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * (l₁.zipWith (fun a b => ‖a - b‖) l₂).sum + ‖a - b‖ * 1 := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul ha hih (norm_nonneg _) (by norm_num)
            · exact mul_le_mul_of_nonneg_left hb2 (norm_nonneg _)
        _ = ‖a - b‖ + (l₁.zipWith (fun a b => ‖a - b‖) l₂).sum := by ring

/-- The difference of the e-th powers of two contractions has norm at most e times the norm of
their difference; see [WocjanYard2006]. -/
theorem pow_sub_pow_le (W V : A) (hW : ‖W‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (e : ℕ) : ‖W ^ e - V ^ e‖ ≤ (e : ℝ) * ‖W - V‖ := by
  induction e with
  | zero => simp
  | succ n ih =>
      have hWn : ‖W ^ n‖ ≤ 1 := by
        refine le_trans (norm_pow_le W n) ?_
        exact pow_le_one₀ (norm_nonneg W) hW
      have hid : W ^ (n + 1) - V ^ (n + 1)
          = W ^ n * (W - V) + (W ^ n - V ^ n) * V := by noncomm_ring
      rw [hid]
      calc ‖W ^ n * (W - V) + (W ^ n - V ^ n) * V‖
          ≤ ‖W ^ n * (W - V)‖ + ‖(W ^ n - V ^ n) * V‖ := norm_add_le _ _
        _ ≤ ‖W ^ n‖ * ‖W - V‖ + ‖W ^ n - V ^ n‖ * ‖V‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * ‖W - V‖ + ((n : ℝ) * ‖W - V‖) * ‖V‖ := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_right hWn (norm_nonneg _)
            · exact mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ ≤ 1 * ‖W - V‖ + ((n : ℝ) * ‖W - V‖) * 1 := by
            have hnn : (0 : ℝ) ≤ (n : ℝ) * ‖W - V‖ := by positivity
            have hle := mul_le_mul_of_nonneg_left hV hnn
            linarith
        _ = ((n + 1 : ℕ) : ℝ) * ‖W - V‖ := by push_cast; ring

end ProdNorm

section Compile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]

omit [Nontrivial E] in

/-- The product of a list of norm-preserving continuous complex linear maps is norm-preserving. -/
theorem list_prod_isometry : ∀ (l : List (E →L[ℂ] E)),
    (∀ W ∈ l, ∀ x, ‖W x‖ = ‖x‖) → ∀ x, ‖l.prod x‖ = ‖x‖
  | [], _ => by intro x; simp
  | W :: l, h => by
      intro x
      rw [List.prod_cons, ContinuousLinearMap.mul_apply, h W (by simp) (l.prod x)]
      exact list_prod_isometry l (fun V hV => h V (by simp [hV])) x

omit [Nontrivial E] in

/-- A norm-preserving continuous complex linear map has operator norm at most one. -/
theorem opNorm_le_one_of_isometry (W : E →L[ℂ] E) (h : ∀ x, ‖W x‖ = ‖x‖) :
    ‖W‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  rw [h x, one_mul]

/-- For equal-length lists of norm-preserving operators, a total pairwise operator-norm error at
most ε ≤ 1 bounds the difference of squared transition amplitudes between unit vectors by ε;
see [WocjanYard2006]. -/
theorem compiled_amplitude_bound (L L' : List (E →L[ℂ] E))
    (hlen : L.length = L'.length)
    (hU : ∀ W ∈ L, ∀ x, ‖W x‖ = ‖x‖)
    (hU' : ∀ W ∈ L', ∀ x, ‖W x‖ = ‖x‖)
    (φ ψ : E) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (ε : ℝ) (hsum : (L.zipWith (fun a b => ‖a - b‖) L').sum ≤ ε) (hε : ε ≤ 1) :
    |‖inner ℂ φ (L.prod ψ)‖ ^ 2 - ‖inner ℂ φ (L'.prod ψ)‖ ^ 2| ≤ ε := by
  have hisoU : ∀ x, ‖L.prod x‖ = ‖x‖ := list_prod_isometry L hU
  have hisoU' : ∀ x, ‖L'.prod x‖ = ‖x‖ := list_prod_isometry L' hU'
  have htro : ‖L.prod - L'.prod‖ ≤ (L.zipWith (fun a b => ‖a - b‖) L').sum :=
    list_prod_sub_prod_le L L' hlen
      (fun W hW => opNorm_le_one_of_isometry W (hU W hW))
      (fun W hW => opNorm_le_one_of_isometry W (hU' W hW))
  exact SourceLemma72 L.prod L'.prod hisoU hisoU' φ ψ hφ hψ ε
    (le_trans htro hsum) hε

end Compile

end Qatlib.Papers.JonesPoly06.MainResults
