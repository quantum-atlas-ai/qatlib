/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonDiagonal

/-!
# Quantitative approximation of the ribbon Gauss kernel

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The unit tangent and normal give a model chord with length
`√(h² + a²)`. A uniform second-order Taylor bound controls the true
chord and the cross product. The difference between the Gauss kernel
and its explicit diagonal profile stays bounded in a fixed narrow band,
uniformly as the positive offset shrinks.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge (cross3_apply_zero cross3_apply_one
  cross3_apply_two)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open Set
open scoped Real

/-- A derivative bound controls the increment for either sign of the parameter step. -/
private theorem norm_increment_le {f : ℝ → Fin 3 → ℝ} (hf : Differentiable ℝ f)
    {B : ℝ} (hB : ∀ u, ‖deriv f u‖ ≤ B) (s h : ℝ) :
    ‖f (s + h) - f s‖ ≤ B * |h| := by
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun u _ => hf u) (fun u _ => hB u) (mem_univ s) (mem_univ (s + h))

/-- A second derivative bound controls the linear Taylor remainder by a square. -/
private theorem norm_sub_linear_le {f : ℝ → Fin 3 → ℝ} (hf : Differentiable ℝ f)
    (hd : Differentiable ℝ (deriv f)) {B : ℝ}
    (hB : ∀ u, ‖deriv (deriv f) u‖ ≤ B) (s h : ℝ) :
    ‖f (s + h) - f s - h • deriv f s‖ ≤ B * |h| ^ 2 := by
  let F (u : ℝ) := f (s + u) - u • deriv f s
  have hF (u : ℝ) : HasDerivAt F (deriv f (s + u) - deriv f s) u := by
    have hshift : HasDerivAt (fun x : ℝ => s + x) 1 u := (hasDerivAt_id u).const_add s
    have hd' : HasDerivAt (fun x => f (s + x)) (deriv f (s + u)) u := by
      simpa only [Function.comp_def, one_smul] using (hf (s + u)).hasDerivAt.scomp u hshift
    exact hd'.sub (by
      simpa only [id_eq, one_smul] using (hasDerivAt_id u).smul_const (deriv f s))
  have hbound (u : ℝ) (hu : u ∈ uIcc 0 h) : ‖deriv F u‖ ≤ B * |h| := by
    have hu' : |u| ≤ |h| := by
      rcases le_total 0 h with hh | hh
      · rw [uIcc_of_le hh] at hu
        rw [abs_of_nonneg hu.1, abs_of_nonneg hh]
        exact hu.2
      · rw [uIcc_of_ge hh] at hu
        rw [abs_of_nonpos hu.2, abs_of_nonpos hh]
        linarith [hu.1]
    rw [(hF u).deriv]
    exact (norm_increment_le hd hB s u).trans
      (mul_le_mul_of_nonneg_left hu' ((norm_nonneg _).trans (hB s)))
  have hM := (convex_uIcc (𝕜 := ℝ) 0 h).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (hF u).differentiableAt) hbound left_mem_uIcc right_mem_uIcc
  simpa only [F, sub_zero, zero_smul, add_zero, Real.norm_eq_abs, pow_two, mul_assoc,
    sub_right_comm] using hM

/-- The coordinate norm bounds Euclidean length up to a fixed dimension constant. -/
private theorem euclideanLength_le_three_norm (v : Fin 3 → ℝ) :
    euclideanLength v ≤ 3 * ‖v‖ := by
  have hsq : euclideanLength v ^ 2 = dot3 v v := by
    rw [euclideanLength, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [dot3, pow_two]
  have h := (le_abs_self (dot3 v v)).trans (abs_dot3_le v v)
  rw [← hsq] at h
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith [sq_nonneg ‖v‖]

/-- The Euclidean length is Lipschitz for the Euclidean difference. -/
private theorem abs_euclideanLength_sub_le (v w : Fin 3 → ℝ) :
    |euclideanLength v - euclideanLength w| ≤ euclideanLength (v - w) := by
  unfold euclideanLength
  rw [WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

/-- A cubic numerator error and a quadratic length error yield a bounded
difference of the normalized kernels. -/
private theorem abs_div_cube_sub_le {n m l r C K D : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hD : 0 ≤ D) (hl : r / 2 ≤ l) (hupper : l ≤ 2 * r)
    (hd : |l - r| ≤ D * r ^ 2) (hm : |m| ≤ K * r ^ 2) (hn : |n - m| ≤ C * r ^ 3) :
    |n / l ^ 3 - m / r ^ 3| ≤ 8 * C + 56 * K * D := by
  have hlpos : 0 < l := (half_pos hr).trans_le hl
  have hden : r ^ 3 / 8 ≤ l ^ 3 := by
    rw [show r ^ 3 / 8 = (r / 2) ^ 3 by ring]
    gcongr
  have hfactor : r ^ 2 + r * l + l ^ 2 ≤ 7 * r ^ 2 := by
    calc
      _ ≤ r ^ 2 + r * (2 * r) + (2 * r) ^ 2 := by gcongr
      _ = _ := by ring
  have hdiff : |r ^ 3 - l ^ 3| ≤ 7 * D * r ^ 4 := by
    rw [show r ^ 3 - l ^ 3 = (r - l) * (r ^ 2 + r * l + l ^ 2) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 + r * l + l ^ 2), abs_sub_comm r l]
    calc
      _ ≤ (D * r ^ 2) * (7 * r ^ 2) := by gcongr
      _ = _ := by ring
  have h₁ : |(n - m) / l ^ 3| ≤ 8 * C := by
    rw [abs_div, abs_of_pos (by positivity : 0 < l ^ 3), div_le_iff₀ (by positivity)]
    calc
      _ ≤ C * r ^ 3 := hn
      _ = (8 * C) * (r ^ 3 / 8) := by ring
      _ ≤ _ := by gcongr
  have h₂ : |m * (r ^ 3 - l ^ 3) / (l ^ 3 * r ^ 3)| ≤ 56 * K * D := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < l ^ 3 * r ^ 3),
      div_le_iff₀ (by positivity)]
    calc
      _ ≤ (K * r ^ 2) * (7 * D * r ^ 4) := by gcongr
      _ = (56 * K * D) * (r ^ 3 / 8 * r ^ 3) := by ring
      _ ≤ _ := by gcongr
  rw [show n / l ^ 3 - m / r ^ 3 = (n - m) / l ^ 3 +
    m * (r ^ 3 - l ^ 3) / (l ^ 3 * r ^ 3) by
    field_simp [hlpos.ne', hr.ne']
    ring]
  exact (abs_add_le _ _).trans (add_le_add h₁ h₂)

/-- The cross product of the two tangents has the displayed linear term
and a remainder expressed using only the linear and quadratic tangent errors. -/
private theorem cross3_tangent_expansion (T A V P : Fin 3 → ℝ) (h a : ℝ) :
    cross3 P (T + a • V) =
      (h • cross3 A T + a • cross3 T V) +
      (cross3 (P - T - h • A) T + a • cross3 (P - T) V) := by
  funext i
  fin_cases i <;> simp [cross3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring

/-- The scalar triple product of the linear tangent term and the model chord
consists exactly of the signed twist and curvature terms. -/
private theorem dot3_tangent_profile (T A U V : Fin 3 → ℝ) (h a : ℝ) :
    dot3 (h • cross3 A T + a • cross3 T V) (h • T - a • U) =
      a ^ 2 * dot3 (cross3 T U) V + a * h * dot3 (cross3 T A) U := by
  simp only [dot3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    cross3_apply_zero, cross3_apply_one, cross3_apply_two]
  ring

set_option maxHeartbeats 550000 in
/-- For a unit frame with a common bound on the first three curve derivatives
and the normal derivative, the pointwise remainder in a short band is bounded
uniformly in the positive width. -/
private theorem abs_normalRibbon_kernel_sub_le {γ N : ℝ → Fin 3 → ℝ}
    (hγ : Differentiable ℝ γ) (hT : Differentiable ℝ (deriv γ))
    (hA : Differentiable ℝ (deriv (deriv γ))) (hN : Differentiable ℝ N)
    {B : ℝ} (hB : 1 ≤ B)
    (hbT : ∀ u, ‖deriv γ u‖ ≤ B) (hbA : ∀ u, ‖deriv (deriv γ) u‖ ≤ B)
    (hbJ : ∀ u, ‖deriv (deriv (deriv γ)) u‖ ≤ B) (hbN : ∀ u, ‖deriv N u‖ ≤ B)
    {a s h : ℝ} (ha : 0 < a) (hh : |h| ≤ 1 / (6 * B))
    (htunit : dot3 (deriv γ s) (deriv γ s) = 1) (hnunit : dot3 (N s) (N s) = 1)
    (horth : dot3 (deriv γ s) (N s) = 0) :
    |gaussKernel γ (normalRibbonPoint γ N a) (s + h) s - frozenRibbonKernel γ N a s h| ≤
      (8 * (12 * B ^ 3 + 24 * B ^ 2) + 56 * (12 * B ^ 2) * (3 * B)) / (4 * π) := by
  let T := deriv γ s
  let A := deriv (deriv γ) s
  let U := N s
  let V := deriv N s
  let P := deriv γ (s + h)
  let E := γ (s + h) - γ s - h • T
  let Z := h • T - a • U
  let W := γ (s + h) - normalRibbonPoint γ N a s
  let C := h • cross3 A T + a • cross3 T V
  let F := cross3 (P - T - h • A) T + a • cross3 (P - T) V
  let r := Real.sqrt (h ^ 2 + a ^ 2)
  let l := euclideanLength W
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have ha0 : 0 ≤ a := ha.le
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = h ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hhr : |h| ≤ r := by
    apply le_of_sq_le_sq _ hr.le
    rw [sq_abs, hr2]
    linarith [sq_nonneg a]
  have har : a ≤ r := by
    apply le_of_sq_le_sq _ hr.le
    rw [hr2]
    linarith [sq_nonneg h]
  have hW : W - Z = E := by
    dsimp only [W, Z, E, U, normalRibbonPoint]
    abel
  have hE0 : ‖E‖ ≤ B * |h| ^ 2 := norm_sub_linear_le hγ hT hbA s h
  have hE : ‖E‖ ≤ B * r ^ 2 :=
    hE0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg h) hhr 2) hBpos.le)
  have hZlen : euclideanLength Z = r := euclideanLength_tangent_normal htunit hnunit horth h a
  have hZ : ‖Z‖ ≤ r := (norm_le_euclideanLength _).trans_eq hZlen
  have hlerr : |l - r| ≤ 3 * B * |h| ^ 2 := by
    change |euclideanLength W - r| ≤ _
    rw [← hZlen]
    calc
      _ ≤ euclideanLength (W - Z) := abs_euclideanLength_sub_le _ _
      _ ≤ 3 * ‖E‖ := by rw [hW]; exact euclideanLength_le_three_norm E
      _ ≤ _ := by linarith only [hE0]
  have hsmall := (le_div_iff₀ (by positivity : 0 < 6 * B)).1 hh
  have hlrough : |l - r| ≤ r / 2 := by
    refine hlerr.trans ?_
    have hstep := mul_le_mul_of_nonneg_right hsmall (abs_nonneg h)
    nlinarith only [hstep, hhr]
  have hl : r / 2 ≤ l := by linarith [(abs_le.mp hlrough).1]
  have hupper : l ≤ 2 * r := by linarith [(abs_le.mp hlrough).2]
  have hWnorm : ‖W‖ ≤ 2 * r := (norm_le_euclideanLength _).trans hupper
  have hC : ‖C‖ ≤ 4 * B ^ 2 * r := by
    have hAT : ‖cross3 A T‖ ≤ 2 * B ^ 2 := by
      refine (norm_cross3_le_mul _ _).trans ?_
      have hprod : 2 * ‖A‖ * ‖T‖ ≤ 2 * B * B := by
        gcongr <;> first | exact hbA s | exact hbT s
      exact hprod.trans_eq (by ring)
    have hTV : ‖cross3 T V‖ ≤ 2 * B ^ 2 := by
      refine (norm_cross3_le_mul _ _).trans ?_
      have hprod : 2 * ‖T‖ * ‖V‖ ≤ 2 * B * B := by
        gcongr <;> first | exact hbT s | exact hbN s
      exact hprod.trans_eq (by ring)
    calc
      _ ≤ |h| * ‖cross3 A T‖ + a * ‖cross3 T V‖ := by
        simpa only [C, norm_smul, Real.norm_eq_abs, abs_of_pos ha] using
          norm_add_le (h • cross3 A T) (a • cross3 T V)
      _ ≤ r * (2 * B ^ 2) + r * (2 * B ^ 2) := by gcongr
      _ = _ := by ring
  have hF : ‖F‖ ≤ 4 * B ^ 2 * r ^ 2 := by
    have hPdev : ‖P - T‖ ≤ B * |h| := norm_increment_le hT hbA s h
    have hPrem : ‖P - T - h • A‖ ≤ B * |h| ^ 2 := norm_sub_linear_le hT hA hbJ s h
    have hFT : ‖cross3 (P - T - h • A) T‖ ≤ 2 * (B * r ^ 2) * B := by
      refine (norm_cross3_le_mul _ _).trans ?_
      have href : ‖P - T - h • A‖ ≤ B * r ^ 2 := hPrem.trans (by gcongr)
      have ht : ‖T‖ ≤ B := hbT s
      gcongr
    have hFV : ‖cross3 (P - T) V‖ ≤ 2 * (B * r) * B := by
      refine (norm_cross3_le_mul _ _).trans ?_
      have href : ‖P - T‖ ≤ B * r := hPdev.trans (by gcongr)
      have hv : ‖V‖ ≤ B := hbN s
      gcongr
    calc
      _ ≤ ‖cross3 (P - T - h • A) T‖ + a * ‖cross3 (P - T) V‖ := by
        simpa only [F, norm_smul, Real.norm_eq_abs, abs_of_pos ha] using
          norm_add_le (cross3 (P - T - h • A) T) (a • cross3 (P - T) V)
      _ ≤ 2 * (B * r ^ 2) * B + r * (2 * (B * r) * B) := by gcongr
      _ = _ := by ring
  let m := dot3 C Z
  let n := dot3 (C + F) W
  have hm : |m| ≤ (12 * B ^ 2) * r ^ 2 := by
    calc
      _ ≤ 3 * ‖C‖ * ‖Z‖ := abs_dot3_le _ _
      _ ≤ 3 * (4 * B ^ 2 * r) * r := by gcongr
      _ = _ := by ring
  have hnEq : n - m = dot3 C E + dot3 F W := by
    rw [← hW]
    simp only [n, m, dot3, Pi.add_apply, Pi.sub_apply]
    ring
  have hn : |n - m| ≤ (12 * B ^ 3 + 24 * B ^ 2) * r ^ 3 := by
    rw [hnEq]
    calc
      _ ≤ |dot3 C E| + |dot3 F W| := abs_add_le _ _
      _ ≤ 3 * ‖C‖ * ‖E‖ + 3 * ‖F‖ * ‖W‖ := add_le_add (abs_dot3_le _ _) (abs_dot3_le _ _)
      _ ≤ 3 * (4 * B ^ 2 * r) * (B * r ^ 2) + 3 * (4 * B ^ 2 * r ^ 2) * (2 * r) := by gcongr
      _ = _ := by ring
  have herr := abs_div_cube_sub_le (D := 3 * B) hr (by positivity) (by positivity) (by positivity)
    hl hupper (hlerr.trans (by gcongr)) hm hn
  have hker : gaussKernel γ (normalRibbonPoint γ N a) (s + h) s = n / (4 * π * l ^ 3) := by
    rw [gaussKernel, (hasDerivAt_normalRibbonPoint (a := a) (hγ s) (hN s)).deriv]
    change dot3 (cross3 P (T + a • V)) W / (4 * π * l ^ 3) = _
    rw [cross3_tangent_expansion T A V P h a]
  have hmodel : frozenRibbonKernel γ N a s h = m / (4 * π * r ^ 3) := by
    unfold frozenRibbonKernel
    rw [show m = a ^ 2 * ribbonTwistDensity γ N s + a * h * ribbonBendDensity γ N s from
      dot3_tangent_profile T A U V h a]
  rw [hker, hmodel, show n / (4 * π * l ^ 3) - m / (4 * π * r ^ 3) =
    (n / l ^ 3 - m / r ^ 3) / (4 * π) by simp only [div_eq_mul_inv, mul_inv_rev]; ring,
    abs_div, abs_of_pos (by positivity : 0 < 4 * π)]
  exact div_le_div_of_nonneg_right herr (by positivity)

/-- A periodic unit-speed curve and a periodic unit framing admit a uniform
pointwise error bound on a fixed narrow band around their circular diagonal. -/
theorem exists_abs_normalRibbon_kernel_sub_le {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 3 γ) (hN : ContDiff ℝ 1 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hspeed : ∀ s, dot3 (deriv γ s) (deriv γ s) = 1)
    (hunit : ∀ s, dot3 (N s) (N s) = 1)
    (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ η > 0, ∃ K ≥ (0 : ℝ), ∀ a s h : ℝ, 0 < a → |h| ≤ η →
      |gaussKernel γ (normalRibbonPoint γ N a) (s + h) s - frozenRibbonKernel γ N a s h| ≤ K := by
  have hT : ContDiff ℝ 2 (deriv γ) := ContDiff.deriv' hγ
  have hA : ContDiff ℝ 1 (deriv (deriv γ)) := ContDiff.deriv' hT
  have hγd := hγ.differentiable (by norm_num)
  have hTd := hT.differentiable (by norm_num)
  have hAd := hA.differentiable (by norm_num)
  have hNd := hN.differentiable (by norm_num)
  have hpT := periodic_deriv_curve hpγ hγd
  have hpA := periodic_deriv_curve hpT hTd
  have hpJ := periodic_deriv_curve hpA hAd
  have hpV := periodic_deriv_curve hpN hNd
  obtain ⟨T, hBT⟩ := periodic_norm_bound hT.continuous hpT
  obtain ⟨A, hBA⟩ := periodic_norm_bound hA.continuous hpA
  obtain ⟨J, hBJ⟩ := periodic_norm_bound hA.continuous_deriv_one hpJ
  obtain ⟨V, hBV⟩ := periodic_norm_bound hN.continuous_deriv_one hpV
  let B := max (max 1 T) (max A (max J V))
  have hB : 1 ≤ B := (le_max_left 1 T).trans (le_max_left _ _)
  have hBp := zero_lt_one.trans_le hB
  have hbT (s : ℝ) : ‖deriv γ s‖ ≤ B :=
    (hBT s).trans ((le_max_right 1 T).trans (le_max_left _ _))
  have hbA (s : ℝ) : ‖deriv (deriv γ) s‖ ≤ B :=
    (hBA s).trans ((le_max_left A (max J V)).trans (le_max_right _ _))
  have hbJ (s : ℝ) : ‖deriv (deriv (deriv γ)) s‖ ≤ B :=
    (hBJ s).trans ((le_max_left J V).trans ((le_max_right A (max J V)).trans (le_max_right _ _)))
  have hbV (s : ℝ) : ‖deriv N s‖ ≤ B :=
    (hBV s).trans ((le_max_right J V).trans ((le_max_right A (max J V)).trans (le_max_right _ _)))
  let K := (8 * (12 * B ^ 3 + 24 * B ^ 2) + 56 * (12 * B ^ 2) * (3 * B)) / (4 * π)
  refine ⟨1 / (6 * B), by positivity, K, by dsimp only [K]; positivity, fun a s h ha hh => ?_⟩
  exact abs_normalRibbon_kernel_sub_le hγd hTd hAd hNd hB hbT hbA hbJ hbV
    ha hh (hspeed s) (hunit s) (horth s)

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
