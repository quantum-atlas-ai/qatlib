/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.WritheGeometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Near-diagonal cancellation of the self Gauss kernel numerator

[Kedia2018SuperfluidHelicity], Section II, [DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The writhe integrand's numerator `(T s × T t) · (γ t − γ s)` vanishes to third order as
`t → s`. By the fundamental theorem of calculus and the repeated-vector triple-product
identity it equals the integral of `(T s × T t) · (T u − T s)` over `[s, t]`, whose two
factors are each `O(|t − s|)` for a `C²` curve. Under the explicit bounds `‖T‖ ≤ B` and
`‖γ''‖ ≤ M` we obtain the quantitative estimate `≤ 6 · B · M² · |t − s|³`.

This is the analytic cancellation that keeps the writhe kernel bounded near the diagonal.
Combining it with a chord-arc lower bound for the chord `γ t − γ s` bounds the kernel near
the diagonal; together with the far-field estimate and the positive far-set chord minimum
of a simple curve (both proved here), this yields integrability of the self Gauss kernel
on the parameter square, discharging the hypothesis of the band-shrink limit.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open Filter
open scoped Real ENNReal

/-! ### Cartesian norm estimates -/

/-- A scalar triple product with a repeated vector vanishes identically. -/
theorem dot3_cross3_self_left (a b : Fin 3 → ℝ) : dot3 (cross3 a b) a = 0 := by
  simp only [dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
  ring

/-- The Cartesian dot product is symmetric. -/
theorem dot3_comm (u v : Fin 3 → ℝ) : dot3 u v = dot3 v u := by
  simp only [dot3]
  ring

/-- The dot product is linear in its first argument as well. -/
theorem dot3_sub_left (n u v : Fin 3 → ℝ) : dot3 (u - v) n = dot3 u n - dot3 v n := by
  simp only [dot3, Pi.sub_apply]
  ring

/-- The Cartesian dot product is bounded by the product of the sup norms with an explicit
dimension constant. -/
theorem abs_dot3_le (u v : Fin 3 → ℝ) : |dot3 u v| ≤ 3 * ‖u‖ * ‖v‖ := by
  have hdot : dot3 u v = ∑ i : Fin 3, u i * v i := by
    simp only [dot3, Fin.sum_univ_three]
  rw [hdot]
  have h1 : |∑ i : Fin 3, u i * v i| ≤ ∑ i : Fin 3, |u i * v i| :=
    Finset.abs_sum_le_sum_abs (fun i => u i * v i) Finset.univ
  have h2 : ∑ i : Fin 3, |u i * v i| ≤ ∑ i : Fin 3, ‖u‖ * ‖v‖ := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hu : |u i| ≤ ‖u‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u i
    have hv : |v i| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) (norm_nonneg u)
  have h3 : ∑ i : Fin 3, ‖u‖ * ‖v‖ = 3 * ‖u‖ * ‖v‖ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  exact h1.trans (h2.trans h3.le)

/-- A single product of components is bounded by the product of the sup norms. -/
theorem abs_mul_component_le (w z : Fin 3 → ℝ) (i j : Fin 3) : |w i * z j| ≤ ‖w‖ * ‖z‖ := by
  have h1 : |w i| ≤ ‖w‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w i
  have h2 : |z j| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z j
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg w)

/-- The cross product of two vectors is controlled by the deviation of the second from the
first: `‖a × b‖ ≤ 2 · ‖a‖ · ‖b − a‖`, since `a × a = 0`. -/
theorem norm_cross3_le (a b : Fin 3 → ℝ) : ‖cross3 a b‖ ≤ 2 * ‖a‖ * ‖b - a‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have hbd : ∀ j : Fin 3, |cross3 a (b - a) j| ≤ 2 * ‖a‖ * ‖b - a‖ := by
    intro j
    fin_cases j
    · show |a 1 * (b - a) 2 - a 2 * (b - a) 1| ≤ 2 * ‖a‖ * ‖b - a‖
      exact (abs_sub _ _).trans ((add_le_add (abs_mul_component_le a (b - a) 1 2)
        (abs_mul_component_le a (b - a) 2 1)).trans_eq (by ring))
    · show |a 2 * (b - a) 0 - a 0 * (b - a) 2| ≤ 2 * ‖a‖ * ‖b - a‖
      exact (abs_sub _ _).trans ((add_le_add (abs_mul_component_le a (b - a) 2 0)
        (abs_mul_component_le a (b - a) 0 2)).trans_eq (by ring))
    · show |a 0 * (b - a) 1 - a 1 * (b - a) 0| ≤ 2 * ‖a‖ * ‖b - a‖
      exact (abs_sub _ _).trans ((add_le_add (abs_mul_component_le a (b - a) 0 1)
        (abs_mul_component_le a (b - a) 1 0)).trans_eq (by ring))
  have hkey : cross3 a b k = cross3 a (b - a) k := by
    fin_cases k
    · show a 1 * b 2 - a 2 * b 1 = a 1 * (b - a) 2 - a 2 * (b - a) 1
      simp only [Pi.sub_apply]; ring
    · show a 2 * b 0 - a 0 * b 2 = a 2 * (b - a) 0 - a 0 * (b - a) 2
      simp only [Pi.sub_apply]; ring
    · show a 0 * b 1 - a 1 * b 0 = a 0 * (b - a) 1 - a 1 * (b - a) 0
      simp only [Pi.sub_apply]; ring
  rw [hkey]
  exact hbd k

/-! ### The tangent deviation estimate -/

/-- A `C²` curve whose second derivative is uniformly bounded has `M`-Lipschitz tangent. -/
theorem norm_deriv_sub_le (γ : ℝ → (Fin 3 → ℝ)) (hγ : ContDiff ℝ 2 γ) {M : ℝ}
    (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M) (u v : ℝ) (hvu : v ≤ u) :
    ‖deriv γ u - deriv γ v‖ ≤ M * (u - v) := by
  have hd1 : ContDiff ℝ 1 (deriv γ) := ContDiff.deriv' hγ
  have hdiff2 : ∀ x : ℝ, HasDerivAt (deriv γ) (deriv (deriv γ) x) x := fun x =>
    ((hd1.differentiable (by norm_num)).differentiableAt).hasDerivAt
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x _ => (hdiff2 x).hasDerivWithinAt) (fun x _ => hM x) u
    (Set.mem_Icc.2 ⟨hvu, le_refl u⟩)

/-! ### The integral representation and the cubic estimate -/

/-- Integral representation of the self Gauss numerator: `(T s × T t) · (γ t − γ s)` equals
the integral of `(T s × T t) · (T u − T s)` over `[s, t]`; the component along `T s` drops
out because a triple product with a repeated vector vanishes. This is the cancellation
that produces the third-order vanishing at the diagonal. -/
theorem dot3_cross3_sub_integral (γ : ℝ → (Fin 3 → ℝ)) (hγ : ContDiff ℝ 2 γ) (s t : ℝ) :
    dot3 (cross3 (deriv γ s) (deriv γ t)) (γ t - γ s)
      = ∫ u in s..t, dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s) := by
  have hdiff : ∀ u : ℝ, HasDerivAt γ (deriv γ u) u := fun u =>
    ((hγ.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcomp : ∀ u : ℝ, HasDerivAt (fun w => dot3 (cross3 (deriv γ s) (deriv γ t)) (γ w))
      (dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u)) u := by
    intro u
    have h := HasFDerivAt.comp_hasDerivAt u
      ((dot3CLM (cross3 (deriv γ s) (deriv γ t))).hasFDerivAt) (hdiff u)
    rw [show (dot3CLM (cross3 (deriv γ s) (deriv γ t)) ∘ γ)
        = fun w => dot3 (cross3 (deriv γ s) (deriv γ t)) (γ w) from
      funext fun w =>
        dot3CLM_apply (cross3 (deriv γ s) (deriv γ t)) (γ w),
      dot3CLM_apply (cross3 (deriv γ s) (deriv γ t)) (deriv γ u)] at h
    exact h
  have hint : IntervalIntegrable (fun u => dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u))
      volume s t := by
    have hT : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
    have hc : Continuous fun u => dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u) := by
      have h := ((dot3CLM (cross3 (deriv γ s) (deriv γ t))).continuous.comp hT)
      rwa [show (dot3CLM (cross3 (deriv γ s) (deriv γ t)) ∘ deriv γ)
          = fun u => dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u) from
        funext fun u =>
          dot3CLM_apply (cross3 (deriv γ s) (deriv γ t)) (deriv γ u)] at h
    exact hc.intervalIntegrable s t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hcomp u) hint
  have hEq : dot3 (cross3 (deriv γ s) (deriv γ t)) (γ t - γ s)
      = ∫ u in s..t, dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u) := by
    rw [hFTC, dot3_sub]
  have hfun : Set.EqOn (fun u => dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u))
      (fun u => dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s))
      (Set.uIcc s t) := fun u _ => by
    show dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u)
      = dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s)
    rw [dot3_sub, dot3_cross3_self_left, sub_zero]
  rw [hEq, intervalIntegral.integral_congr hfun]

/-- Quantitative near-diagonal cancellation: under explicit uniform bounds `‖γ'‖ ≤ B` and
`‖γ''‖ ≤ M`, the self Gauss numerator is at most `6 · B · M² · |t − s|³`. -/
theorem abs_dot3_cross3_le (γ : ℝ → (Fin 3 → ℝ)) {B M : ℝ} (hγ : ContDiff ℝ 2 γ)
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M) (s t : ℝ) :
    |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ t - γ s)| ≤ 6 * B * M ^ 2 * |t - s| ^ 3 := by
  have hB0 : (0 : ℝ) ≤ B := (norm_nonneg (deriv γ s)).trans (hB s)
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (deriv (deriv γ) s)).trans (hM s)
  have hswap : ∀ s t : ℝ, s ≤ t →
      |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ t - γ s)| ≤ 6 * B * M ^ 2 * (t - s) ^ 3 := by
    intro s t hst
    rw [dot3_cross3_sub_integral γ hγ s t, ← Real.norm_eq_abs]
    have hTs : ‖deriv γ t - deriv γ s‖ ≤ M * (t - s) :=
      norm_deriv_sub_le γ hγ hM t s hst
    have hX : ‖cross3 (deriv γ s) (deriv γ t)‖ ≤ 2 * B * (M * (t - s)) := by
      refine (norm_cross3_le (deriv γ s) (deriv γ t)).trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hB s) (by norm_num)) hTs
        (norm_nonneg _) (mul_nonneg (by norm_num) hB0)
    have hae : ∀ᵐ u ∂volume, u ∈ Set.Ioc s t →
        ‖dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s)‖
          ≤ 6 * B * M ^ 2 * (t - s) ^ 2 := by
      filter_upwards with u hu
      have hus : u - s ≤ t - s := sub_le_sub_right hu.2 _
      have hTu : ‖deriv γ u - deriv γ s‖ ≤ M * (t - s) :=
        (norm_deriv_sub_le γ hγ hM u s hu.1.le).trans
          (mul_le_mul_of_nonneg_left hus hM0)
      have hab : ‖cross3 (deriv γ s) (deriv γ t)‖ * ‖deriv γ u - deriv γ s‖
          ≤ (2 * B * (M * (t - s))) * (M * (t - s)) :=
        mul_le_mul hX hTu (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB0)
            (mul_nonneg hM0 (sub_nonneg.mpr hst)))
      have hstep : ‖dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s)‖
          ≤ 3 * (2 * B * (M * (t - s))) * (M * (t - s)) :=
        calc ‖dot3 (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s)‖
            ≤ 3 * ‖cross3 (deriv γ s) (deriv γ t)‖ * ‖deriv γ u - deriv γ s‖ := by
              rw [Real.norm_eq_abs]
              exact abs_dot3_le (cross3 (deriv γ s) (deriv γ t)) (deriv γ u - deriv γ s)
          _ ≤ 3 * ((2 * B * (M * (t - s))) * (M * (t - s))) := by
              nlinarith [hab, hB0, hM0, hst]
          _ = 3 * (2 * B * (M * (t - s))) * (M * (t - s)) := by ring
      rw [Real.norm_eq_abs] at hstep ⊢
      nlinarith [hstep, hB0, hM0, hst]
    refine (intervalIntegral.norm_integral_le_of_norm_le hst hae
      (continuous_const.intervalIntegrable s t :
        IntervalIntegrable (fun _ : ℝ => 6 * B * M ^ 2 * (t - s) ^ 2) volume s t)).trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    exact le_of_eq (by ring)
  rcases le_total s t with hst | hst
  · exact (hswap s t hst).trans (le_of_eq (by rw [abs_of_nonneg (sub_nonneg.mpr hst)]))
  · have hEq : dot3 (cross3 (deriv γ s) (deriv γ t)) (γ t - γ s)
        = dot3 (cross3 (deriv γ t) (deriv γ s)) (γ s - γ t) := by
      rw [cross3_antisymm (deriv γ s) (deriv γ t),
        show γ s - γ t = -(γ t - γ s) from by ring, dot3_neg_neg]
    rw [hEq]
    exact (hswap t s hst).trans (le_of_eq (by
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]; ring))

/-! ### Chord-arc lower bound and near-diagonal kernel boundedness -/

/-- Local chord-arc lower bound for an immersed `C²` curve with Euclidean speed uniformly
at least `τ`: as long as the parameter gap is small enough relative to the tangent
Lipschitz constant, the chord length is at least a fixed multiple of the parameter
difference. -/
theorem norm_chord_ge_of_sqSpeed_ge (γ : ℝ → (Fin 3 → ℝ)) (hγ : ContDiff ℝ 2 γ)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    (s t : ℝ) (hst : s ≤ t) (hsmall : 3 * M * B * (t - s) ≤ τ ^ 2 / 2) :
    τ ^ 2 / (6 * B) * (t - s) ≤ ‖γ t - γ s‖ := by
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (deriv (deriv γ) s)).trans (hM s)
  have hB0 : (0 : ℝ) < B := by
    have h1 := abs_dot3_le (deriv γ s) (deriv γ s)
    have h2 := hτ s
    have hnn : (0 : ℝ) ≤ dot3 (deriv γ s) (deriv γ s) := by
      have hsum : dot3 (deriv γ s) (deriv γ s)
          = ∑ i : Fin 3, (deriv γ s) i * (deriv γ s) i := by
        simp only [dot3, Fin.sum_univ_three]
      rw [hsum]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith [h1, h2, hnn, hτ0, hB s, abs_of_nonneg hnn,
      norm_nonneg (deriv γ s)]
  have hgd : ∀ u : ℝ, HasDerivAt (fun w => dot3 (γ w) (deriv γ s))
      (dot3 (deriv γ u) (deriv γ s)) u := by
    intro u
    have h := HasFDerivAt.comp_hasDerivAt u ((dot3CLM (deriv γ s)).hasFDerivAt)
      ((hγ.differentiable (by norm_num)).differentiableAt).hasDerivAt
    rw [show (dot3CLM (deriv γ s) ∘ γ) = fun w => dot3 (γ w) (deriv γ s) from
        funext fun w => by rw [Function.comp_apply, dot3CLM_apply, dot3_comm],
      show dot3CLM (deriv γ s) (deriv γ u) = dot3 (deriv γ u) (deriv γ s) from
        by rw [dot3CLM_apply, dot3_comm]] at h
    exact h
  have hint : IntervalIntegrable (fun u => dot3 (deriv γ u) (deriv γ s)) volume s t := by
    have hc : Continuous fun u => dot3 (deriv γ u) (deriv γ s) := by
      have h := ((dot3CLM (deriv γ s)).continuous.comp (hγ.continuous_deriv (by norm_num)))
      rwa [show (dot3CLM (deriv γ s) ∘ deriv γ)
          = fun u => dot3 (deriv γ u) (deriv γ s) from
        funext fun u => by rw [Function.comp_apply, dot3CLM_apply, dot3_comm]] at h
    exact hc.intervalIntegrable s t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hgd u) hint
  have hlow : ∀ u ∈ Set.Icc s t, τ ^ 2 / 2 ≤ dot3 (deriv γ u) (deriv γ s) := by
    intro u hu
    have hsplit : dot3 (deriv γ u) (deriv γ s)
        = dot3 (deriv γ s) (deriv γ s) + dot3 (deriv γ u - deriv γ s) (deriv γ s) := by
      rw [dot3_sub_left]
      ring
    have hus : u - s ≤ t - s := sub_le_sub_right hu.2 _
    have hm : ‖deriv γ u - deriv γ s‖ * ‖deriv γ s‖ ≤ (M * (u - s)) * B :=
      le_trans (mul_le_mul_of_nonneg_right (norm_deriv_sub_le γ hγ hM u s hu.1)
        (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hB s) (mul_nonneg hM0 (sub_nonneg.mpr hu.1)))
    have hx := abs_dot3_le (deriv γ u - deriv γ s) (deriv γ s)
    have h1 : |dot3 (deriv γ u - deriv γ s) (deriv γ s)| ≤ 3 * (M * (u - s)) * B := by
      calc |dot3 (deriv γ u - deriv γ s) (deriv γ s)|
          ≤ 3 * ‖deriv γ u - deriv γ s‖ * ‖deriv γ s‖ := hx
        _ ≤ 3 * (M * (u - s)) * B := by nlinarith [hm]
    have hneg : -(3 * M * B * (t - s)) ≤ dot3 (deriv γ u - deriv γ s) (deriv γ s) := by
      have hBge : (0 : ℝ) ≤ B := (norm_nonneg (deriv γ s)).trans (hB s)
      have hMB : (0 : ℝ) ≤ 3 * M * B := by nlinarith [hM0, hBge]
      have htupos : (0 : ℝ) ≤ t - u := by linarith [hu.2]
      have hC : 3 * (M * (u - s)) * B ≤ 3 * M * B * (t - s) := by nlinarith [htupos, hMB]
      exact (neg_le_neg hC).trans (abs_le.mp h1).1
    rw [hsplit]
    nlinarith [hτ s, hneg, hsmall, hM0, hB0.le]
  have hintconst : IntervalIntegrable (fun _ : ℝ => τ ^ 2 / 2) volume s t :=
    continuous_const.intervalIntegrable s t
  have hmono := intervalIntegral.integral_mono_on hst hintconst hint hlow
  have hconst : ∫ _ in s..t, (τ ^ 2 / 2 : ℝ) = τ ^ 2 / 2 * (t - s) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [hconst] at hmono
  rw [hFTC, dot3_comm (γ t) (deriv γ s), dot3_comm (γ s) (deriv γ s), ← dot3_sub,
    dot3_comm (deriv γ s) (γ t - γ s)] at hmono
  have hx := abs_dot3_le (γ t - γ s) (deriv γ s)
  have habs : |dot3 (γ t - γ s) (deriv γ s)| ≤ 3 * ‖γ t - γ s‖ * B := by
    calc |dot3 (γ t - γ s) (deriv γ s)|
        ≤ 3 * ‖γ t - γ s‖ * ‖deriv γ s‖ := hx
      _ ≤ 3 * ‖γ t - γ s‖ * B :=
          mul_le_mul_of_nonneg_left (hB s) (mul_nonneg (by norm_num) (norm_nonneg _))
  have hkey : τ ^ 2 / 2 * (t - s) ≤ 3 * ‖γ t - γ s‖ * B := hmono.trans (abs_le.mp habs).2
  have hkey' : τ ^ 2 * (t - s) ≤ ‖γ t - γ s‖ * (6 * B) := by
    have h2 : (2 : ℝ) * (τ ^ 2 / 2 * (t - s)) ≤ 2 * (3 * ‖γ t - γ s‖ * B) :=
      mul_le_mul_of_nonneg_left hkey (by norm_num)
    rw [show (2 : ℝ) * (τ ^ 2 / 2 * (t - s)) = τ ^ 2 * (t - s) from by field_simp] at h2
    linarith
  rw [show τ ^ 2 / (6 * B) * (t - s) = τ ^ 2 * (t - s) / (6 * B) from by ring,
    div_le_iff₀ (by nlinarith [hB0] : (0 : ℝ) < 6 * B)]
  exact hkey'

/-- Near-diagonal boundedness of the self Gauss kernel: combining the cubic cancellation
of the numerator with the chord-arc lower bound, the writhe kernel is bounded by an
explicit constant whenever the parameter difference is small enough. Far-field
boundedness (available for simple curves by compactness) is still needed for global
boundedness and is not provided here. -/
theorem abs_writheKernel_le_near (γ : ℝ → (Fin 3 → ℝ)) (hγ : ContDiff ℝ 2 γ)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    (s t : ℝ) (hsmall : 3 * M * B * |t - s| ≤ τ ^ 2 / 2) :
    |writheKernel γ s t| ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) := by
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (deriv (deriv γ) s)).trans (hM s)
  have hB0 : (0 : ℝ) < B := by
    have h1 := abs_dot3_le (deriv γ s) (deriv γ s)
    have h2 := hτ s
    have hnn : (0 : ℝ) ≤ dot3 (deriv γ s) (deriv γ s) := by
      have hsum : dot3 (deriv γ s) (deriv γ s)
          = ∑ i : Fin 3, (deriv γ s) i * (deriv γ s) i := by
        simp only [dot3, Fin.sum_univ_three]
      rw [hsum]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith [h1, h2, hnn, hτ0, hB s, abs_of_nonneg hnn,
      norm_nonneg (deriv γ s)]
  have hK : (0 : ℝ) ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB0.le 4)) (pow_nonneg hM0 2))
      (le_of_lt (mul_pos Real.pi_pos (pow_pos hτ0 6)))
  rcases eq_or_ne s t with rfl | hne
  · rw [writheKernel_diag_eq_zero, abs_zero]
    exact hK
  have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hchord : τ ^ 2 / (6 * B) * |t - s| ≤ ‖γ t - γ s‖ := by
    rcases le_total s t with hst | hst
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      refine norm_chord_ge_of_sqSpeed_ge γ hγ hτ0 hτ hB hM s t hst ?_
      rwa [abs_of_nonneg (sub_nonneg.mpr hst)] at hsmall
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
      exact norm_chord_ge_of_sqSpeed_ge γ hγ hτ0 hτ hB hM t s hst
        (by rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)] at hsmall)
  have hcpos : (0 : ℝ) < τ ^ 2 / (6 * B) * |t - s| :=
    mul_pos (div_pos (by nlinarith [hτ0]) (by nlinarith [hB0])) hpos
  have hnorm : (0 : ℝ) < ‖γ t - γ s‖ := lt_of_lt_of_le hcpos hchord
  have hlength := norm_le_euclideanLength (γ t - γ s)
  have hden : (0 : ℝ) < 4 * π * euclideanLength (γ t - γ s) ^ 3 :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos (hnorm.trans_le hlength) 3)
  have hnum := abs_dot3_cross3_le γ hγ hB hM s t
  have hcub : (τ ^ 2 / (6 * B) * |t - s|) ^ 3 ≤ euclideanLength (γ t - γ s) ^ 3 :=
    pow_le_pow_left₀ (le_of_lt hcpos) (hchord.trans hlength) 3
  have hnum' : |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t)|
      ≤ 6 * B * M ^ 2 * |t - s| ^ 3 := by
    rw [show γ s - γ t = (-1 : ℝ) • (γ t - γ s) from by rw [neg_one_smul, neg_sub],
      dot3_smul_right, neg_one_mul, abs_neg]
    exact hnum
  rw [writheKernel, gaussKernel, abs_div, euclideanLength_sub_rev, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  calc |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t)|
      ≤ 6 * B * M ^ 2 * |t - s| ^ 3 := hnum'
    _ = 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (4 * π * (τ ^ 2 / (6 * B) * |t - s|) ^ 3) := by
        field_simp
        ring
    _ ≤ 324 * B ^ 4 * M ^ 2 / (π * τ ^ 6) * (4 * π * euclideanLength (γ t - γ s) ^ 3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcub (mul_nonneg (by norm_num) Real.pi_pos.le)) hK

/-! ### Far-field boundedness -/

/-- The cross product is bounded by twice the product of the norms: each component is a
planar determinant controlled by the component-wise products. -/
theorem norm_cross3_le_mul (a b : Fin 3 → ℝ) : ‖cross3 a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  fin_cases k
  · show |a 1 * b 2 - a 2 * b 1| ≤ 2 * ‖a‖ * ‖b‖
    exact (abs_sub _ _).trans ((add_le_add (abs_mul_component_le a b 1 2)
      (abs_mul_component_le a b 2 1)).trans_eq (by ring))
  · show |a 2 * b 0 - a 0 * b 2| ≤ 2 * ‖a‖ * ‖b‖
    exact (abs_sub _ _).trans ((add_le_add (abs_mul_component_le a b 2 0)
      (abs_mul_component_le a b 0 2)).trans_eq (by ring))
  · show |a 0 * b 1 - a 1 * b 0| ≤ 2 * ‖a‖ * ‖b‖
    exact (abs_sub _ _).trans ((add_le_add (abs_mul_component_le a b 0 1)
      (abs_mul_component_le a b 1 0)).trans_eq (by ring))

/-- Far-field bound for the writhe kernel: away from coincident points the kernel is
controlled by the inverse square of the chord, with the tangent sup bound `B` as the only
curvature input. Combined with a positive lower bound on the chord (available on the
far set of a simple curve by compactness), this yields a uniform far-field bound. -/
theorem abs_writheKernel_le_far (γ : ℝ → (Fin 3 → ℝ)) {B : ℝ} (hB : ∀ u, ‖deriv γ u‖ ≤ B)
    (s t : ℝ) (hc : γ s ≠ γ t) :
    |writheKernel γ s t| ≤ 3 * B ^ 2 / (2 * π * ‖γ s - γ t‖ ^ 2) := by
  have hcne : γ s - γ t ≠ 0 := sub_ne_zero.mpr hc
  have hnc : (0 : ℝ) < ‖γ s - γ t‖ := norm_pos_iff.mpr hcne
  have hlength := norm_le_euclideanLength (γ s - γ t)
  have hden : (0 : ℝ) < 4 * π * euclideanLength (γ s - γ t) ^ 3 :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos (hnc.trans_le hlength) 3)
  have hx := abs_dot3_le (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t)
  have hnum : |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t)|
      ≤ 6 * B ^ 2 * ‖γ s - γ t‖ := by
    have hcross : ‖cross3 (deriv γ s) (deriv γ t)‖ ≤ 2 * B * B := by
      have h2 := norm_cross3_le_mul (deriv γ s) (deriv γ t)
      have hTs := hB s
      have hTt := hB t
      have hTs0 := norm_nonneg (deriv γ s)
      have hTt0 := norm_nonneg (deriv γ t)
      nlinarith [h2, hTs, hTt, hTs0, hTt0]
    calc |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t)|
        ≤ 3 * ‖cross3 (deriv γ s) (deriv γ t)‖ * ‖γ s - γ t‖ := hx
      _ ≤ 3 * (2 * B * B) * ‖γ s - γ t‖ := by
          nlinarith [hcross, norm_nonneg (γ s - γ t)]
      _ = 6 * B ^ 2 * ‖γ s - γ t‖ := by ring
  rw [writheKernel, gaussKernel, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |dot3 (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t)|
      ≤ 6 * B ^ 2 * ‖γ s - γ t‖ := hnum
    _ = 3 * B ^ 2 / (2 * π * ‖γ s - γ t‖ ^ 2) * (4 * π * ‖γ s - γ t‖ ^ 3) := by
        have hc0 : ‖γ s - γ t‖ ≠ 0 := ne_of_gt hnc
        have hπ0 : π ≠ 0 := Real.pi_pos.ne'
        field_simp [hc0, hπ0]
        ring
    _ ≤ 3 * B ^ 2 / (2 * π * ‖γ s - γ t‖ ^ 2) *
        (4 * π * euclideanLength (γ s - γ t) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hnc.le hlength 3) (by positivity))
        (by positivity)

/-- A positive chord lower bound on the far set of a simple arc: on the compact part of
the parameter square with `δ ≤ |t - s|`, an injective continuous curve has a strictly
positive minimum chord. This supplies the uniform lower bound needed to turn the
far-field kernel estimate into a global bound. -/
theorem exists_pos_le_norm_sub_of_injective_on (γ : ℝ → (Fin 3 → ℝ)) (hγ : Continuous γ)
    (hinj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ s = γ t → s = t)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    ∃ m, 0 < m ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      δ ≤ |t - s| → m ≤ ‖γ t - γ s‖ := by
  have hKclosed : IsClosed {p : ℝ × ℝ | δ ≤ |p.2 - p.1|} :=
    isClosed_le continuous_const
      (continuous_abs.comp (continuous_snd.sub continuous_fst))
  have hKc : IsCompact ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩
      {p : ℝ × ℝ | δ ≤ |p.2 - p.1|}) :=
    IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc)
      ((isClosed_Icc.prod isClosed_Icc).inter hKclosed) Set.inter_subset_left
  have hfn : Continuous fun p : ℝ × ℝ => ‖γ p.2 - γ p.1‖ :=
    ((hγ.comp continuous_snd).sub (hγ.comp continuous_fst)).norm
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨le_refl 0, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨zero_le_one, le_refl 1⟩
  have hKne : (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∩
      {p : ℝ × ℝ | δ ≤ |p.2 - p.1|}).Nonempty := by
    refine ⟨(0, 1), ⟨⟨h01, h11⟩, ?_⟩⟩
    show δ ≤ |(1 : ℝ) - 0|
    rw [sub_zero, abs_one]
    exact hδle
  obtain ⟨p₀, hp₀mem, hmin⟩ := hKc.exists_isMinOn hKne hfn.continuousOn
  have h₁ : p₀.1 ∈ Set.Icc (0 : ℝ) 1 := hp₀mem.1.1
  have h₂ : p₀.2 ∈ Set.Icc (0 : ℝ) 1 := hp₀mem.1.2
  have hband : δ ≤ |p₀.2 - p₀.1| := hp₀mem.2
  have hpne : p₀.2 ≠ p₀.1 := by
    intro heq
    rw [heq, sub_self, abs_zero] at hband
    exact absurd hband (not_le.mpr hδ)
  have hγne : γ p₀.2 ≠ γ p₀.1 := fun he => hpne (hinj p₀.2 h₂ p₀.1 h₁ he)
  refine ⟨‖γ p₀.2 - γ p₀.1‖, norm_pos_iff.mpr (sub_ne_zero.mpr hγne), ?_⟩
  intro s hs t ht hge
  have hmem : (s, t) ∈ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩
      {p : ℝ × ℝ | δ ≤ |p.2 - p.1|} := by
    constructor
    · constructor
      · exact hs
      · exact ht
    · show δ ≤ |t - s|
      exact hge
  exact hmin hmem

/-- Rescaled far-set minimum for the closed-curve parameter square `[0, 2π]²`: the
compactness argument on `[0, 1]` transfers by linear reparametrization. -/
theorem exists_pos_le_norm_sub_of_injective_on_two_pi (γ : ℝ → (Fin 3 → ℝ))
    (hγ : Continuous γ)
    (hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      γ s = γ t → s = t)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 2 * π) :
    ∃ m, 0 < m ∧ ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      δ ≤ |t - s| → m ≤ ‖γ t - γ s‖ := by
  have hπ : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hsc : Continuous fun u : ℝ => γ (2 * π * u) :=
    hγ.comp (continuous_const.mul continuous_id)
  have hinj' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ (2 * π * s) = γ (2 * π * t) → s = t := by
    intro s hs t ht heq
    have hst : 2 * π * s = 2 * π * t :=
      hinj _ (Set.mem_Icc.2 ⟨by nlinarith [hs.1, hπ], by nlinarith [hs.2, hπ]⟩)
        _ (Set.mem_Icc.2 ⟨by nlinarith [ht.1, hπ], by nlinarith [ht.2, hπ]⟩) heq
    exact mul_left_cancel₀ hπ.ne' hst
  obtain ⟨m, hm0, hlow⟩ :=
    exists_pos_le_norm_sub_of_injective_on (fun u => γ (2 * π * u)) hsc hinj'
      (div_pos hδ hπ) (by rw [div_le_iff₀ hπ, one_mul]; exact hδle)
  refine ⟨m, hm0, fun s hs t ht hge => ?_⟩
  have hs' : s / (2 * π) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.2 ⟨div_nonneg hs.1 hπ.le, (div_le_one hπ).2 hs.2⟩
  have ht' : t / (2 * π) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.2 ⟨div_nonneg ht.1 hπ.le, (div_le_one hπ).2 ht.2⟩
  have hge' : δ / (2 * π) ≤ |t / (2 * π) - s / (2 * π)| := by
    rw [div_sub_div_same, abs_div, abs_of_pos hπ, div_le_div_iff₀ hπ hπ]
    exact mul_le_mul_of_nonneg_right hge hπ.le
  have hres := hlow (s / (2 * π)) hs' (t / (2 * π)) ht' hge'
  rw [show 2 * π * (s / (2 * π)) = s from by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hπ.ne'],
    show 2 * π * (t / (2 * π)) = t from by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hπ.ne']] at hres
  exact hres

/-! ### Integrability of the self Gauss kernel -/

/-- Uniform boundedness on the finite parameter square implies integrability
of the self Gauss kernel. Its measurability includes the points where the chord
vanishes, because division by zero is defined in the real field. -/
theorem writheKernel_integrable_of_uniform_bound (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ) (C : ℝ)
    (hbound : ∀ p : ℝ × ℝ, p ∈ gaussDomain → |writheKernel γ p.1 p.2| ≤ C) :
    Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure := by
  have hmeas : Measurable fun p : ℝ × ℝ => writheKernel γ p.1 p.2 := by
    have hd : Continuous (deriv γ) := ContDiff.continuous_deriv hγ (by norm_num)
    have hc1 : Continuous fun p : ℝ × ℝ => deriv γ p.1 := hd.comp continuous_fst
    have hc2 : Continuous fun p : ℝ × ℝ => deriv γ p.2 := hd.comp continuous_snd
    have hg1 : Continuous fun p : ℝ × ℝ => γ p.1 := hγ.continuous.comp continuous_fst
    have hg2 : Continuous fun p : ℝ × ℝ => γ p.2 := hγ.continuous.comp continuous_snd
    have hsub : Continuous fun p : ℝ × ℝ => γ p.1 - γ p.2 := hg1.sub hg2
    have hap : ∀ (F : ℝ × ℝ → (Fin 3 → ℝ)) (i : Fin 3),
        Continuous F → Continuous fun p => F p i := fun F i hF =>
          (continuous_apply i).comp hF
    have hcA : Continuous fun p : ℝ × ℝ => cross3 (deriv γ p.1) (deriv γ p.2) 0 := by
      show Continuous fun p : ℝ × ℝ =>
        deriv γ p.1 1 * deriv γ p.2 2 - deriv γ p.1 2 * deriv γ p.2 1
      exact ((hap _ 1 hc1).mul (hap _ 2 hc2)).sub ((hap _ 2 hc1).mul (hap _ 1 hc2))
    have hcB : Continuous fun p : ℝ × ℝ => cross3 (deriv γ p.1) (deriv γ p.2) 1 := by
      show Continuous fun p : ℝ × ℝ =>
        deriv γ p.1 2 * deriv γ p.2 0 - deriv γ p.1 0 * deriv γ p.2 2
      exact ((hap _ 2 hc1).mul (hap _ 0 hc2)).sub ((hap _ 0 hc1).mul (hap _ 2 hc2))
    have hcC : Continuous fun p : ℝ × ℝ => cross3 (deriv γ p.1) (deriv γ p.2) 2 := by
      show Continuous fun p : ℝ × ℝ =>
        deriv γ p.1 0 * deriv γ p.2 1 - deriv γ p.1 1 * deriv γ p.2 0
      exact ((hap _ 0 hc1).mul (hap _ 1 hc2)).sub ((hap _ 1 hc1).mul (hap _ 0 hc2))
    have hnumc : Continuous fun p : ℝ × ℝ =>
        dot3 (cross3 (deriv γ p.1) (deriv γ p.2)) (γ p.1 - γ p.2) := by
      show Continuous fun p : ℝ × ℝ =>
        cross3 (deriv γ p.1) (deriv γ p.2) 0 * (γ p.1 - γ p.2) 0
          + cross3 (deriv γ p.1) (deriv γ p.2) 1 * (γ p.1 - γ p.2) 1
          + cross3 (deriv γ p.1) (deriv γ p.2) 2 * (γ p.1 - γ p.2) 2
      have h1 : Continuous fun p : ℝ × ℝ =>
        cross3 (deriv γ p.1) (deriv γ p.2) 0 * (γ p.1 - γ p.2) 0 :=
        hcA.mul (hap _ 0 hsub)
      have h2 : Continuous fun p : ℝ × ℝ =>
        cross3 (deriv γ p.1) (deriv γ p.2) 1 * (γ p.1 - γ p.2) 1 :=
        hcB.mul (hap _ 1 hsub)
      have h3 : Continuous fun p : ℝ × ℝ =>
        cross3 (deriv γ p.1) (deriv γ p.2) 2 * (γ p.1 - γ p.2) 2 :=
        hcC.mul (hap _ 2 hsub)
      exact (h1.add h2).add h3
    have hdenc : Continuous fun p : ℝ × ℝ => 4 * π * euclideanLength (γ p.1 - γ p.2) ^ 3 :=
      continuous_const.mul ((continuous_euclideanLength.comp hsub).pow 3)
    have hrew : (fun p : ℝ × ℝ => writheKernel γ p.1 p.2)
        = fun p : ℝ × ℝ => (dot3 (cross3 (deriv γ p.1) (deriv γ p.2)) (γ p.1 - γ p.2))
          * ((4 * π * euclideanLength (γ p.1 - γ p.2) ^ 3)⁻¹) := by
      funext p
      simp only [writheKernel, gaussKernel, div_eq_mul_inv]
    rw [hrew]
    exact hnumc.measurable.mul (hdenc.measurable.inv)
  have hfin : gaussMeasure Set.univ < ∞ := by
    have heq : gaussMeasure Set.univ
        = volume.restrict (Set.Icc (0 : ℝ) (2 * π)) Set.univ
          * volume.restrict (Set.Icc (0 : ℝ) (2 * π)) Set.univ := by
      rw [gaussMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
    rw [heq, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
      sub_zero]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hae : ∀ᵐ p ∂gaussMeasure, p ∈ gaussDomain := by
    have heqm : gaussMeasure
        = (volume.prod (volume : Measure ℝ)).restrict
          (Set.Icc (0 : ℝ) (2 * π) ×ˢ Set.Icc (0 : ℝ) (2 * π)) := by
      rw [gaussMeasure, Measure.prod_restrict]
    rw [heqm]
    exact (ae_restrict_iff' (MeasurableSet.prod measurableSet_Icc measurableSet_Icc)).2
      (Filter.Eventually.of_forall fun p hp => hp)
  calc (∫⁻ p, ENNReal.ofReal ‖writheKernel γ p.1 p.2‖ ∂gaussMeasure)
      ≤ ∫⁻ _ : ℝ × ℝ, ENNReal.ofReal C ∂gaussMeasure := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with p hp
        exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hbound p hp)
    _ = ENNReal.ofReal C * gaussMeasure Set.univ := by rw [lintegral_const]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The writhe kernel of a regular simple `C²` curve is integrable on the parameter
square: the near-diagonal boundedness and the far-field estimate, combined with the
positive far-set chord minimum, give a uniform bound on the square, which has finite
measure. This discharges the integrability hypothesis of the band-shrink limit. -/
theorem writheKernel_integrable_of_regular (γ : ℝ → (Fin 3 → ℝ)) (hγ : ContDiff ℝ 2 γ)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    (hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      γ s = γ t → s = t) :
    Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure := by
  have hπ : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (deriv (deriv γ) 0)).trans (hM 0)
  have hB0 : (0 : ℝ) < B := by
    have h1 := abs_dot3_le (deriv γ 0) (deriv γ 0)
    have h2 := hτ 0
    have hnn : (0 : ℝ) ≤ dot3 (deriv γ 0) (deriv γ 0) := by
      have hsum : dot3 (deriv γ 0) (deriv γ 0)
          = ∑ i : Fin 3, (deriv γ 0) i * (deriv γ 0) i := by
        simp only [dot3, Fin.sum_univ_three]
      rw [hsum]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith [h1, h2, hnn, hτ0, hB 0, abs_of_nonneg hnn, norm_nonneg (deriv γ 0)]
  have hδpos : (0 : ℝ) < min (τ ^ 2 / (6 * (M + 1) * B)) (2 * π) :=
    lt_min (div_pos (by nlinarith [hτ0]) (by nlinarith [hB0, hM0])) hπ
  obtain ⟨m, hm0, hlow⟩ := exists_pos_le_norm_sub_of_injective_on_two_pi γ hγ.continuous hinj
    hδpos (min_le_right _ _)
  have hbound : ∀ p : ℝ × ℝ, p ∈ gaussDomain →
      |writheKernel γ p.1 p.2|
        ≤ max (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) (3 * B ^ 2 / (2 * π * m ^ 2)) := by
    intro p hp
    have h1 : p.1 ∈ Set.Icc (0 : ℝ) (2 * π) := hp.1
    have h2 : p.2 ∈ Set.Icc (0 : ℝ) (2 * π) := hp.2
    rcases le_or_gt (3 * M * B * |p.2 - p.1|) (τ ^ 2 / 2) with hsmall | hbig
    · exact le_trans (abs_writheKernel_le_near γ hγ hτ0 hτ hB hM p.1 p.2 hsmall)
        (le_max_left _ _)
    · have hMpos : (0 : ℝ) < M := by
        rcases lt_or_ge 0 M with h | h
        · exact h
        · exfalso
          have hprod : (0 : ℝ) ≤ B * |p.2 - p.1| :=
            mul_nonneg hB0.le (abs_nonneg _)
          have hle : 3 * M * B * |p.2 - p.1| ≤ 0 := by nlinarith [h, hprod]
          nlinarith [hle, hbig, hτ0]
      have hge : min (τ ^ 2 / (6 * (M + 1) * B)) (2 * π) ≤ |p.2 - p.1| := by
        refine le_trans (min_le_left _ _) ?_
        have hstep1 : τ ^ 2 / (6 * (M + 1) * B) ≤ τ ^ 2 / (6 * M * B) := by
          rw [div_le_div_iff₀ (by nlinarith [hB0, hM0])
            (by nlinarith [hB0, hMpos])]
          nlinarith [hM0, hτ0, hB0]
        refine le_trans hstep1 ?_
        rw [div_le_iff₀ (by nlinarith [hB0, hMpos])]
        nlinarith [hbig]
      have hpne : p.1 ≠ p.2 := by
        intro heq
        rw [heq, sub_self, abs_zero] at hge
        exact absurd hge (not_le.mpr hδpos)
      have hγne : γ p.1 ≠ γ p.2 := fun he => hpne (hinj p.1 h1 p.2 h2 he)
      have hlow' : m ≤ ‖γ p.1 - γ p.2‖ := by
        rw [norm_sub_rev]
        exact hlow p.1 h1 p.2 h2 hge
      have hdenm : 2 * π * m ^ 2 ≤ 2 * π * ‖γ p.1 - γ p.2‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0.le hlow' 2)
          (mul_nonneg (by norm_num) Real.pi_pos.le)
      have hB2 : (0 : ℝ) < B ^ 2 := pow_pos hB0 2
      have hm2 : (0 : ℝ) < m ^ 2 := pow_pos hm0 2
      calc |writheKernel γ p.1 p.2|
          ≤ 3 * B ^ 2 / (2 * π * ‖γ p.1 - γ p.2‖ ^ 2) :=
              abs_writheKernel_le_far γ hB p.1 p.2 hγne
        _ ≤ 3 * B ^ 2 / (2 * π * m ^ 2) := by
            rw [div_le_div_iff₀ (by nlinarith [hB2]) (by nlinarith [hπ, hm2])]
            nlinarith [hdenm, hB2]
        _ ≤ max (324 * B ^ 4 * M ^ 2 / (π * τ ^ 6)) (3 * B ^ 2 / (2 * π * m ^ 2)) :=
            le_max_right _ _
  exact writheKernel_integrable_of_uniform_bound γ hγ _ hbound

/-- For a regular simple `C²` curve the band-shrink limit is unconditional: the banded
writhe converges, as the band width tends to `0⁺`, to the full self Gauss integral
`gaussLinking γ γ`. The integrability hypothesis of the dominated-convergence argument
is discharged by `writheKernel_integrable_of_regular`. -/
theorem tendsto_writheBand_nhds_selfKernel_of_regular (γ : ℝ → (Fin 3 → ℝ))
    (hγ : ContDiff ℝ 2 γ)
    {τ B M : ℝ} (hτ0 : 0 < τ) (hτ : ∀ u, τ ^ 2 ≤ dot3 (deriv γ u) (deriv γ u))
    (hB : ∀ u, ‖deriv γ u‖ ≤ B) (hM : ∀ u, ‖deriv (deriv γ) u‖ ≤ M)
    (hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      γ s = γ t → s = t) :
    Tendsto (fun δ => writheBand γ δ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussLinking γ γ)) := by
  have hint := writheKernel_integrable_of_regular γ hγ hτ0 hτ hB hM hinj
  have hlim := tendsto_writheBand_nhds_selfKernel γ hint
  rwa [show (∫ p, writheKernel γ p.1 p.2 ∂gaussMeasure) = gaussLinking γ γ from rfl] at hlim

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
