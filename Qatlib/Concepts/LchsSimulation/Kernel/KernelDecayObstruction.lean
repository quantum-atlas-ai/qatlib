/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Obstruction to exponential boundary decay

A lower-half-plane Phragmen-Lindelof estimate controls holomorphic functions with sublinear
exponential growth. The theorem `kernel_decay_obstruction_of_exponential_bound` uses it to show
that a bounded analytic kernel with exponential real-axis decay vanishes on the closed lower
half-plane. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `phragmen_lindelof_lower_half_plane_power`: A function holomorphic on the open lower
  half-plane and continuous on its closure, with the stated sublinear exponential growth and
  real-axis norm bound `C`, has norm at most `C` throughout the closed half-plane.
* `kernel_decay_obstruction_of_exponential_bound`: A function analytic on the open lower
  half-plane, continuous and bounded on its closure, and exponentially decaying on the real axis
  vanishes on the closed lower half-plane.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Concepts.LchsSimulation.Kernel

open Filter Set Asymptotics Complex Bornology
open scoped Topology
set_option warningAsError false

/-- For `ρ < 1` and positive `ε`, the bound `B * x^ρ ≤ ε * x / 2` holds for all sufficiently
large real `x`. -/
private theorem sublinear_power_small (ρ B ε : ℝ) (hρ : ρ < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, B * x ^ ρ ≤ ε * x / 2 := by
  have ht : Tendsto (fun x : ℝ => B * x ^ (-(1 - ρ))) atTop (𝓝 0) := by
    simpa using! (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - ρ)).const_mul B
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2)),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : B * x ^ ρ = (B * x ^ (-(1 - ρ))) * x := by
    have hr : x ^ (-(1 - ρ)) * x = x ^ ρ := by
      calc
        _ = x ^ (-(1 - ρ)) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ (-(1 - ρ) + 1) := (Real.rpow_add hx0 _ _).symm
        _ = _ := by congr 1; ring
    rw [mul_assoc, hr]
  rw [he]
  nlinarith

/-- A function holomorphic on the open lower half-plane and continuous on its closure, with the
stated sublinear exponential growth and real-axis norm bound `C`, has norm at most `C`
throughout the closed half-plane. -/
theorem phragmen_lindelof_lower_half_plane_power :
    ∀ (g : ℂ → ℂ) (ρ γ C : ℝ),
      0 < ρ → ρ < γ → γ < 1 → 0 ≤ C →
      DifferentiableOn ℂ g {z : ℂ | z.im < 0} →
      ContinuousOn g {z : ℂ | z.im ≤ 0} →
      (∀ k : ℝ, ‖g (k : ℂ)‖ ≤ C) →
      (∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z : ℂ, z.im ≤ 0 →
        ‖g z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) →
      ∀ z : ℂ, z.im ≤ 0 → ‖g z‖ ≤ C := by
  intro g ρ γ C _ hργ hγ _ hd hc hreal hg z hz
  obtain ⟨A, B, hA, _, hbound⟩ := hg
  have hρ : ρ < 1 := hργ.trans hγ
  have hclosed : closure {z : ℂ | z.im < 0} ⊆ {z : ℂ | z.im ≤ 0} :=
    closure_minimal (by intro w hw; change w.im < 0 at hw; exact hw.le)
      (isClosed_le Complex.continuous_im continuous_const)
  have hgd : DiffContOnCl ℂ g {z : ℂ | z.im < 0} := ⟨hd, hc.mono hclosed⟩
  let G := fun (ε : ℝ) (w : ℂ) => Complex.exp (-(ε : ℂ) * w) * g (-Complex.I * w)
  have hnorm (ε : ℝ) (w : ℂ) : ‖G ε w‖ = Real.exp (-ε * w.re) * ‖g (-Complex.I * w)‖ := by
    simp [G, Complex.norm_exp, Complex.mul_re]
  have hrotate (w : ℂ) : ‖-Complex.I * w‖ = ‖w‖ := by simp
  have hdim (w : ℂ) : (-Complex.I * w).im = -w.re := by simp [Complex.mul_im]
  have hGe (ε : ℝ) (hε : 0 < ε) : ‖G ε (Complex.I * z)‖ ≤ C := by
    apply PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real
    · exact ((differentiable_id.const_mul (-(ε : ℂ))).cexp.diffContOnCl).smul
        (hgd.comp (differentiable_id.const_mul (-Complex.I)).diffContOnCl
          (fun w hw => by change (-Complex.I * w).im < 0; rw [hdim]; exact neg_neg_of_pos hw))
    · refine ⟨ρ, by linarith, B, IsBigO.of_bound A ?_⟩
      apply eventually_inf_principal.mpr
      exact Eventually.of_forall (fun w hw => by
        change 0 < w.re at hw
        rw [hnorm, Real.norm_of_nonneg (Real.exp_pos _).le]
        have hgw := hbound (-Complex.I * w) (by rw [hdim]; linarith)
        rw [hrotate] at hgw
        exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))).trans hgw)
    · have ht : Tendsto (fun x : ℝ => A * Real.exp (-ε * x / 2)) atTop (𝓝 0) := by
        have he := Real.tendsto_exp_atBot.comp
          ((tendsto_const_mul_atBot_of_neg (by linarith : -ε / 2 < 0)).mpr tendsto_id)
        simpa [div_mul_eq_mul_div] using! he.const_mul A
      apply squeeze_zero_norm' _ ht
      filter_upwards [sublinear_power_small ρ B ε hρ hε, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      rw [hnorm, Complex.ofReal_re]
      have hgw := hbound (-Complex.I * (x : ℂ)) (by rw [hdim]; simpa using! hx0.le)
      rw [hrotate, Complex.norm_real, Real.norm_of_nonneg hx0.le] at hgw
      calc
        _ ≤ Real.exp (-ε * x) * (A * Real.exp (B * x ^ ρ)) :=
          mul_le_mul_of_nonneg_left hgw (Real.exp_pos _).le
        _ = A * Real.exp (-ε * x + B * x ^ ρ) := by rw [Real.exp_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA
    · intro x
      rw [hnorm]
      have hr : -Complex.I * ((x : ℂ) * Complex.I) = (x : ℂ) := by
        calc
          _ = -(Complex.I * Complex.I) * (x : ℂ) := by ring
          _ = _ := by rw [Complex.I_mul_I]; simp
      simpa [hr] using! hreal x
    · simpa [Complex.mul_re] using! neg_nonneg.mpr hz
  have ht : Tendsto (fun ε : ℝ => ‖G ε (Complex.I * z)‖) (𝓝[>] 0) (𝓝 ‖g z‖) := by
    have hcont : Continuous (fun ε : ℝ => ‖G ε (Complex.I * z)‖) := by
      dsimp [G]
      fun_prop
    have he : -Complex.I * (Complex.I * z) = z := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]; simp
    simpa only [G, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero,
      one_mul, he] using! (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hGe ε hε

/-- For positive `ρ`, the real part of `(Complex.I * k)^ρ` is `|k|^ρ * Real.cos (ρ * Real.pi /
2)`. -/
private theorem imaginary_cpow_real_part (k ρ : ℝ) (hρ : 0 < ρ) :
    ((Complex.I * (k : ℂ)) ^ (ρ : ℂ)).re =
      |k| ^ ρ * Real.cos (ρ * Real.pi / 2) := by
  rw [Complex.cpow_ofReal_re]
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have he : Complex.I * (k : ℂ) = (-k : ℝ) * (-Complex.I) := by push_cast; ring
    rw [he, Complex.arg_real_mul _ (neg_pos.mpr hk), Complex.arg_neg_I]
    rw [neg_mul, Real.cos_neg]
    congr 2
    ring
  · simp [hk, Real.zero_rpow hρ.ne']
  · rw [mul_comm Complex.I, Complex.arg_real_mul _ hk, Complex.arg_I]
    congr 2
    ring

/-- A function analytic on the open lower half-plane, continuous and bounded on its closure, and
exponentially decaying on the real axis vanishes on the closed lower half-plane. -/
theorem kernel_decay_obstruction_of_exponential_bound (f : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ f {z : ℂ | z.im < 0})
    (hc : ContinuousOn f {z : ℂ | z.im ≤ 0})
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ≤ 0 → ‖f z‖ ≤ C)
    (he : ∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧
      ∀ k : ℝ, ‖f (k : ℂ)‖ ≤ c₀ * Real.exp (-c * |k|)) :
    ∀ z : ℂ, z.im ≤ 0 → f z = 0 := by
  obtain ⟨C, hC, hbounded⟩ := hb
  obtain ⟨c, c₀, hcp, hc₀, hdecay⟩ := he
  let D := c₀ * Real.exp c
  let G := fun (n : ℕ) (ρ : ℝ) (z : ℂ) =>
    Complex.exp ((n : ℂ) * (Complex.I * z) ^ (ρ : ℂ)) * f z
  have hnorm (n : ℕ) (ρ : ℝ) (z : ℂ) :
      ‖G n ρ z‖ = Real.exp ((n : ℝ) * ((Complex.I * z) ^ (ρ : ℂ)).re) * ‖f z‖ := by
    simp [G, Complex.norm_exp, Complex.mul_re]
  have hGbound (n : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
      (hcoef : (n : ℝ) * Real.cos (ρ * Real.pi / 2) ≤ c) :
      ∀ z : ℂ, z.im ≤ 0 → ‖G n ρ z‖ ≤ D := by
    have hcos := highKernel_cos_pos ρ hρ0 hρ1
    have hgd : DifferentiableOn ℂ (G n ρ) {z : ℂ | z.im < 0} := by
      intro z hz
      change z.im < 0 at hz
      have hpow : AnalyticAt ℂ (fun w : ℂ => (Complex.I * w) ^ (ρ : ℂ)) z :=
        (analyticAt_const.mul analyticAt_id).cpow analyticAt_const
          (Or.inl (by simpa [Complex.mul_re] using! neg_pos.mpr hz))
      exact ((analyticAt_const.mul hpow).cexp.differentiableAt.differentiableWithinAt).mul
        (ha z hz).differentiableAt.differentiableWithinAt
    have hgc : ContinuousOn (G n ρ) {z : ℂ | z.im ≤ 0} := by
      intro z hz
      change z.im ≤ 0 at hz
      have hpow : ContinuousAt (fun w : ℂ => (Complex.I * w) ^ (ρ : ℂ)) z :=
        (Complex.continuousAt_cpow_const_of_re_pos (z := Complex.I * z) (w := (ρ : ℂ))
          (Or.inl (by simpa [Complex.mul_re] using! neg_nonneg.mpr hz))
          (by simpa using! hρ0)).comp (continuous_const.mul continuous_id).continuousAt
      exact (hpow.const_mul (n : ℂ)).cexp.continuousWithinAt.mul (hc z hz)
    have hboundary (k : ℝ) : ‖G n ρ (k : ℂ)‖ ≤ D := by
      rw [hnorm, imaginary_cpow_real_part k ρ hρ0]
      have hkpow : |k| ^ ρ ≤ max 1 |k| := by
        by_cases hk : |k| ≤ 1
        · exact (Real.rpow_le_one (abs_nonneg k) hk hρ0.le).trans (le_max_left _ _)
        · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hk)) hρ1.le).trans_eq
            (by simp [Real.rpow_one, max_eq_right (le_of_lt (lt_of_not_ge hk))])
      have hex : (n : ℝ) * (|k| ^ ρ * Real.cos (ρ * Real.pi / 2)) - c * |k| ≤ c := by
        have hm := mul_le_mul_of_nonneg_left hkpow
          (mul_nonneg (Nat.cast_nonneg n) hcos.le)
        have hm2 := mul_le_mul_of_nonneg_right hcoef (le_trans zero_le_one (le_max_left 1 |k|))
        have hmax : max 1 |k| ≤ 1 + |k| := max_le (by linarith [abs_nonneg k]) (by linarith)
        have hm3 := mul_le_mul_of_nonneg_left hmax hcp.le
        nlinarith
      calc
        _ ≤ Real.exp ((n : ℝ) * (|k| ^ ρ * Real.cos (ρ * Real.pi / 2))) *
            (c₀ * Real.exp (-c * |k|)) := mul_le_mul_of_nonneg_left (hdecay k) (Real.exp_pos _).le
        _ = c₀ * Real.exp ((n : ℝ) * (|k| ^ ρ * Real.cos (ρ * Real.pi / 2)) - c * |k|) := by
          rw [sub_eq_add_neg, Real.exp_add]
          have he : Real.exp (-c * |k|) = Real.exp (-(c * |k|)) := by congr 1; ring
          rw [he]
          ring
        _ ≤ D := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hc₀.le
    have hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
        ∀ z : ℂ, z.im ≤ 0 → ‖G n ρ z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := by
      refine ⟨C, n, hC, Nat.cast_nonneg n, ?_⟩
      intro z hz
      rw [hnorm]
      have hpow := Complex.re_le_norm ((Complex.I * z) ^ (ρ : ℂ))
      rw [Complex.norm_cpow_real, norm_mul, Complex.norm_I, one_mul] at hpow
      have hh := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
      exact (mul_le_mul (Real.exp_le_exp.mpr hh) (hbounded z hz)
        (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
    exact phragmen_lindelof_lower_half_plane_power (G n ρ) ρ ((ρ + 1) / 2) D
      hρ0 (by linarith) (by linarith) (by dsimp [D]; positivity) hgd hgc hboundary hgrowth
  have hlinear (n : ℕ) (z : ℂ) (hz : z.im ≤ 0) :
      Real.exp ((n : ℝ) * (-z.im)) * ‖f z‖ ≤ D := by
    have htcos : Tendsto (fun ρ : ℝ => (n : ℝ) * Real.cos (ρ * Real.pi / 2)) (𝓝 1) (𝓝 0) := by
      have hcont : Continuous (fun ρ : ℝ => (n : ℝ) * Real.cos (ρ * Real.pi / 2)) := by fun_prop
      simpa using! hcont.tendsto (1 : ℝ)
    have hcoef : ∀ᶠ ρ : ℝ in 𝓝[<] 1, (n : ℝ) * Real.cos (ρ * Real.pi / 2) < c :=
      (htcos.eventually (gt_mem_nhds hcp)).filter_mono nhdsWithin_le_nhds
    have hpos0 : ∀ᶠ ρ : ℝ in 𝓝 1, 0 < ρ := Ioi_mem_nhds (by norm_num)
    have hpos : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ := hpos0.filter_mono nhdsWithin_le_nhds
    have hpcomplex : ContinuousAt (fun ρ : ℂ => (Complex.I * z) ^ ρ) 1 :=
      (Complex.continuousAt_cpow_of_re_pos (p := (Complex.I * z, (1 : ℂ)))
        (Or.inl (by simpa [Complex.mul_re] using! neg_nonneg.mpr hz)) (by norm_num)).comp
          (continuousAt_const.prodMk continuousAt_id)
    have hpow : ContinuousAt (fun ρ : ℝ => (Complex.I * z) ^ (ρ : ℂ)) 1 := by
      have hpcomplex' : ContinuousAt (fun ρ : ℂ => (Complex.I * z) ^ ρ) (Complex.ofReal (1 : ℝ)) := by
        simpa only [Complex.ofReal_one] using! hpcomplex
      exact hpcomplex'.comp (f := Complex.ofReal) Complex.continuous_ofReal.continuousAt
    have ht : Tendsto (fun ρ : ℝ => ‖G n ρ z‖) (𝓝[<] 1)
        (𝓝 (Real.exp ((n : ℝ) * (-z.im)) * ‖f z‖)) := by
      have hcont : ContinuousAt (fun ρ : ℝ => ‖G n ρ z‖) 1 :=
        ((hpow.const_mul (n : ℂ)).cexp.mul (continuousAt_const (y := f z))).norm
      simpa [G, Complex.norm_exp, Complex.mul_re] using! hcont.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, hpos, hcoef] with ρ hρ1 hρ0 hρc
    exact hGbound n ρ hρ0 hρ1 hρc.le z hz
  have hzero : ∀ z : ℂ, z.im < 0 → f z = 0 := by
    intro z hz
    by_contra hfz
    have hn : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
    have he : 1 < Real.exp (-z.im) := Real.one_lt_exp_iff.mpr (neg_pos.mpr hz)
    have ht := (tendsto_pow_atTop_atTop_of_one_lt he).atTop_mul_const hn
    obtain ⟨n, hngt⟩ := (ht.eventually (eventually_gt_atTop D)).exists
    have hle := hlinear n z hz.le
    rw [Real.exp_nat_mul] at hle
    exact (not_le_of_gt hngt) hle
  have hcl : ContinuousOn f (closure {z : ℂ | z.im < 0}) := by
    simpa only [Complex.closure_setOf_im_lt] using! hc
  simpa only [Complex.closure_setOf_im_lt] using!
    EqOn.of_subset_closure hzero hcl continuousOn_const subset_closure Subset.rfl

end Qatlib.Concepts.LchsSimulation.Kernel
