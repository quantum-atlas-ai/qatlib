/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults
open KernelStrip

theorem antitone_tail_on (f : ℝ → ℝ) (a : ℝ) (hf : AntitoneOn f (Ici a))
    (hn : ∀ x, 0 ≤ f x) (hi : Integrable f) :
    Summable (fun j : ℕ => f (a + (j + 1 : ℕ))) ∧
      (∑' j : ℕ, f (a + (j + 1 : ℕ))) ≤ ∫ x in Ioi a, f x := by
  have hb (m : ℕ) : (∑ j ∈ Finset.range m, f (a + (j + 1 : ℕ))) ≤
      ∫ x in Ioi a, f x := by
    have hpart : AntitoneOn f (Icc a (a + m)) :=
      hf.mono (fun _ hx => hx.1)
    apply hpart.sum_le_integral.trans
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg m))]
    apply setIntegral_mono_set hi.integrableOn
      (Filter.Eventually.of_forall fun x => hn x)
    exact Filter.Eventually.of_forall (fun x hx => hx.1)
  exact ⟨summable_of_sum_range_le (fun _ => hn _) hb,
    Real.tsum_le_of_sum_range_le (fun _ => hn _) hb⟩

theorem antitone_tail (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0))
    (hn : ∀ x, 0 ≤ f x) (hi : Integrable f) {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun j : ℕ => f (a + (j + 1 : ℕ))) ∧
      (∑' j : ℕ, f (a + (j + 1 : ℕ))) ≤ ∫ x in Ioi a, f x :=
  antitone_tail_on f a (hf.mono (fun _ hx => ha.trans hx)) hn hi

theorem real_norm (n : ℕ) (b c d x : ℝ) (hb : 0 < b) :
    ‖coefficient n b c d (x : ℂ)‖ =
      ((b + 1) ^ n / (2 * Real.pi) * Real.exp (d - 1 / (4 * c ^ 2))) *
        Real.exp (-x ^ 2 / (4 * c ^ 2)) /
        (Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n) := by
  have h1 : ‖1 - I * (x : ℂ)‖ = Real.sqrt (1 + x ^ 2) := by
    rw [show 1 - I * (x : ℂ) = (1 : ℝ) + (-x : ℝ) * I by push_cast; ring]
    simpa using! Complex.norm_add_mul_I 1 (-x)
  have h2 : ‖(b : ℂ) + I * (x : ℂ)‖ = Real.sqrt (b ^ 2 + x ^ 2) := by
    rw [mul_comm I]
    exact Complex.norm_add_mul_I b x
  rw [norm_coefficient n b c d hb (x : ℂ), h1, h2]
  simp only [ofReal_im, ofReal_re, zero_pow two_ne_zero, add_zero, mul_one,
    zero_add, neg_div, sub_eq_add_neg]

theorem real_norm_antitone (n : ℕ) (b c d : ℝ) (hb : 0 < b) :
    AntitoneOn (fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖) (Set.Ici 0) := by
  intro x hx y hy hxy
  change ‖coefficient n b c d (y : ℂ)‖ ≤ ‖coefficient n b c d (x : ℂ)‖
  rw [real_norm n b c d y hb, real_norm n b c d x hb]
  let C := (b + 1) ^ n / (2 * Real.pi) * Real.exp (d - 1 / (4 * c ^ 2))
  let D := fun x : ℝ => Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).mpr hxy
  have hD : D x ≤ D y :=
    mul_le_mul (Real.sqrt_le_sqrt (add_le_add (le_refl 1) hs))
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (add_le_add (le_refl (b ^ 2)) hs)) n)
      (pow_nonneg (Real.sqrt_nonneg _) _) (Real.sqrt_nonneg _)
  have hDx : 0 < D x := by dsimp [D]; positivity
  have he : Real.exp (-y ^ 2 / (4 * c ^ 2)) ≤ Real.exp (-x ^ 2 / (4 * c ^ 2)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hs) (by positivity))
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hC)
    (hDx.le.trans hD)).trans (div_le_div_of_nonneg_left (by positivity) hDx hD)

theorem real_norm_even (n : ℕ) (b c d x : ℝ) (hb : 0 < b) :
    ‖coefficient n b c d ((-x : ℝ) : ℂ)‖ = ‖coefficient n b c d (x : ℂ)‖ := by
  simp only [real_norm n b c d (-x) hb, real_norm n b c d x hb, neg_sq]

theorem real_norm_integrable (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    MeasureTheory.Integrable (fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖) := by
  have hf : Continuous (fun x : ℝ => coefficient n b c d (x : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((coefficient_analytic n b c d (ρ := 0) (by norm_num) (Or.inr hb) _
      (by simp)).continuousAt.comp (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ)) x))
  apply ((gaussian_integrable hc).const_mul (amplitude n b c d 0 0)).mono'
    hf.norm.aestronglyMeasurable
  filter_upwards [] with x
  have h := coefficient_growth_le n b c d hb (ρ := 0) (K := 0) (by norm_num)
    (Or.inr hb) (by norm_num) (z := (x : ℂ)) (by simp)
  simpa only [norm_norm, ofReal_im, ofReal_re, max_self, zero_mul, Real.exp_zero, mul_one] using! h

theorem scaled_antitone_tail (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0))
    (hn : ∀ x, 0 ≤ f x) (hi : Integrable f) (N : ℕ) {h : ℝ} (hh : 0 < h) :
    Summable (fun j : ℕ => f (h * ((N : ℝ) + (j + 1 : ℕ)))) ∧
      h * (∑' j : ℕ, f (h * ((N : ℝ) + (j + 1 : ℕ)))) ≤
        ∫ x in Ioi (h * N), f x := by
  have hg : AntitoneOn (fun x : ℝ => f (h * x)) (Ici 0) := by
    intro x hx y hy hxy
    exact hf (mul_nonneg hh.le hx) (mul_nonneg hh.le hy)
      (mul_le_mul_of_nonneg_left hxy hh.le)
  have ht := antitone_tail (fun x => f (h * x)) hg (fun x => hn _)
    (hi.comp_mul_left' hh.ne') (a := (N : ℝ)) (Nat.cast_nonneg N)
  refine ⟨ht.1, ?_⟩
  have hb := mul_le_mul_of_nonneg_left ht.2 hh.le
  rw [integral_comp_mul_left_Ioi f N hh, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hh.ne', one_mul] at hb
  exact hb

def tailIndex (N : ℕ) : ℕ ⊕ ℕ → {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N}
  | Sum.inl j => ⟨(N : ℤ) + j + 1, by simp only [Finset.mem_Icc]; omega⟩
  | Sum.inr j => ⟨-((N : ℤ) + j + 1), by simp only [Finset.mem_Icc]; omega⟩

theorem tailIndex_bijective (N : ℕ) : Function.Bijective (tailIndex N) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    cases x <;> cases y <;> simp only [tailIndex] at he
    all_goals (congr 1; omega)
  · intro q
    have hq := q.property
    simp only [Finset.mem_Icc] at hq
    by_cases hp : 0 < q.val
    · refine ⟨Sum.inl (q.val.toNat - N - 1), ?_⟩
      apply Subtype.ext
      simp only [tailIndex]
      omega
    · refine ⟨Sum.inr ((-q.val).toNat - N - 1), ?_⟩
      apply Subtype.ext
      simp only [tailIndex]
      omega

noncomputable def tailEquiv (N : ℕ) : (ℕ ⊕ ℕ) ≃
    {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N} :=
  Equiv.ofBijective (tailIndex N) (tailIndex_bijective N)

theorem summable_coefficient_norm (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun q : ℤ => ‖coefficient n b c d ((h * (q : ℝ) : ℝ) : ℂ)‖) := by
  let f := fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖
  have ht := (scaled_antitone_tail f (real_norm_antitone n b c d hb)
    (fun _ => norm_nonneg _) (real_norm_integrable n b c d hb hc) 0 hh).1
  have hp : Summable (fun j : ℕ => f (h * (j : ℝ))) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] using! ht
  have he : (fun j : ℕ => f (h * ((-((j : ℤ) + 1) : ℤ) : ℝ))) =
      (fun j : ℕ => f (h * ((j : ℝ) + 1))) := by
    funext j
    have hj : h * ((-((j : ℤ) + 1) : ℤ) : ℝ) = -(h * ((j : ℝ) + 1)) := by
      push_cast
      ring
    rw [hj]
    exact real_norm_even n b c d (h * ((j : ℝ) + 1)) hb
  have hm : Summable (fun j : ℕ => f (h * ((-((j : ℤ) + 1) : ℤ) : ℝ))) := by
    rw [he]
    simpa only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] using! ht
  exact Summable.of_nat_of_neg_add_one (by simpa only [Int.cast_natCast] using! hp) hm

theorem coefficient_tail_eq (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (N : ℕ) {h : ℝ} (hh : 0 < h) :
    (∑' q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N},
      ‖coefficient n b c d ((h * (q.val : ℝ) : ℝ) : ℂ)‖) =
      2 * ∑' j : ℕ, ‖coefficient n b c d
        ((h * ((N : ℝ) + (j + 1 : ℕ)) : ℝ) : ℂ)‖ := by
  let g := fun q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N} =>
    ‖coefficient n b c d ((h * (q.val : ℝ) : ℝ) : ℂ)‖
  have hg : Summable g := (summable_coefficient_norm n b c d hb hc hh).subtype _
  have hs := (tailEquiv N).summable_iff.mpr hg
  have hp : (fun j : ℕ => g (tailEquiv N (Sum.inl j))) =
      (fun j : ℕ => ‖coefficient n b c d ((h * ((N : ℝ) + (j + 1 : ℕ)) : ℝ) : ℂ)‖) := by
    funext j
    dsimp [g, tailEquiv, tailIndex]
    push_cast
    ring_nf
  have hm : (fun j : ℕ => g (tailEquiv N (Sum.inr j))) =
      (fun j : ℕ => ‖coefficient n b c d ((h * ((N : ℝ) + (j + 1 : ℕ)) : ℝ) : ℂ)‖) := by
    funext j
    dsimp [g, tailEquiv, tailIndex]
    push_cast
    convert! real_norm_even n b c d (h * ((N : ℝ) + ((j : ℝ) + 1))) hb using 1
    all_goals (congr 2; push_cast; ring)
  calc
    _ = ∑' j : ℕ ⊕ ℕ, g (tailEquiv N j) := ((tailEquiv N).tsum_eq g).symm
    _ = (∑' j : ℕ, g (tailEquiv N (Sum.inl j))) +
        ∑' j : ℕ, g (tailEquiv N (Sum.inr j)) :=
      (hs.comp_injective Sum.inl_injective).tsum_sum (hs.comp_injective Sum.inr_injective)
    _ = _ := by rw [hp, hm]; ring

def latticeTail (n : ℕ) (b c d h : ℝ) (N : ℕ) : ℝ :=
  h * ∑' q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N},
    ‖coefficient n b c d ((h * (q.val : ℝ) : ℝ) : ℂ)‖

def continuousTail (n : ℕ) (b c d R : ℝ) : ℝ :=
  2 * ∫ x in Ioi R, ‖coefficient n b c d (x : ℂ)‖

theorem latticeTail_le (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (N : ℕ) {h : ℝ} (hh : 0 < h) :
    latticeTail n b c d h N ≤ continuousTail n b c d (h * N) := by
  unfold latticeTail continuousTail
  rw [coefficient_tail_eq n b c d hb hc N hh]
  have ht := (scaled_antitone_tail _ (real_norm_antitone n b c d hb)
    (fun _ => norm_nonneg _) (real_norm_integrable n b c d hb hc) N hh).2
  nlinarith

theorem continuousTail_antitone (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Antitone (continuousTail n b c d) := by
  intro R S hRS
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply setIntegral_mono_set (real_norm_integrable n b c d hb hc).integrableOn
    (Eventually.of_forall fun _ => norm_nonneg _)
  exact Eventually.of_forall fun _ hx => lt_of_le_of_lt hRS hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

theorem norm_real_integrand_le (n : ℕ) (b c d : ℝ)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    ‖integrand n b c d T H L (x : ℂ)‖ ≤ ‖coefficient n b c d (x : ℂ)‖ := by
  rw [integrand, norm_smul]
  have hv : ‖propagator H L T (x : ℂ)‖ ≤ 1 := by
    simpa only [ofReal_im, max_self, mul_zero, zero_mul, Real.exp_zero] using!
      norm_propagator_le H L hH hL hT (x : ℂ)
  simpa only [mul_one] using! mul_le_mul_of_nonneg_left hv (norm_nonneg _)

theorem summable_integrand_norm (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) :
    Summable (fun q : ℤ => ‖integrand n b c d T H L ((h * (q : ℝ) : ℝ) : ℂ)‖) :=
  (summable_coefficient_norm n b c d hb hc hh).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun _ => norm_real_integrand_le n b c d H L hH hL hT _)

def finiteIdeal (n : ℕ) (b c d T h : ℝ) (H L : Matrix ι ι ℂ) (N : ℕ) : Matrix ι ι ℂ :=
  h • ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
    integrand n b c d T H L ((h * (q : ℝ) : ℝ) : ℂ)

theorem mesh_sub_finite_le (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (N : ℕ) :
    ‖h • (∑' q : ℤ, integrand n b c d T H L ((h * (q : ℝ) : ℝ) : ℂ)) -
      finiteIdeal n b c d T h H L N‖ ≤ latticeTail n b c d h N := by
  let F := fun q : ℤ => integrand n b c d T H L ((h * (q : ℝ) : ℝ) : ℂ)
  let s := Finset.Icc (-(N : ℤ)) N
  have hFn : Summable (fun q => ‖F q‖) := summable_integrand_norm n b c d hb hc H L hH hL hT hh
  have hF : Summable F := hFn.of_norm
  have he := hF.sum_add_tsum_subtype_compl s
  have hid : (∑' q, F q) - ∑ q ∈ s, F q = ∑' q : {q // q ∉ s}, F q := by
    exact sub_eq_iff_eq_add.mpr (he.symm.trans (add_comm _ _))
  change ‖h • (∑' q, F q) - h • (∑ q ∈ s, F q)‖ ≤ _
  rw [← smul_sub, hid, norm_smul, Real.norm_of_nonneg hh.le]
  apply mul_le_mul_of_nonneg_left _ hh.le
  apply (norm_tsum_le_tsum_norm (hFn.subtype _)).trans
  exact (hFn.subtype _).tsum_le_tsum
    (fun q => norm_real_integrand_le n b c d H L hH hL hT _)
    ((summable_coefficient_norm n b c d hb hc hh).subtype _)

theorem finite_error_le_latticeTail (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ h : ℝ} (hT : 0 ≤ T) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    (hbn : n = 0 ∨ ρ < b) (hh : 0 < h) (N : ℕ) :
    ‖(∫ x : ℝ, integrand n b c d T H L (x : ℂ)) - finiteIdeal n b c d T h H L N‖ ≤
      2 * mass n b c d ρ (T * ‖L‖) / (Real.exp (2 * Real.pi * ρ / h) - 1) +
        latticeTail n b c d h N := by
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (h • ∑' q : ℤ, integrand n b c d T H L ((h * (q : ℝ) : ℝ) : ℂ)) _).trans
    (_root_.add_le_add (integrand_mesh_error n b c d hb hc H L hH hL hT hρ₀ hρ hbn hh)
      (mesh_sub_finite_le n b c d hb hc H L hH hL hT hh N))

def cutoff (R h : ℝ) : ℕ := Nat.ceil (R / h)

def radius (R h : ℝ) : ℝ := h * cutoff R h

theorem node_count (R h : ℝ) :
    (Finset.Icc (-(cutoff R h : ℤ)) (cutoff R h)).card = 2 * cutoff R h + 1 := by
  rw [Int.card_Icc]
  omega

theorem le_radius (R : ℝ) {h : ℝ} (hh : 0 < h) : R ≤ radius R h := by
  have he := (div_le_iff₀ hh).mp (Nat.le_ceil (R / h))
  simpa only [radius, cutoff, mul_comm] using! he

theorem radius_lt_add {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h) : radius R h < R + h := by
  have he := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (div_nonneg hR hh.le)) hh
  have hid : h * (R / h + 1) = R + h := by field_simp
  simpa only [radius, cutoff, hid] using! he

theorem node_le_radius (R h : ℝ) (hh : 0 ≤ h) (q : ℤ)
    (hq : q ∈ Finset.Icc (-(cutoff R h : ℤ)) (cutoff R h)) :
    |h * (q : ℝ)| ≤ radius R h := by
  have hq' : |(q : ℝ)| ≤ (cutoff R h : ℝ) := by
    exact_mod_cast abs_le.mpr (Finset.mem_Icc.mp hq)
  simpa only [abs_mul, abs_of_nonneg hh, radius] using! mul_le_mul_of_nonneg_left hq' hh

theorem finiteIdeal_eq_weighted (n : ℕ) (b c d T h : ℝ) (H L : Matrix ι ι ℂ) (N : ℕ) :
    finiteIdeal n b c d T h H L N =
      ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
        ((h : ℂ) * coefficient n b c d ((h * (q : ℝ) : ℝ) : ℂ)) •
          propagator H L T ((h * (q : ℝ) : ℝ) : ℂ) := by
  rw [finiteIdeal, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ext i j
  simp only [integrand, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem finite_error_le_continuousTail (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ h : ℝ} (hT : 0 ≤ T) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    (hbn : n = 0 ∨ ρ < b) (hh : 0 < h) (R : ℝ) :
    ‖(∫ x : ℝ, integrand n b c d T H L (x : ℂ)) -
      finiteIdeal n b c d T h H L (cutoff R h)‖ ≤
      2 * mass n b c d ρ (T * ‖L‖) / (Real.exp (2 * Real.pi * ρ / h) - 1) +
        continuousTail n b c d R := by
  apply (finite_error_le_latticeTail n b c d hb hc H L hH hL hT hρ₀ hρ hbn hh _).trans
  exact _root_.add_le_add le_rfl ((latticeTail_le n b c d hb hc _ hh).trans
    (continuousTail_antitone n b c d hb hc (le_radius R hh)))

theorem rounded_tail_bounds (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (R : ℝ) {h : ℝ} (hh : 0 < h) :
    latticeTail n b c d h (cutoff R h) ≤ continuousTail n b c d (radius R h) ∧
      continuousTail n b c d (radius R h) ≤ continuousTail n b c d R :=
  ⟨latticeTail_le n b c d hb hc _ hh,
    continuousTail_antitone n b c d hb hc (le_radius R hh)⟩

omit [Fintype ι] [DecidableEq ι] in

theorem continuousTail_eq_integral (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {R : ℝ} (hR : 0 ≤ R) :
    continuousTail n b c d R =
      ∫ x in {x : ℝ | R < |x|}, ‖coefficient n b c d (x : ℂ)‖ := by
  let f := fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖
  have hi : Integrable f := real_norm_integrable n b c d hb hc
  have hf (x : ℝ) : f (-x) = f x := real_norm_even n b c d x hb
  have hs : {x : ℝ | R < |x|} = Iio (-R) ∪ Ioi R := by
    ext x
    simp only [lt_abs, mem_union, mem_Iio, mem_Ioi, mem_setOf_eq]
    constructor
    · rintro (hx | hx)
      · exact Or.inr hx
      · exact Or.inl (by linarith)
    · rintro (hx | hx)
      · exact Or.inr (by linarith)
      · exact Or.inl hx
  have hn : (∫ x in Iio (-R), f x) = ∫ x in Ioi R, f x := by
    calc
      _ = ∫ x : ℝ, (Iio (-R)).indicator f x := (integral_indicator measurableSet_Iio).symm
      _ = ∫ x : ℝ, (Iio (-R)).indicator f (-x) := (integral_neg_eq_self _ volume).symm
      _ = ∫ x : ℝ, (Ioi R).indicator f x := by
        congr 1
        funext x
        simp only [Set.indicator_apply, mem_Iio, mem_Ioi, neg_lt_neg_iff, hf]
      _ = _ := integral_indicator measurableSet_Ioi
  have hd : Disjoint (Iio (-R)) (Ioi R) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change x < -R at hx
    change R < x at hy
    linarith
  change 2 * (∫ x in Ioi R, f x) = ∫ x in {x : ℝ | R < |x|}, f x
  rw [hs, setIntegral_union hd measurableSet_Ioi hi.integrableOn hi.integrableOn, hn]
  ring

def operatorTruncationError (n : ℕ) (b c d T : ℝ) (H L : Matrix ι ι ℂ) (R : ℝ) : ℝ :=
  ‖(∫ x : ℝ, integrand n b c d T H L (x : ℂ)) -
    ∫ x in Icc (-R) R, integrand n b c d T H L (x : ℂ)‖

theorem operatorTruncationError_eq_tail (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    operatorTruncationError n b c d T H L R =
      ‖∫ x in {x : ℝ | R < |x|}, integrand n b c d T H L (x : ℂ)‖ := by
  have hi : Integrable (fun x : ℝ => integrand n b c d T H L (x : ℂ)) := by
    simpa using! integrand_integrable n b c d hb hc H L hH hL hT
      (ρ := 0) (y := 0) (by norm_num) (Or.inr hb) (by simp)
  have hs : (Icc (-R) R)ᶜ = {x : ℝ | R < |x|} := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, ← abs_le, not_le]
  unfold operatorTruncationError
  rw [← setIntegral_compl measurableSet_Icc hi, hs]

theorem operatorTruncationError_le (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    operatorTruncationError n b c d T H L R ≤ continuousTail n b c d R := by
  rw [operatorTruncationError_eq_tail n b c d hb hc H L hH hL hT R,
    continuousTail_eq_integral n b c d hb hc hR]
  have hi : Integrable (fun x : ℝ => integrand n b c d T H L (x : ℂ)) := by
    simpa using! integrand_integrable n b c d hb hc H L hH hL hT
      (ρ := 0) (y := 0) (by norm_num) (Or.inr hb) (by simp)
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hi.integrableOn.norm (real_norm_integrable n b c d hb hc).integrableOn
  intro x
  exact norm_real_integrand_le n b c d H L hH hL hT x

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
