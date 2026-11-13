/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.Lemma12CoefficientMassStat
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule
import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialKernelModulus
import Qatlib.Concepts.LchsSimulation.Quadrature.CompositeGaussAlgebra

/-!
# Coefficient mass for composite Gauss LCHS

Positive polynomial-exact rules give a simple window-dependent bound on the composite
coefficient mass. The theorem `lemma12CoefficientMass` establishes the refined budget with a
kernel integral term and an explicit grid correction, while `node_omega_prod_integral` recovers
the nodal-product identity from exactness. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `lemma12_coefficient_mass_le_window`: For a positive polynomial-exact rule and `M ≥ 1`, the
  composite coefficient mass is at most `2 * K / highKernelC β` when `0 < β < 1`.
* `lemma12CoefficientMass`: The composite Gauss coefficient mass is bounded by the stated kernel
  integral budget plus `2 * K / (3 * highKernelC β) * (16 * h)^(2 * Q)`, as formalized for [An,
  Childs, and Lin, Lemma 12][AnChildsLin2026].

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.Kernel

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.Quadrature
open Set MeasureTheory

/-- For `0 < β < 1`, `K ≥ 1`, and `M ≥ 1`, the displayed kernel integral budget plus the
composite grid correction is strictly positive. -/
theorem lemma12_coefficient_budget_pos (β : ℝ) (K Q M : ℕ)
    (hβ : 0 < β) (hβ1 : β < 1) (hK : 1 ≤ K) (hM : 1 ≤ M) :
    0 < (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * (1 - β))) +
      (2 * (K : ℝ)) / (3 * highKernelC β) *
        (16 * ((2 * K : ℝ) / M)) ^ (2 * Q) := by
  have hgap : 0 < 1 - β := by linarith
  have hC := highKernelC_pos β
  positivity

/-- For a positive polynomial-exact rule and `M ≥ 1`, the composite coefficient mass is at most
`2 * K / highKernelC β` when `0 < β < 1`. -/
theorem lemma12_coefficient_mass_le_window (β : ℝ) (K Q M : ℕ)
    (node weight : Fin Q → ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hM : 1 ≤ M)
    (hw : ∀ q, 0 < weight q)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) :
    let h : ℝ := (2 * K : ℝ) / M
    let nodeAt : Fin M → Fin Q → ℝ :=
      fun m q => (-K : ℝ) + h * ((m : ℝ) + (node q + 1) / 2)
    (∑ m : Fin M, ∑ q : Fin Q,
        ‖(h / 2) * weight q * highKernelG β (nodeAt m q)‖) ≤
      2 * (K : ℝ) / highKernelC β := by
  (try dsimp only)
  let h : ℝ := (2 * K : ℝ) / M
  have hhn : 0 ≤ h := by dsimp [h]; positivity
  have hs := gauss_rule_weight_sum Q node weight hexact
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  calc
    _ ≤ ∑ _m : Fin M, ∑ q : Fin Q, (h / 2) * weight q * (1 / highKernelC β) := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro q _
      have hn : 0 ≤ h / 2 * weight q := mul_nonneg (by positivity) (hw q).le
      change ‖(h : ℂ) / 2 * (weight q : ℂ) *
        highKernelG β (-K + h * ((m : ℝ) + (node q + 1) / 2))‖ ≤ _
      simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
        abs_of_nonneg hhn, abs_of_pos (hw q)]
      exact mul_le_mul_of_nonneg_left (highKernelG_abs_le_invC β hβ hβ1 _) hn
    _ = 2 * (K : ℝ) / highKernelC β := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hs]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [h]
      field_simp

/-- For positive `Q`, a rule exact through degree `2 * Q - 1` has the stated factorial value for
the integral of the squared nodal product on `[-1, 1]`. -/
private theorem node_omega_prod_integral (Q : ℕ) (hQ : 1 ≤ Q) (node weight : Fin Q → ℝ)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) :
    (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) := by
  classical
  obtain ⟨node₁, weight₁, _, _, _, hexact₁, homega₁⟩ := gauss_legendre_rule_exists Q hQ
  set W : Polynomial ℝ := ∏ q, (Polynomial.X - Polynomial.C (node q)) with hWdef
  set W₁ : Polynomial ℝ := ∏ q, (Polynomial.X - Polynomial.C (node₁ q)) with hW₁def
  have hWmonic : W.Monic := by
    rw [hWdef]
    exact Polynomial.monic_prod_X_sub_C _ _
  have hW₁monic : W₁.Monic := by
    rw [hW₁def]
    exact Polynomial.monic_prod_X_sub_C _ _
  have hWne : W ≠ 0 := hWmonic.ne_zero
  have hW₁ne : W₁ ≠ 0 := hW₁monic.ne_zero
  have hWdeg : W.natDegree = Q := by
    rw [hWdef, Polynomial.natDegree_prod_of_monic _ _
      (fun q _ => Polynomial.monic_X_sub_C (node q))]
    simp
  have hW₁deg : W₁.natDegree = Q := by
    rw [hW₁def, Polynomial.natDegree_prod_of_monic _ _
      (fun q _ => Polynomial.monic_X_sub_C (node₁ q))]
    simp
  have hWnode : ∀ q : Fin Q, W.eval (node q) = 0 := by
    intro q
    rw [hWdef, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ q)
      (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
  have hW₁node : ∀ q : Fin Q, W₁.eval (node₁ q) = 0 := by
    intro q
    rw [hW₁def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ q)
      (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
  have hWorth : ∀ s : Polynomial ℝ, s.natDegree < Q →
      ∫ t in (-1 : ℝ)..1, (s * W).eval t = 0 := by
    intro s hs
    have hdeg : (s * W).natDegree ≤ 2 * Q - 1 := by
      have e := Polynomial.natDegree_mul_le (p := s) (q := W)
      rw [hWdeg] at e
      omega
    rw [hexact _ hdeg, Finset.sum_eq_zero]
    intro q _
    rw [Polynomial.eval_mul, hWnode q]
    ring
  have hW₁orth : ∀ s : Polynomial ℝ, s.natDegree < Q →
      ∫ t in (-1 : ℝ)..1, (s * W₁).eval t = 0 := by
    intro s hs
    have hdeg : (s * W₁).natDegree ≤ 2 * Q - 1 := by
      have e := Polynomial.natDegree_mul_le (p := s) (q := W₁)
      rw [hW₁deg] at e
      omega
    rw [hexact₁ _ hdeg, Finset.sum_eq_zero]
    intro q _
    rw [Polynomial.eval_mul, hW₁node q]
    ring
  have hrdeg : (W - W₁).natDegree < Q := by
    rcases eq_or_ne (W - W₁) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      omega
    · have hdeq : W.degree = W₁.degree := by
        rw [Polynomial.degree_eq_natDegree hWne, hWdeg,
          Polynomial.degree_eq_natDegree hW₁ne, hW₁deg]
      have hdlt := Polynomial.degree_sub_lt (p := W) (q := W₁) hdeq hWne
        (by rw [hWmonic.leadingCoeff, hW₁monic.leadingCoeff])
      rw [Polynomial.degree_eq_natDegree hWne, hWdeg] at hdlt
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdlt
  have hrint : ∫ t in (-1 : ℝ)..1, ((W - W₁) * W).eval t - ((W - W₁) * W₁).eval t = 0 := by
    rw [intervalIntegral.integral_sub (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _)
      (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _), hWorth (W - W₁) hrdeg,
      hW₁orth (W - W₁) hrdeg, sub_zero]
  have hWeq : W = W₁ := by
    by_contra hne
    have hrne : W - W₁ ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨y, hy⟩ := ((Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).diff
      ((W - W₁).roots.toFinset.finite_toSet)).nonempty
    have hyev : (W - W₁).eval y ≠ 0 := by
      intro h0
      exact absurd (Finset.mem_coe.mpr
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hrne).mpr h0))) hy.2
    have hcont_sq : Continuous (fun x : ℝ => (W - W₁).eval x ^ 2) := by
      have := Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval (W - W₁)
      fun_prop
    have hcontra := Qatlib.Concepts.LchsSimulation.Quadrature.integral_pos_of_nonneg_of_pos_at (by norm_num : (-1 : ℝ) < 1)
      hcont_sq (fun x _ => sq_nonneg _)
      ⟨hy.1.1.le, hy.1.2.le⟩ (sq_pos_of_ne_zero hyev)
    have hsqeq : ∫ x in (-1 : ℝ)..1, (W - W₁).eval x ^ 2
        = ∫ t in (-1 : ℝ)..1, ((W - W₁) * (W - W₁)).eval t :=
      intervalIntegral.integral_congr (fun t _ => by rw [sq, Polynomial.eval_mul])
    rw [hsqeq, intervalIntegral.integral_congr (fun t _ => by
        rw [show (W - W₁) * (W - W₁) = (W - W₁) * W - (W - W₁) * W₁ from by ring,
          Polynomial.eval_sub]),
      intervalIntegral.integral_sub (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _)
        (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _), hWorth (W - W₁) hrdeg,
      hW₁orth (W - W₁) hrdeg, sub_zero] at hcontra
    exact lt_irrefl 0 hcontra
  have hprod : ∀ t : ℝ, ∏ q : Fin Q, (t - node q) ^ 2 = W.eval t ^ 2 := by
    intro t
    rw [hWdef, Polynomial.eval_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun q _ => by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
  have hprod₁ : ∀ t : ℝ, ∏ q : Fin Q, (t - node₁ q) ^ 2 = W₁.eval t ^ 2 := by
    intro t
    rw [hW₁def, Polynomial.eval_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun q _ => by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
  calc (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2)
      = ∫ t in (-1 : ℝ)..1, W.eval t ^ 2 :=
        intervalIntegral.integral_congr (fun t _ => hprod t)
    _ = ∫ t in (-1 : ℝ)..1, W₁.eval t ^ 2 := by rw [hWeq]
    _ = ∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node₁ q) ^ 2 :=
        intervalIntegral.integral_congr (fun t _ => (hprod₁ t).symm)
    _ = ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) := homega₁

/-- The composite Gauss coefficient mass is bounded by the stated kernel integral budget plus `2
* K / (3 * highKernelC β) * (16 * h)^(2 * Q)`, as formalized for [An, Childs, and Lin, Lemma
12][AnChildsLin2026]. -/
theorem lemma12CoefficientMass : Lemma12CoefficientMass := by
  intro β K Q M node weight hβ hβ1 hK hQ hM hw hexact
  (try dsimp only)
  set h : ℝ := (2 * (K : ℝ)) / M with hh
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hpos : 0 < h := by rw [hh]; positivity
  have hpos2 : 0 < h / 2 := by positivity
  have hCpos := highKernelC_pos β
  have hCne : highKernelC β ≠ 0 := hCpos.ne'
  have hfint : Integrable (fun k : ℝ => ‖highKernelG β k‖) volume :=
    highKernelG_abs_integrable β hβ hβ1
  have hfintv : ∀ u v : ℝ, IntervalIntegrable (fun k : ℝ => ‖highKernelG β k‖) volume u v :=
    fun u v => (highKernelG_abs_continuous β).intervalIntegrable u v
  have hfcd : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) (fun k : ℝ => ‖highKernelG β k‖) :=
    (highKernelG_abs_contDiff β).of_le (WithTop.coe_le_coe.mpr le_top)
  have hG3 : (∫ k : ℝ, ‖highKernelG β k‖) ≤
      (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * (1 - β))) :=
    highKernelG_abs_integral_le β hβ hβ1
  have href := node_omega_prod_integral Q hQ node weight hexact
  set g : ℝ → ℝ := (fun k : ℝ => ‖highKernelG β k‖) with hgdef
  have hrpow : h ^ ((2 : ℝ) * Q + 1) = h ^ (2 * Q + 1) := by
    have hc : ((2 : ℝ) * Q + 1) = ((2 * Q + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hc, Real.rpow_natCast]
  have hsup : ∀ a : ℝ,
      (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) g k|)
        ≤ ((2 * Q).factorial : ℝ) * (32 : ℝ) ^ (2 * Q) / highKernelC β := by
    intro a
    have hmem : ∀ k, k ∈ Icc a (a + h) → |iteratedDeriv (2 * Q) g k|
        ≤ ((2 * Q).factorial : ℝ) * (32 : ℝ) ^ (2 * Q) / highKernelC β := fun k _ =>
      highKernelG_abs_deriv_le β hβ hβ1 (2 * Q) (by omega) k
    have hinner : ∀ k : ℝ, (⨆ _j : k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) g k|)
        ≤ ((2 * Q).factorial : ℝ) * (32 : ℝ) ^ (2 * Q) / highKernelC β := by
      intro k
      by_cases hk : k ∈ Icc a (a + h)
      · haveI : Nonempty (k ∈ Icc a (a + h)) := ⟨hk⟩
        rw [ciSup_le_iff (f := fun _j : k ∈ Icc a (a + h) => |iteratedDeriv (2 * Q) g k|)
          (bddAbove_def.mpr ⟨((2 * Q).factorial : ℝ) * (32 : ℝ) ^ (2 * Q) / highKernelC β,
            fun x hx => by
              obtain ⟨j, rfl⟩ := Set.mem_range.mp hx
              exact hmem k j⟩)]
        exact fun j => hmem k j
      · haveI : IsEmpty (k ∈ Icc a (a + h)) := ⟨fun hj => hk hj⟩
        rw [iSup_of_empty', Real.sSup_empty]
        exact div_nonneg (by positivity) hCpos.le
    exact ciSup_le hinner
  have hcell : ∀ m : Fin M,
      ∑ q, (h / 2) * weight q * g (-K + h * ((m : ℝ) + (node q + 1) / 2)) ≤
        (∫ x in (-K + h * (m : ℝ))..(-K + h * ((m : ℝ) + 1)), g x) +
          ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
              (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
            ((32 : ℝ) ^ (2 * Q) / highKernelC β) := by
    intro m
    set a : ℝ := -K + h * (m : ℝ) with hadef
    have hcellx := gauss_cell_rule_affine_exact Q a h node weight hexact
    have homegacell := gauss_cell_omega Q a h node hpos href
    have hG2 := gauss_legendre_cell_error_bound Q a h node weight g
      hQ hpos hcellx homegacell hfcd
    rw [hrpow] at hG2
    have habs := (abs_sub_le_iff.mp hG2).2
    have hErr : ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
        (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) g k|)
        ≤ ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
          ((32 : ℝ) ^ (2 * Q) / highKernelC β) := by
      have hnq : ((2 * Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hnf : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
      rw [show ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
          ((32 : ℝ) ^ (2 * Q) / highKernelC β)
          = ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
              (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
            (((2 * Q).factorial : ℝ) * (32 : ℝ) ^ (2 * Q) / highKernelC β) from by
        field_simp]
      exact mul_le_mul_of_nonneg_left (hsup a) (by positivity)
    have hnodeq : ∀ q : Fin Q,
        a + h * (node q + 1) / 2 = -K + h * ((m : ℝ) + (node q + 1) / 2) := by
      intro q
      rw [hadef]
      ring
    have hup : -K + h * ((m : ℝ) + 1) = a + h := by rw [hadef]; ring
    rw [hup]
    have hsum : ∑ q, (h / 2) * weight q * g (-K + h * ((m : ℝ) + (node q + 1) / 2))
        = ∑ q, (h / 2) * weight q * g (a + h * (node q + 1) / 2) :=
      Finset.sum_congr rfl (fun q _ => by rw [hnodeq q])
    rw [hsum]
    linarith [habs, hErr]
  have hpart : ∀ (n : ℕ) (b d : ℝ),
      (∑ m ∈ Finset.range n, ∫ x in b + d * (m : ℝ)..b + d * ((m : ℝ) + 1), g x)
        = ∫ x in b..b + d * (n : ℝ), g x := by
    intro n b d
    induction n with
    | zero => simp [intervalIntegral.integral_same]
    | succ n ih =>
        have hjoin : (∫ x in b..b + d * (n : ℝ), g x)
            + ∫ x in b + d * (n : ℝ)..b + d * ((n : ℝ) + 1), g x
            = ∫ x in b..b + d * ((n : ℝ) + 1), g x :=
          intervalIntegral.integral_add_adjacent_intervals (hfintv _ _) (hfintv _ _)
        rw [Finset.sum_range_succ, ih, hjoin, Nat.cast_succ]
  have hcells : (∑ m : Fin M, ∫ x in (-K + h * (m : ℝ))..(-K + h * ((m : ℝ) + 1)), g x)
      = ∫ x in (-K : ℝ)..(K : ℝ), g x := by
    rw [Fin.sum_univ_eq_sum_range
      (fun n : ℕ => ∫ x in (-K + h * (n : ℝ))..(-K + h * ((n : ℝ) + 1)), g x) M,
      hpart M (-K : ℝ) h]
    have hMh : h * (M : ℝ) = 2 * (K : ℝ) := by
      rw [hh]
      field_simp
    rw [hMh, show (-K : ℝ) + 2 * (K : ℝ) = (K : ℝ) from by ring]
  have hwindow : (∫ x in (-K : ℝ)..(K : ℝ), g x) ≤ ∫ k : ℝ, g k := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    have h1 := MeasureTheory.integral_add_compl
      (s := Set.Ioc (-K : ℝ) (K : ℝ)) (measurableSet_Ioc) hfint
    have h2 : 0 ≤ ∫ x in (Set.Ioc (-K : ℝ) (K : ℝ))ᶜ, g x :=
      integral_nonneg (fun _ => norm_nonneg _)
    linarith
  have htail : (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
        ((32 : ℝ) ^ (2 * Q) / highKernelC β))
      ≤ (2 * (K : ℝ)) / (3 * highKernelC β) * (16 * h) ^ (2 * Q) := by
    have hnq : ((2 * Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hnf : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
    have hT2 : (0 : ℝ) < (2 : ℝ) ^ (2 * Q) := by positivity
    have hP32 : ((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)) * (32 : ℝ) ^ (2 * Q)
        ≤ (16 : ℝ) ^ (2 * Q) := by
      have h32eq : (32 : ℝ) ^ (2 * Q) = (2 : ℝ) ^ (2 * Q) * (16 : ℝ) ^ (2 * Q) := by
        rw [show (32 : ℝ) = 2 * 16 from by norm_num, mul_pow]
      have hP2 : ((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)) *
          (2 : ℝ) ^ (2 * Q) ≤ 1 :=
        (le_div_iff₀ hT2).mp (gauss_factorial_ratio_le Q)
      calc ((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)) * (32 : ℝ) ^ (2 * Q)
          = (((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)) * (2 : ℝ) ^ (2 * Q)) *
              (16 : ℝ) ^ (2 * Q) := by rw [h32eq, mul_assoc]
        _ ≤ 1 * (16 : ℝ) ^ (2 * Q) :=
            mul_le_mul_of_nonneg_right hP2 (by positivity)
        _ = (16 : ℝ) ^ (2 * Q) := by ring
    have h3 : (3 : ℝ) ≤ ((2 * Q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 3 ≤ 2 * Q + 1)
    have hrew : (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
        ((32 : ℝ) ^ (2 * Q) / highKernelC β))
        = 2 * (K : ℝ) * (((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)
            * (32 : ℝ) ^ (2 * Q)) * h ^ (2 * Q))
          / (((2 * Q + 1 : ℕ) : ℝ) * highKernelC β) := by
      rw [show h ^ (2 * Q + 1) = h * h ^ (2 * Q) from by rw [pow_succ, mul_comm], hh]
      field_simp
    rw [hrew, mul_pow]
    have hX : (((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)
          * (32 : ℝ) ^ (2 * Q)) * h ^ (2 * Q))
        ≤ ((16 : ℝ) ^ (2 * Q)) * h ^ (2 * Q) :=
      mul_le_mul_of_nonneg_right hP32 (by positivity)
    have hnum : 2 * (K : ℝ) * (((Q.factorial : ℝ) ^ 4 / (((2 * Q).factorial : ℝ) ^ 2)
          * (32 : ℝ) ^ (2 * Q)) * h ^ (2 * Q))
        ≤ 2 * (K : ℝ) * ((16 : ℝ) ^ (2 * Q) * h ^ (2 * Q)) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have hden : (3 : ℝ) * highKernelC β
        ≤ ((2 * Q + 1 : ℕ) : ℝ) * highKernelC β :=
      mul_le_mul_of_nonneg_right h3 hCpos.le
    refine le_trans (div_le_div_of_nonneg_right hnum (by positivity)) ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hnormeq : (∑ m : Fin M, ∑ q : Fin Q,
      ‖(h / 2) * weight q * highKernelG β (-K + h * ((m : ℝ) + (node q + 1) / 2))‖)
      = ∑ m : Fin M, ∑ q : Fin Q,
          (h / 2) * weight q * g (-K + h * ((m : ℝ) + (node q + 1) / 2)) := by
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro q _
    change ‖((h : ℂ) / 2 * (weight q : ℂ)) *
      highKernelG β (-K + h * ((m : ℝ) + (node q + 1) / 2))‖ = _
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      abs_of_pos hpos, abs_of_pos (hw q)]
    rfl
  calc (∑ m : Fin M, ∑ q : Fin Q,
        ‖(h / 2) * weight q * highKernelG β (-K + h * ((m : ℝ) + (node q + 1) / 2))‖)
      = ∑ m : Fin M, ∑ q : Fin Q,
          (h / 2) * weight q * g (-K + h * ((m : ℝ) + (node q + 1) / 2)) := hnormeq
    _ ≤ ∑ m : Fin M, ((∫ x in (-K + h * (m : ℝ))..(-K + h * ((m : ℝ) + 1)), g x) +
          ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
              (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
            ((32 : ℝ) ^ (2 * Q) / highKernelC β)) :=
          Finset.sum_le_sum (fun m _ => hcell m)
    _ = (∑ m : Fin M, ∫ x in (-K + h * (m : ℝ))..(-K + h * ((m : ℝ) + 1)), g x) +
          (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
              (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
            ((32 : ℝ) ^ (2 * Q) / highKernelC β)) := by
          have hE : (∑ _m : Fin M, ((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
              (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
            ((32 : ℝ) ^ (2 * Q) / highKernelC β)) = (M : ℝ) *
              (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
                (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
              ((32 : ℝ) ^ (2 * Q) / highKernelC β)) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_add_distrib, hE]
    _ ≤ (∫ k : ℝ, g k) +
          (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
              (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) *
            ((32 : ℝ) ^ (2 * Q) / highKernelC β)) := by linarith
    _ ≤ (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * (1 - β))) +
          (2 * (K : ℝ)) / (3 * highKernelC β) * (16 * h) ^ (2 * Q) := by
          linarith [hG3, htail]

end Qatlib.Concepts.LchsSimulation.Quadrature
