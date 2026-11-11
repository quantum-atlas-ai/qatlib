/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowHamSim26.FourierTrunc.Definitions
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / FourierTrunc — Lemma 4.3 (Eq. (4.35), p. 22)

Fixed source: arXiv:2608.17653v1.  For `ρ > 1` and the decreasing sum

`S(ζ) = Σ_{m=0}^∞ e^{-m^{1/ρ}/ζ}`,

one has `Γ(ρ+1) ζ^ρ ≤ S(ζ) ≤ 1 + Γ(ρ+1) ζ^ρ` for every `ζ > 0`.
-/

set_option autoImplicit false
open MeasureTheory Filter
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.FourierTrunc

/-- Fixed arXiv:2608.17653v1, Lemma 4.3, Eq. (4.35), p. 22.
`Γ(ρ+1) ζ^ρ ≤ S(ζ) ≤ 1 + Γ(ρ+1) ζ^ρ` for `ρ > 1`, `ζ > 0`. -/
theorem lemma_four_three_gamma_sum
    (ρ ζ : ℝ) (hρ : 1 < ρ) (hζ : 0 < ζ) :
    Real.Gamma (ρ + 1) * ζ ^ ρ ≤ Ssum ρ ζ ∧
      Ssum ρ ζ ≤ 1 + Real.Gamma (ρ + 1) * ζ ^ ρ := by
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ (1 / ρ)) / ζ) with hfdef
  have hfpos : ∀ x, 0 < f x := fun x => Real.exp_pos _
  have hΓpos : 0 < Real.Gamma (ρ + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hζρpos : 0 < ζ ^ ρ := Real.rpow_pos_of_pos hζ ρ
  have hP : (0 : ℝ) < Real.Gamma (ρ + 1) * ζ ^ ρ := mul_pos hΓpos hζρpos
  -- **Part 1: the integral evaluation** `∫₀^∞ f = Γ(ρ+1) ζ^ρ`, Eqs. (4.38)–(4.41).
  have hpw : ∀ x ∈ Set.Ioi (0 : ℝ), (x ^ ρ) ^ (1 / ρ) = x := fun x hx => by
    have hinv : ρ * (1 / ρ) = 1 := by field_simp
    rw [← Real.rpow_mul hx.le ρ (1 / ρ), hinv, Real.rpow_one]
  have hs1 : (∫ x in Set.Ioi 0, (ρ * x ^ (ρ - 1)) • Real.exp (-((x ^ ρ) ^ (1 / ρ)) / ζ))
      = ∫ x in Set.Ioi 0, ρ * x ^ (ρ - 1) * Real.exp (-(x / ζ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    show (ρ * x ^ (ρ - 1)) • Real.exp (-((x ^ ρ) ^ (1 / ρ)) / ζ)
        = ρ * x ^ (ρ - 1) * Real.exp (-(x / ζ))
    rw [hpw x hx, smul_eq_mul, neg_div]
  have hL1 : (∫ x in Set.Ioi 0, ρ * x ^ (ρ - 1) * Real.exp (-(x / ζ)))
      = ∫ x in Set.Ioi 0, ρ * (ζ * ((1 / ζ) * x)) ^ (ρ - 1) * Real.exp (-((1 / ζ) * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show ρ * x ^ (ρ - 1) * Real.exp (-(x / ζ))
        = ρ * (ζ * ((1 / ζ) * x)) ^ (ρ - 1) * Real.exp (-((1 / ζ) * x))
    have h1 : ζ * ((1 / ζ) * x) = x := by field_simp
    have h2 : (1 / ζ) * x = x / ζ := by field_simp
    rw [h1, h2]
  have hsub2 := MeasureTheory.integral_comp_mul_left_Ioi
    (g := fun t => ρ * (ζ * t) ^ (ρ - 1) * Real.exp (-t)) 0
    (div_pos one_pos hζ : (0 : ℝ) < 1 / ζ)
  have hpts : ∀ t ∈ Set.Ioi (0 : ℝ),
      ρ * (ζ * t) ^ (ρ - 1) * Real.exp (-t)
        = (ρ * ζ ^ (ρ - 1)) * (Real.exp (-t) * t ^ (ρ - 1)) := by
    intro t ht
    rw [Real.mul_rpow hζ.le ht.le]
    ring
  have hintΓ : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (ρ - 1))
      (Set.Ioi 0) := Real.GammaIntegral_convergent hρpos
  have hL2 : (∫ t in Set.Ioi 0, ρ * (ζ * t) ^ (ρ - 1) * Real.exp (-t))
      = (ρ * ζ ^ (ρ - 1)) * (∫ t in Set.Ioi 0, Real.exp (-t) * t ^ (ρ - 1)) := by
    have hc : (∫ t in Set.Ioi 0, ρ * (ζ * t) ^ (ρ - 1) * Real.exp (-t))
        = ∫ t in Set.Ioi 0, (ρ * ζ ^ (ρ - 1)) • (Real.exp (-t) * t ^ (ρ - 1)) :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => by
          show ρ * (ζ * t) ^ (ρ - 1) * Real.exp (-t)
              = (ρ * ζ ^ (ρ - 1)) • (Real.exp (-t) * t ^ (ρ - 1))
          rw [hpts t ht, smul_eq_mul])
    rw [hc, integral_smul, smul_eq_mul]
  have hGam : (∫ t in Set.Ioi 0, Real.exp (-t) * t ^ (ρ - 1)) = Real.Gamma ρ :=
    (Real.Gamma_eq_integral hρpos).symm
  have hzp2 : ζ * ζ ^ (ρ - 1) = ζ ^ ρ := by
    have h := Real.rpow_add hζ 1 (ρ - 1)
    have h2 : (1 : ℝ) + (ρ - 1) = ρ := by ring
    rw [h2, Real.rpow_one ζ] at h
    exact h.symm
  have hz0 : Set.Ioi ((1 / ζ) * (0 : ℝ)) = Set.Ioi (0 : ℝ) := by simp
  have hzeta : (1 / ζ)⁻¹ = ζ := by field_simp
  have hI : (∫ x in Set.Ioi 0, f x) = Real.Gamma (ρ + 1) * ζ ^ ρ := by
    have hsub1 := MeasureTheory.integral_comp_rpow_Ioi_of_pos
      (g := fun y => Real.exp (-(y ^ (1 / ρ)) / ζ)) hρpos
    calc (∫ x in Set.Ioi 0, f x)
        = ∫ x in Set.Ioi 0, (ρ * x ^ (ρ - 1)) • Real.exp (-((x ^ ρ) ^ (1 / ρ)) / ζ) :=
          hsub1.symm
      _ = ∫ x in Set.Ioi 0, ρ * x ^ (ρ - 1) * Real.exp (-(x / ζ)) := hs1
      _ = ∫ x in Set.Ioi 0, ρ * (ζ * ((1 / ζ) * x)) ^ (ρ - 1) * Real.exp (-((1 / ζ) * x)) :=
          hL1
      _ = (1 / ζ)⁻¹ • ∫ t in Set.Ioi ((1 / ζ) * 0), ρ * (ζ * t) ^ (ρ - 1) * Real.exp (-t) :=
          hsub2
      _ = ζ * ((ρ * ζ ^ (ρ - 1)) * Real.Gamma ρ) := by
          rw [hz0, hzeta, hL2, hGam, smul_eq_mul]
      _ = Real.Gamma (ρ + 1) * ζ ^ ρ := by
          rw [Real.Gamma_add_one hρne]
          have hrr : ζ * ((ρ * ζ ^ (ρ - 1)) * Real.Gamma ρ)
              = (ρ * Real.Gamma ρ) * (ζ * ζ ^ (ρ - 1)) := by ring
          rw [hrr, hzp2]
  -- **Part 2: `f` is antitone; the integral test on `[0,N]` (Eqs. (4.36)–(4.37)).**
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro a ha b hb hab
    apply Real.exp_le_exp.mpr
    have hr : a ^ (1 / ρ) ≤ b ^ (1 / ρ) := Real.rpow_le_rpow ha hab (le_of_lt (div_pos one_pos hρpos))
    rw [div_le_div_iff₀ hζ hζ]
    have h2 := mul_le_mul_of_nonneg_right hr hζ.le
    linarith
  have hIccN : ∀ N : ℕ, AntitoneOn f (Set.Icc (0 : ℝ) (N : ℝ)) := fun N =>
    hanti.mono fun x hx => hx.1
  have hlowN : ∀ N : ℕ, (∫ x in (0 : ℝ)..(N : ℝ), f x) ≤ ∑ i ∈ Finset.range N, f ((i : ℝ)) := by
    intro N
    have hAN : AntitoneOn f (Set.Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by simpa using hIccN N
    simpa using hAN.integral_le_sum
  have hupN : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, f ((i : ℝ) + 1)) ≤ ∫ x in (0 : ℝ)..(N : ℝ), f x := by
    intro N
    have hAN : AntitoneOn f (Set.Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by simpa using hIccN N
    simpa [Nat.cast_add, Nat.cast_one] using hAN.sum_le_integral
  -- **Part 3: summability, integrability, and the limit `N → ∞`.**
  have hintf : IntegrableOn f (Set.Ioi 0) := by
    by_contra hn
    have hI2 : (∫ x, f x ∂(volume.restrict (Set.Ioi 0)))
        = Real.Gamma (ρ + 1) * ζ ^ ρ := hI
    rw [MeasureTheory.integral_undef hn] at hI2
    linarith
  have htnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlimI : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), f x) atTop
      (nhds (∫ x in Set.Ioi 0, f x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hintf htnat
  have hmonoN : Monotone (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), f x) := by
    intro M N hMN
    have hab : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hiv1 : IntervalIntegrable f volume (0 : ℝ) (M : ℝ) := by
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le (Nat.cast_nonneg M)]
      exact hIccN M
    have hiv2 : IntervalIntegrable f volume (M : ℝ) (N : ℝ) := by
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact (hIccN N).mono fun x hx =>
        ⟨le_trans (Nat.cast_nonneg M) hx.1, hx.2⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hiv1 hiv2
    have hnn : (0 : ℝ) ≤ ∫ x in (M : ℝ)..(N : ℝ), f x :=
      intervalIntegral.integral_nonneg hab fun u _ => le_of_lt (hfpos u)
    show (∫ x in (0 : ℝ)..(M : ℝ), f x) ≤ ∫ x in (0 : ℝ)..(N : ℝ), f x
    rw [← hsplit]
    linarith
  have hble : ∀ N : ℕ, (∫ x in (0 : ℝ)..(N : ℝ), f x) ≤ ∫ x in Set.Ioi 0, f x :=
    fun N => hmonoN.ge_of_tendsto hlimI N
  have hf0 : f (0 : ℝ) = 1 := by
    have hz : ((0 : ℝ) ^ (1 / ρ)) = 0 :=
      Real.zero_rpow (div_ne_zero one_ne_zero hρne)
    rw [hfdef]
    show Real.exp (-((0 : ℝ) ^ (1 / ρ)) / ζ) = 1
    rw [hz]
    simp
  have hfsumN : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, f ((i : ℝ))) ≤ 1 + ∫ x in Set.Ioi 0, f x := by
    intro N
    cases N with
    | zero => simp; linarith
    | succ N' =>
      have hshift : (∑ i ∈ Finset.range (N' + 1), f ((i : ℝ)))
          = f (0 : ℝ) + ∑ i ∈ Finset.range N', f ((i : ℝ) + 1) := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
      rw [hshift, hf0]
      have h1 := hupN N'
      have h2 := hble N'
      linarith
  have hsumG : Summable (fun m : ℕ => f ((m : ℝ))) :=
    summable_of_sum_range_le (fun n => le_of_lt (hfpos ((n : ℝ)))) hfsumN
  have hlimS : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, f ((i : ℝ))) atTop
      (nhds (∑' m : ℕ, f ((m : ℝ)))) :=
    hsumG.hasSum.tendsto_sum_nat
  have hIle : (∫ x in Set.Ioi 0, f x) ≤ ∑' m : ℕ, f ((m : ℝ)) := by
    refine le_of_tendsto_of_tendsto hlimI hlimS ?_
    filter_upwards with N
    exact hlowN N
  have hSle : (∑' m : ℕ, f ((m : ℝ))) ≤ 1 + ∫ x in Set.Ioi 0, f x := by
    refine Real.tsum_le_of_sum_le (fun m => le_of_lt (hfpos ((m : ℝ)))) ?_
    intro u
    have hsub : u ⊆ Finset.range (u.sup id + 1) := fun b hb =>
      Finset.mem_range.2 (by
        have h1 : id b ≤ u.sup id := Finset.le_sup hb
        have h2 : id b = b := rfl
        omega)
    calc ∑ x ∈ u, f ((x : ℝ)) ≤ ∑ x ∈ Finset.range (u.sup id + 1), f ((x : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => le_of_lt (hfpos ((x : ℝ))))
      _ ≤ 1 + ∫ x in Set.Ioi 0, f x := hfsumN _
  have hGm : ∀ m : ℕ, Real.exp (-((m : ℝ) ^ (1 / ρ)) / ζ) = f ((m : ℝ)) := fun m => by
    rw [hfdef]
  refine ⟨?_, ?_⟩
  · calc Real.Gamma (ρ + 1) * ζ ^ ρ = ∫ x in Set.Ioi 0, f x := hI.symm
      _ ≤ ∑' m : ℕ, f ((m : ℝ)) := hIle
      _ = ∑' m : ℕ, Real.exp (-((m : ℝ) ^ (1 / ρ)) / ζ) := tsum_congr fun m => (hGm m).symm
      _ = Ssum ρ ζ := rfl
  · calc Ssum ρ ζ = ∑' m : ℕ, Real.exp (-((m : ℝ) ^ (1 / ρ)) / ζ) := rfl
      _ = ∑' m : ℕ, f ((m : ℝ)) := tsum_congr hGm
      _ ≤ 1 + ∫ x in Set.Ioi 0, f x := hSle
      _ = 1 + Real.Gamma (ρ + 1) * ζ ^ ρ := by rw [hI]

/-- Fixed arXiv:2608.17653v1, Lemma 4.3, Eq. (4.35), p. 22 (claim c008, same
result as `lemma_four_three_gamma_sum`). -/
theorem claim_c008_lemma_four_three
    (ρ ζ : ℝ) (hρ : 1 < ρ) (hζ : 0 < ζ) :
    Real.Gamma (ρ + 1) * ζ ^ ρ ≤ Ssum ρ ζ ∧
      Ssum ρ ζ ≤ 1 + Real.Gamma (ρ + 1) * ζ ^ ρ :=
  lemma_four_three_gamma_sum ρ ζ hρ hζ

end Qatlib.Papers.SlowHamSim26.FourierTrunc
end
