/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
import Mathlib.Analysis.Asymptotics.Theta
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates
open Filter Set Asymptotics
open scoped Topology
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
set_option warningAsError false

theorem log_one_add_div_le {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hεA : ε ≤ 1 / (1 + A)) :
    Real.log (1 + A / ε) ≤ 2 * Real.log (1 / ε) := by
  have hAp : 0 < 1 + A := by linarith
  have hr : 1 + A / ε ≤ (1 + A) / ε := by
    apply (le_div_iff₀ hε).mpr
    have he : (1 + A / ε) * ε = ε + A := by field_simp
    rw [he]
    linarith
  have hrec : 1 + A ≤ 1 / ε := by
    apply (le_div_iff₀ hε).mpr
    have hm := (le_div_iff₀ hAp).mp hεA
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 1 + A / ε) hr
  have hAlog := Real.log_le_log hAp hrec
  rw [Real.log_div hAp.ne' hε.ne'] at hl
  have hL : Real.log (1 / ε) = -Real.log ε := by simp
  rw [hL] at hAlog ⊢
  linarith

theorem mesh_log_le {M κ ε εm : ℝ} (hM : 0 < M) (hκ : 0 < κ) (hε : 0 < ε)
    (hbudget : κ * ε ≤ εm) (hε1 : ε ≤ 1) (hsmall : ε ≤ 1 / (1 + 2 * M / κ)) :
    Real.log (1 + 2 * M / εm) ≤ 2 * Real.log (1 / ε) := by
  have hm : 0 < εm := lt_of_lt_of_le (mul_pos hκ hε) hbudget
  have hr : 2 * M / εm ≤ (2 * M / κ) / ε := by
    calc
      _ ≤ 2 * M / (κ * ε) := div_le_div_of_nonneg_left (by positivity) (mul_pos hκ hε) hbudget
      _ = _ := by ring
  exact (Real.log_le_log (by positivity : 0 < 1 + 2 * M / εm) (by linarith)).trans
    (log_one_add_div_le (by positivity : 0 ≤ 2 * M / κ) hε hε1 hsmall)

theorem log_inv_ge_one {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / Real.exp 1) :
    1 ≤ Real.log (1 / ε) := by
  have he : Real.exp 1 ≤ 1 / ε := by
    apply (le_div_iff₀ hε).mpr
    have hm := (le_div_iff₀ (Real.exp_pos 1)).mp hsmall
    nlinarith
  simpa only [Real.log_exp] using! Real.log_le_log (Real.exp_pos 1) he

theorem tail_log_le {C κ ε εt : ℝ} (hC : 0 < C) (hκ : 0 < κ) (hε : 0 < ε)
    (hbudget : κ * ε ≤ εt) (hε1 : ε ≤ 1) (hsmall : ε ≤ 1 / (1 + C / κ))
    (hexp : ε ≤ 1 / Real.exp 1) :
    max 1 (Real.log (C / εt)) ≤ 2 * Real.log (1 / ε) := by
  have ht : 0 < εt := lt_of_lt_of_le (mul_pos hκ hε) hbudget
  have hr : C / εt ≤ 1 + (C / κ) / ε := by
    have hdiv := div_le_div_of_nonneg_left hC.le (mul_pos hκ hε) hbudget
    have he : C / (κ * ε) = (C / κ) / ε := by ring
    rw [he] at hdiv
    linarith
  apply max_le
  · linarith [log_inv_ge_one hε hexp]
  · exact (Real.log_le_log (div_pos hC ht) hr).trans
      (log_one_add_div_le (by positivity : 0 ≤ C / κ) hε hε1 hsmall)

theorem exists_log_window (M C κm κt : ℝ) (hM : 0 < M) (hC : 0 < C)
    (hκm : 0 < κm) (hκt : 0 < κt) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ εm εt : ℝ,
      κm * ε ≤ εm → κt * ε ≤ εt →
      Real.log (1 + 2 * M / εm) ≤ 2 * Real.log (1 / ε) ∧
      max 1 (Real.log (C / εt)) ≤ 2 * Real.log (1 / ε) ∧ 1 ≤ Real.log (1 / ε) := by
  let δ := min 1 (min (1 / (1 + 2 * M / κm))
    (min (1 / (1 + C / κt)) (1 / Real.exp 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun ε hε hεδ εm εt hmesh htail => ?_⟩
  have hε1 : ε ≤ 1 := hεδ.trans (min_le_left _ _)
  have hsmallm : ε ≤ 1 / (1 + 2 * M / κm) :=
    hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallt : ε ≤ 1 / (1 + C / κt) :=
    hεδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hexp : ε ≤ 1 / Real.exp 1 :=
    hεδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨mesh_log_le hM hκm hε hmesh hε1 hsmallm,
    tail_log_le hC hκt hε htail hε1 hsmallt hexp, log_inv_ge_one hε hexp⟩

theorem sqrt_log_le {L ℓ : ℝ} (hL : 1 ≤ L) (hℓ : ℓ ≤ 2 * L) :
    Real.sqrt ℓ ≤ 2 * Real.sqrt L := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  calc
    _ ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt (by linarith)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]

theorem node_scale_le {c ρ L ℓt ℓm : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (ht : ℓt ≤ 2 * L) (hm : ℓm ≤ 2 * L) (hm0 : 0 ≤ ℓm) :
    4 * (1 + (1 + c) * Real.sqrt ℓt + (c / ρ) * Real.sqrt ℓt * ℓm) ≤
      (12 + 8 * c + 16 * c / ρ) * (L * Real.sqrt L) := by
  have hs := sqrt_log_le hL ht
  have hq : 0 ≤ c / ρ := by positivity
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 + c)
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul hs hm hm0 (by positivity)) hq
  have hroot : Real.sqrt L ≤ L * Real.sqrt L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (Real.sqrt_nonneg L)]
  have hone : 1 ≤ L * Real.sqrt L :=
    (show 1 ≤ Real.sqrt L by simpa using! Real.sqrt_le_sqrt hL).trans hroot
  have hp1 := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 4)
  have hp2 := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 8 * (1 + c))
  have hp3 : 4 * (1 + (1 + c) * Real.sqrt ℓt + (c / ρ) * Real.sqrt ℓt * ℓm) ≤
      4 * (1 + (1 + c) * (2 * Real.sqrt L) + (c / ρ) * (2 * Real.sqrt L * (2 * L))) := by
    nlinarith [h1, h2]
  calc
    _ ≤ 4 * (1 + (1 + c) * (2 * Real.sqrt L) + (c / ρ) * (2 * Real.sqrt L * (2 * L))) := hp3
    _ = 4 + (8 * (1 + c)) * Real.sqrt L + (16 * (c / ρ)) * (L * Real.sqrt L) := by ring
    _ ≤ 4 * (L * Real.sqrt L) + (8 * (1 + c)) * (L * Real.sqrt L) +
        (16 * (c / ρ)) * (L * Real.sqrt L) := by
      exact _root_.add_le_add (_root_.add_le_add (by simpa only [mul_one] using! hp1) hp2) le_rfl
    _ = _ := by ring

theorem radius_scale_le {c L ℓt : ℝ} (hc : 0 < c) (hL : 1 ≤ L) (ht : ℓt ≤ 2 * L) :
    2 * c * Real.sqrt ℓt + 1 ≤ (4 * c + 1) * Real.sqrt L := by
  have hs := mul_le_mul_of_nonneg_left (sqrt_log_le hL ht) (by positivity : 0 ≤ 2 * c)
  have hroot : 1 ≤ Real.sqrt L := by simpa using! Real.sqrt_le_sqrt hL
  nlinarith

theorem eventual_budget_logs (M C : ℝ) (hM : 0 < M) (hC : 0 < C)
    (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ Real.log (1 + 2 * M / εm ε) ≤ 2 * Real.log (1 / ε) ∧
      max 1 (Real.log (C / εt ε)) ≤ 2 * Real.log (1 / ε) ∧ 1 ≤ Real.log (1 / ε) := by
  obtain ⟨κm, hκm, hmesh⟩ := isBigO_iff''.mp hmO
  obtain ⟨κt, hκt, htail⟩ := isBigO_iff''.mp htO
  obtain ⟨δ, hδ, hwindow⟩ := exists_log_window M C κm κt hM hC hκm hκt
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < δ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hsmall, hmesh, htail, hmpos, htpos]
    with ε hε hεδ hm ht hemp hetp
  have hεp : 0 < ε := hε
  simp only [Real.norm_eq_abs, abs_of_pos hεp, abs_of_pos hemp] at hm
  simp only [Real.norm_eq_abs, abs_of_pos hεp, abs_of_pos hetp] at ht
  exact ⟨hεp, hwindow ε hεp hεδ.le (εm ε) (εt ε) hm ht⟩

theorem three_halves {L : ℝ} (hL : 1 ≤ L) :
    L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by linarith : 0 < L), Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem radius_isGreatest (R h : ℝ) (hh : 0 ≤ h) :
    IsGreatest {r : ℝ | ∃ q ∈ Finset.Icc (-(cutoff R h : ℤ)) (cutoff R h : ℤ),
      r = |h * (q : ℝ)|} (radius R h) := by
  constructor
  · refine ⟨(cutoff R h : ℤ), Finset.mem_Icc.mpr ⟨?_, le_rfl⟩, ?_⟩
    · omega
    · simp only [Int.cast_natCast, abs_of_nonneg (mul_nonneg hh (Nat.cast_nonneg _)), radius]
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact node_le_radius R h hh q hq

theorem selected_nodes_isBigO (c ρ M C : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hC : 0 < C) (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt) :
    (fun ε : ℝ => ((Finset.Icc
      (-(cutoff (tailRadius c C (εt ε)) (meshStep c ρ M (εm ε)) : ℤ))
      (cutoff (tailRadius c C (εt ε)) (meshStep c ρ M (εm ε)) : ℤ)).card : ℝ)) =O[𝓝[>] 0]
        (fun ε => (c / ρ) * (Real.log (1 / ε)) ^ (3 / 2 : ℝ)) := by
  apply IsBigO.of_bound ((12 + 8 * c + 16 * c / ρ) / (c / ρ))
  filter_upwards [eventual_budget_logs M C hM hC εm εt hmpos htpos hmO htO, hmpos]
    with ε hlogs hemp
  have hn := budget_node_count c ρ M C (εm ε) (εt ε) hc hρ hM hemp
  have hs := node_scale_le hc hρ hlogs.2.2.2 hlogs.2.2.1 hlogs.2.1 (meshLog_pos hM hemp).le
  have hf : 0 ≤ ((Finset.Icc
      (-(cutoff (tailRadius c C (εt ε)) (meshStep c ρ M (εm ε)) : ℤ))
      (cutoff (tailRadius c C (εt ε)) (meshStep c ρ M (εm ε)) : ℤ)).card : ℝ) := by positivity
  have hL : 0 ≤ Real.log (1 / ε) := le_trans (by norm_num) hlogs.2.2.2
  have hg : 0 ≤ (c / ρ) * (Real.log (1 / ε)) ^ (3 / 2 : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
  calc
    _ ≤ (12 + 8 * c + 16 * c / ρ) *
        (Real.log (1 / ε) * Real.sqrt (Real.log (1 / ε))) := hn.trans hs
    _ = _ := by rw [three_halves hlogs.2.2.2]; field_simp

theorem selected_radius_isBigO (c ρ M C : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (hM : 0 < M) (hC : 0 < C) (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt) :
    (fun ε : ℝ => radius (tailRadius c C (εt ε)) (meshStep c ρ M (εm ε))) =O[𝓝[>] 0]
      (fun ε => c * Real.sqrt (Real.log (1 / ε))) := by
  apply IsBigO.of_bound ((4 * c + 1) / c)
  filter_upwards [eventual_budget_logs M C hM hC εm εt hmpos htpos hmO htO, hmpos]
    with ε hlogs hemp
  have hh := meshStep_pos hc hρ hM hemp
  have hR : 0 ≤ tailRadius c C (εt ε) := by unfold tailRadius; positivity
  have hr := (radius_lt_add hR hh).le
  have hh1 : meshStep c ρ M (εm ε) ≤ 1 := min_le_left _ _
  have hf : 0 ≤ radius (tailRadius c C (εt ε)) (meshStep c ρ M (εm ε)) := by
    unfold radius
    exact mul_nonneg hh.le (Nat.cast_nonneg _)
  have hg : 0 ≤ c * Real.sqrt (Real.log (1 / ε)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
  calc
    _ ≤ 2 * c * Real.sqrt (tailLog C (εt ε)) + 1 := by
      change _ ≤ tailRadius c C (εt ε) + 1
      linarith
    _ ≤ (4 * c + 1) * Real.sqrt (Real.log (1 / ε)) :=
      radius_scale_le hc hlogs.2.2.2 hlogs.2.2.1
    _ = _ := by field_simp

theorem kernel_balanced_geometry (n : ℕ) (b c d ρ K : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hbn : n = 0 ∨ ρ < b) (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmΘ : εm =Θ[𝓝[>] 0] (fun ε : ℝ => ε))
    (htΘ : εt =Θ[𝓝[>] 0] (fun ε : ℝ => ε)) :
    let M := mass n b c d ρ K
    let C := tailConstant n b c d
    let h := fun ε => meshStep c ρ M (εm ε)
    let R := fun ε => tailRadius c C (εt ε)
    ((fun ε : ℝ => ((Finset.Icc (-(cutoff (R ε) (h ε) : ℤ))
      (cutoff (R ε) (h ε) : ℤ)).card : ℝ)) =O[𝓝[>] 0]
        (fun ε => (c / ρ) * (Real.log (1 / ε)) ^ (3 / 2 : ℝ))) ∧
    ((fun ε : ℝ => radius (R ε) (h ε)) =O[𝓝[>] 0]
      (fun ε => c * Real.sqrt (Real.log (1 / ε)))) := by
  (try dsimp only)
  have hM := mass_pos n b c d ρ K hb hc hρ1 hbn
  have hC := tailConstant_pos n b c d hb hc
  exact ⟨selected_nodes_isBigO c ρ _ _ hc hρ0 hM hC εm εt hmpos htpos hmΘ.2 htΘ.2,
    selected_radius_isBigO c ρ _ _ hc hρ0 hM hC εm εt hmpos htpos hmΘ.2 htΘ.2⟩

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates
