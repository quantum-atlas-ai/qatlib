/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
import Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhGeometry
open Set Filter Asymptotics
open scoped Topology
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule (window)
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)

theorem arsinh_le_twolog {u : ℝ} (hu : 0 ≤ u) : Real.arsinh u ≤ 2 * Real.log (1 + u) := by
  have hs : Real.sqrt (1 + u ^ 2) ≤ 1 + u := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  have ha : u + Real.sqrt (1 + u ^ 2) ≤ (1 + u) ^ 2 := by nlinarith
  have he : 2 * Real.log (1 + u) = Real.log ((1 + u) ^ 2) := by rw [Real.log_pow]; norm_num
  rw [he, Real.arsinh]
  exact Real.log_le_log (by positivity) ha

def windowFactor : ℝ := 2 + 1 / Real.log 2

theorem window_le_log {u : ℝ} (hu : 1 ≤ u) :
    max 1 (Real.arsinh u) ≤ windowFactor * Real.log (1 + u) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (1 + u) := Real.log_le_log (by norm_num) (by linarith)
  have hL : 0 ≤ Real.log (1 + u) := hlog.le.trans hl
  have hunit : 1 ≤ Real.log (1 + u) / Real.log 2 := (le_div_iff₀ hlog).mpr (by simpa using! hl)
  have hnon : 0 ≤ Real.log (1 + u) / Real.log 2 := by positivity
  rw [show windowFactor * Real.log (1 + u) =
    2 * Real.log (1 + u) + Real.log (1 + u) / Real.log 2 by unfold windowFactor; ring]
  apply max_le
  · linarith
  · have ha := arsinh_le_twolog (show 0 ≤ u by linarith)
    linarith

theorem inv_step_le {β M ε : ℝ} (hβ : 0 < β) (hM : 0 < M) (hε : 0 < ε) :
    1 / step β M ε ≤ 1 + meshLog M ε / (2 * Real.pi * β) := by
  have hl := meshLog_pos hM hε
  have hq : 0 ≤ meshLog M ε / (2 * Real.pi * β) := by positivity
  unfold step
  rcases min_choice (1 : ℝ) (2 * Real.pi * β / meshLog M ε) with he | he
  · rw [he, one_div_one]
    linarith
  · rw [he]
    have hi : 1 / (2 * Real.pi * β / meshLog M ε) = meshLog M ε / (2 * Real.pi * β) := by field_simp
    rw [hi]
    linarith

def nodeFactor : ℝ := 3 + 2 * windowFactor

theorem budget_node_count (c η β M C εm εt : ℝ) (hη : 0 < η)
    (hηc : η ≤ 2 * c) (hβ : 0 < β) (hM : 0 < M) (hεm : 0 < εm) :
    let u := 2 * c / η * Real.sqrt (tailLog C εt)
    let h := step β M εm
    let Y := window c η (Real.sqrt (tailLog C εt))
    ((Finset.Icc (-(cutoff Y h : ℤ)) (cutoff Y h)).card : ℝ) ≤
      nodeFactor * (1 + Real.log (1 + u) * (1 + meshLog M εm / β)) := by
  (try dsimp only)
  let u := 2 * c / η * Real.sqrt (tailLog C εt)
  let h := step β M εm
  let Y := window c η (Real.sqrt (tailLog C εt))
  have hh : 0 < h := step_pos hβ hM hεm
  have hY : 0 ≤ Y := le_trans (by norm_num) (le_max_left _ _)
  have hell : 1 ≤ tailLog C εt := le_max_left _ _
  have hu : 1 ≤ u := by
    have hratio : 1 ≤ 2 * c / η := (le_div_iff₀ hη).mpr (by simpa using! hηc)
    have hs : 1 ≤ Real.sqrt (tailLog C εt) := by simpa using! Real.sqrt_le_sqrt hell
    dsimp [u]
    nlinarith
  have hw : Y ≤ windowFactor * Real.log (1 + u) := window_le_log hu
  have hn := node_count_le hY hh
  have hi := inv_step_le hβ hM hεm
  have hl : 0 ≤ meshLog M εm := (meshLog_pos hM hεm).le
  have hlog : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hfact : 0 < windowFactor := by unfold windowFactor; positivity
  have hq : meshLog M εm / (2 * Real.pi * β) ≤ meshLog M εm / β := by
    apply div_le_div_of_nonneg_left hl (by positivity)
    nlinarith [Real.pi_gt_three]
  have hprod : 2 * Y / h ≤ 2 * (windowFactor * Real.log (1 + u)) * (1 + meshLog M εm / β) := by
    calc
      _ = 2 * Y * (1 / h) := by ring
      _ ≤ 2 * Y * (1 + meshLog M εm / β) :=
        mul_le_mul_of_nonneg_left (hi.trans (by linarith)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) (by positivity)
  change _ ≤ _
  dsimp [nodeFactor]
  nlinarith [mul_nonneg hlog (show 0 ≤ 1 + meshLog M εm / β by positivity)]

def radiusFactor : ℝ := 2 * (Real.cosh 1 + Real.sinh 1) +
  Real.sinh 1 * (Real.cosh 1 + Real.sinh 1 + 1)

theorem radius_bound {c η h u : ℝ} (hc : 0 < c) (hη : 0 < η) (hh : 0 < h)
    (hh₁ : h ≤ 1) (hu : 0 ≤ u) :
    η * Real.sinh (h * cutoff (window c η u) h) ≤ radiusFactor * (c * u + η) := by
  let v := 2 * c / η * u
  let Y := window c η u
  have hY : 0 ≤ Y := le_trans (by norm_num) (le_max_left _ _)
  have hround := (Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid.radius_lt_add hY hh).le
  have hceil : h * cutoff Y h ≤ Y + 1 := by
    change h * cutoff Y h ≤ Y + h at hround
    linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsY : Real.sinh Y ≤ Real.sinh 1 + v := by
    rcases le_total (1 : ℝ) (Real.arsinh v) with he | he
    · have hYY : Y = Real.arsinh v := max_eq_right he
      rw [hYY, Real.sinh_arsinh]
      linarith [Real.sinh_nonneg_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)]
    · have hYY : Y = 1 := max_eq_left he
      rw [hYY]
      linarith
  have hcY : Real.cosh Y ≤ 1 + Real.sinh Y := by
    simpa only [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hY)] using!
      Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip.cosh_le_one_add_abs_sinh Y
  have hs1 : 0 ≤ Real.sinh 1 := Real.sinh_nonneg_iff.mpr (by norm_num)
  have hc1 : 0 ≤ Real.cosh 1 := (Real.cosh_pos _).le
  have he : η * v = 2 * c * u := by dsimp [v]; field_simp
  have hbound : η * Real.sinh (h * cutoff Y h) ≤
      2 * (Real.cosh 1 + Real.sinh 1) * c * u +
        Real.sinh 1 * (Real.cosh 1 + Real.sinh 1 + 1) * η := by
    calc
      _ ≤ η * Real.sinh (Y + 1) := mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr hceil) hη.le
      _ = η * (Real.sinh Y * Real.cosh 1 + Real.cosh Y * Real.sinh 1) := by rw [Real.sinh_add]
      _ ≤ η * ((Real.sinh 1 + v) * Real.cosh 1 + (1 + Real.sinh 1 + v) * Real.sinh 1) := by
        apply mul_le_mul_of_nonneg_left _ hη.le
        exact add_le_add (mul_le_mul_of_nonneg_right hsY hc1)
          (mul_le_mul_of_nonneg_right (by linarith : Real.cosh Y ≤ 1 + Real.sinh 1 + v) hs1)
      _ = _ := by nlinarith [he]
  change _ ≤ _
  unfold radiusFactor
  have hcross1 : 0 ≤ 2 * (Real.cosh 1 + Real.sinh 1) * η := by positivity
  have hcross2 : 0 ≤ Real.sinh 1 * (Real.cosh 1 + Real.sinh 1 + 1) * (c * u) := by positivity
  nlinarith

theorem windowFactor_pos : 0 < windowFactor := by unfold windowFactor; positivity

theorem nodeFactor_pos : 0 < nodeFactor := by
    unfold nodeFactor; have := windowFactor_pos; positivity

theorem radiusFactor_pos : 0 < radiusFactor := by
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
  unfold radiusFactor
  positivity

theorem log_double_le {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + 2 * u) ≤ 2 * Real.log (1 + u) := by
  have h := Real.log_le_log (by positivity : 0 < 1 + 2 * u)
    (show 1 + 2 * u ≤ (1 + u) ^ 2 by nlinarith [sq_nonneg u])
  simpa only [Real.log_pow, Nat.cast_ofNat] using! h

theorem node_scale_le {c η β L ℓt ℓm : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hηc : η ≤ 2 * c) (hβ : 0 < β) (hL : 1 ≤ L) (ht : ℓt ≤ 2 * L)
    (hm : ℓm ≤ 2 * L) (hm₀ : 0 ≤ ℓm) :
    nodeFactor * (1 + Real.log (1 + 2 * c / η * Real.sqrt ℓt) * (1 + ℓm / β)) ≤
      (nodeFactor * (β / Real.log 2 + 2 * β + 4)) *
        ((1 / β) * L * Real.log (1 + 2 * c / η * Real.sqrt L)) := by
  let F := Real.log (1 + 2 * c / η * Real.sqrt L)
  have hsqrt := Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates.sqrt_log_le hL ht
  have hA : 1 ≤ 2 * c / η := (le_div_iff₀ hη).mpr (by simpa using! hηc)
  have hsL : 1 ≤ Real.sqrt L := by simpa using! Real.sqrt_le_sqrt hL
  have hv : 1 ≤ 2 * c / η * Real.sqrt L := by nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hF₂ : Real.log 2 ≤ F := Real.log_le_log (by norm_num) (by linarith)
  have hF : 0 ≤ F := hlog2.le.trans hF₂
  have hFt : Real.log (1 + 2 * c / η * Real.sqrt ℓt) ≤ 2 * F := by
    have hu := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2 * c / η by positivity)
    have hlog := Real.log_le_log (by positivity : 0 < 1 + 2 * c / η * Real.sqrt ℓt)
      (show 1 + 2 * c / η * Real.sqrt ℓt ≤ 1 + 2 * (2 * c / η * Real.sqrt L) by nlinarith)
    exact hlog.trans (log_double_le (by positivity))
  have hdiv : ℓm / β ≤ 2 * L / β := div_le_div_of_nonneg_right hm hβ.le
  have hLF : F ≤ L * F := by nlinarith
  have hunit : 1 ≤ (L * F) / Real.log 2 := (le_div_iff₀ hlog2).mpr (by nlinarith)
  have hprod : Real.log (1 + 2 * c / η * Real.sqrt ℓt) * (1 + ℓm / β) ≤
      2 * F * (1 + 2 * L / β) :=
    mul_le_mul hFt (by linarith) (by positivity) (by positivity)
  have hsum : 1 + Real.log (1 + 2 * c / η * Real.sqrt ℓt) * (1 + ℓm / β) ≤
      (1 / Real.log 2 + 2 + 4 / β) * (L * F) := by
    calc
      _ ≤ (L * F) / Real.log 2 + 2 * F * (1 + 2 * L / β) := by linarith
      _ = (L * F) / Real.log 2 + 2 * F + 4 * (L * F) / β := by ring
      _ ≤ (L * F) / Real.log 2 + 2 * (L * F) + 4 * (L * F) / β := by linarith
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hsum nodeFactor_pos.le
  convert! hmul using 1
  dsimp [F]
  field_simp

theorem selected_nodes_isBigO (c η β M C : ℝ) (hc : 0 < c) (hη : 0 < η)
    (hηc : η ≤ 2 * c) (hβ : 0 < β) (hM : 0 < M) (hC : 0 < C)
    (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt) :
    (fun ε : ℝ => ((Finset.Icc
      (-(cutoff (window c η (Real.sqrt (tailLog C (εt ε)))) (step β M (εm ε)) : ℤ))
      (cutoff (window c η (Real.sqrt (tailLog C (εt ε)))) (step β M (εm ε)) : ℤ)).card : ℝ)) =O[𝓝[>] 0]
        (fun ε => (1 / β) * Real.log (1 / ε) *
          Real.log (1 + 2 * c / η * Real.sqrt (Real.log (1 / ε)))) := by
  apply IsBigO.of_bound (nodeFactor * (β / Real.log 2 + 2 * β + 4))
  filter_upwards [Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates.eventual_budget_logs
      M C hM hC εm εt hmpos htpos hmO htO, hmpos] with ε hlogs hemp
  have hn := budget_node_count c η β M C (εm ε) (εt ε) hη hηc hβ hM hemp
  have hs := node_scale_le hc hη hηc hβ hlogs.2.2.2 hlogs.2.2.1 hlogs.2.1 (meshLog_pos hM hemp).le
  have hf : 0 ≤ ((Finset.Icc
      (-(cutoff (window c η (Real.sqrt (tailLog C (εt ε)))) (step β M (εm ε)) : ℤ))
      (cutoff (window c η (Real.sqrt (tailLog C (εt ε)))) (step β M (εm ε)) : ℤ)).card : ℝ) := by positivity
  have hg : 0 ≤ (1 / β) * Real.log (1 / ε) *
      Real.log (1 + 2 * c / η * Real.sqrt (Real.log (1 / ε))) := by
    have hL : 0 ≤ Real.log (1 / ε) := by linarith [hlogs.2.2.2]
    have hlog : 0 ≤ Real.log (1 + 2 * c / η * Real.sqrt (Real.log (1 / ε))) := by
      apply Real.log_nonneg
      have hh : 0 ≤ 2 * c / η * Real.sqrt (Real.log (1 / ε)) := by positivity
      linarith
    exact mul_nonneg (mul_nonneg (by positivity) hL) hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
  exact hn.trans hs

theorem selected_radius_isBigO (c η β M C : ℝ) (hc : 0 < c) (hη : 0 < η)
    (hβ : 0 < β) (hM : 0 < M) (hC : 0 < C) (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt) :
    (fun ε : ℝ => η * Real.sinh (step β M (εm ε) *
      cutoff (window c η (Real.sqrt (tailLog C (εt ε)))) (step β M (εm ε)))) =O[𝓝[>] 0]
        (fun ε => c * Real.sqrt (Real.log (1 / ε)) + η) := by
  apply IsBigO.of_bound (2 * radiusFactor)
  filter_upwards [Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates.eventual_budget_logs
      M C hM hC εm εt hmpos htpos hmO htO, hmpos] with ε hlogs hemp
  have hh := step_pos hβ hM hemp
  have hr := radius_bound hc hη hh (min_le_left _ _) (Real.sqrt_nonneg (tailLog C (εt ε)))
  have hsqrt := Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates.sqrt_log_le
    hlogs.2.2.2 hlogs.2.2.1
  change Real.sqrt (tailLog C (εt ε)) ≤ 2 * Real.sqrt (Real.log (1 / ε)) at hsqrt
  have hf : 0 ≤ η * Real.sinh (step β M (εm ε) *
      cutoff (window c η (Real.sqrt (tailLog C (εt ε)))) (step β M (εm ε))) :=
    mul_nonneg hη.le (Real.sinh_nonneg_iff.mpr (mul_nonneg hh.le (Nat.cast_nonneg _)))
  have hg : 0 ≤ c * Real.sqrt (Real.log (1 / ε)) + η := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
  have hscale : radiusFactor * (c * Real.sqrt (tailLog C (εt ε)) + η) ≤
      2 * radiusFactor * (c * Real.sqrt (Real.log (1 / ε)) + η) := by
    have hm := mul_le_mul_of_nonneg_left hsqrt hc.le
    calc
      _ ≤ radiusFactor * (2 * (c * Real.sqrt (Real.log (1 / ε)) + η)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) radiusFactor_pos.le
      _ = _ := by ring
  exact hr.trans hscale

theorem uniform_geometry_isBigO {α : Type*} (l : Filter α)
    (c η β M C εm εt : α → ℝ)
    (ha : ∀ᶠ x in l, 0 < c x ∧ 0 < η x ∧ η x ≤ 2 * c x ∧
      0 < β x ∧ 0 < M x ∧ 0 < εm x) :
    ((fun x => ((Finset.Icc
      (-(cutoff (window (c x) (η x) (Real.sqrt (tailLog (C x) (εt x))))
        (step (β x) (M x) (εm x)) : ℤ))
      (cutoff (window (c x) (η x) (Real.sqrt (tailLog (C x) (εt x))))
        (step (β x) (M x) (εm x)) : ℤ)).card : ℝ)) =O[l]
      (fun x => 1 + Real.log (1 + 2 * c x / η x * Real.sqrt (tailLog (C x) (εt x))) *
        (1 + meshLog (M x) (εm x) / β x))) ∧
    ((fun x => η x * Real.sinh (step (β x) (M x) (εm x) *
      cutoff (window (c x) (η x) (Real.sqrt (tailLog (C x) (εt x))))
        (step (β x) (M x) (εm x)))) =O[l]
      (fun x => c x * Real.sqrt (tailLog (C x) (εt x)) + η x)) := by
  constructor
  · apply IsBigO.of_bound nodeFactor
    filter_upwards [ha] with x hx
    rcases hx with ⟨hc, hη, hηc, hβ, hM, hm⟩
    have hn := budget_node_count (c x) (η x) (β x) (M x) (C x) (εm x) (εt x)
      hη hηc hβ hM hm
    have hf : 0 ≤ ((Finset.Icc
      (-(cutoff (window (c x) (η x) (Real.sqrt (tailLog (C x) (εt x))))
        (step (β x) (M x) (εm x)) : ℤ))
      (cutoff (window (c x) (η x) (Real.sqrt (tailLog (C x) (εt x))))
        (step (β x) (M x) (εm x)) : ℤ)).card : ℝ) := by positivity
    have hl : 0 ≤ Real.log (1 + 2 * c x / η x * Real.sqrt (tailLog (C x) (εt x))) := by
      apply Real.log_nonneg
      have hu : 0 ≤ 2 * c x / η x * Real.sqrt (tailLog (C x) (εt x)) := by positivity
      linarith
    have hg : 0 ≤ 1 + Real.log (1 + 2 * c x / η x * Real.sqrt (tailLog (C x) (εt x))) *
        (1 + meshLog (M x) (εm x) / β x) := by
      have hlog := meshLog_pos hM hm
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
    exact hn
  · apply IsBigO.of_bound radiusFactor
    filter_upwards [ha] with x hx
    rcases hx with ⟨hc, hη, _, hβ, hM, hm⟩
    have hh := step_pos hβ hM hm
    have hr := radius_bound hc hη hh (min_le_left _ _) (Real.sqrt_nonneg (tailLog (C x) (εt x)))
    have hf : 0 ≤ η x * Real.sinh (step (β x) (M x) (εm x) *
        cutoff (window (c x) (η x) (Real.sqrt (tailLog (C x) (εt x))))
          (step (β x) (M x) (εm x))) :=
      mul_nonneg hη.le (Real.sinh_nonneg_iff.mpr (mul_nonneg hh.le (Nat.cast_nonneg _)))
    have hg : 0 ≤ c x * Real.sqrt (tailLog (C x) (εt x)) + η x := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
    exact hr

open Complex Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

theorem kernel_budget_geometry (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hηc : η ≤ 2 * c) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T εm εt : ℝ}
    (hT : 0 ≤ T) (hεm : 0 < εm) (hεt : 0 < εt)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    let M := stripMass n b c d η β (T * ‖L‖)
    let h := step β M εm
    let Y := selectedWindow n b c d η εt
    let u := 2 * c / η * Real.sqrt (tailLog (tailConstant n b c d) εt)
    0 < h ∧
      (‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
        finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤ εm + εt) ∧
      ((Finset.Icc (-(cutoff Y h : ℤ)) (cutoff Y h)).card = 2 * cutoff Y h + 1) ∧
      (((Finset.Icc (-(cutoff Y h : ℤ)) (cutoff Y h)).card : ℝ) ≤
        nodeFactor * (1 + Real.log (1 + u) * (1 + meshLog M εm / β))) ∧
      (IsGreatest {r : ℝ | ∃ q ∈ Finset.Icc (-(cutoff Y h : ℤ)) (cutoff Y h),
        r = |η * Real.sinh (h * (q : ℝ))|} (η * Real.sinh (h * cutoff Y h))) ∧
      η * Real.sinh (h * cutoff Y h) ≤
        radiusFactor * (c * Real.sqrt (tailLog (tailConstant n b c d) εt) + η) := by
  (try dsimp only)
  let M := stripMass n b c d η β (T * ‖L‖)
  let h := step β M εm
  let Y := selectedWindow n b c d η εt
  have hM : 0 < M := stripMass_pos n b c d η β hb hc hη hβ₀.le hβ T H L hw
  have he := selected_error n b c d η β hb hc hη hβ₀ hβ H L hH hL hT hεm hεt hw
  have hh : 0 < h := step_pos hβ₀ hM hεm
  exact ⟨hh, he.2, Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid.node_count Y h,
    budget_node_count c η β M (tailConstant n b c d) εm εt hη hηc hβ₀ hM hεm,
    physical_radius_max η Y h hη.le hh.le,
    radius_bound hc hη hh (min_le_left _ _) (Real.sqrt_nonneg _)⟩

theorem kernel_balanced_geometry (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hηc : η ≤ 2 * c) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) {T : ℝ}
    (hw : (β : EReal) < analyticWidth n b c d T η H L) (εm εt : ℝ → ℝ)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt) :
    let M := stripMass n b c d η β (T * ‖L‖)
    ((fun ε : ℝ => ((Finset.Icc
      (-(cutoff (selectedWindow n b c d η (εt ε)) (step β M (εm ε)) : ℤ))
      (cutoff (selectedWindow n b c d η (εt ε)) (step β M (εm ε)) : ℤ)).card : ℝ)) =O[𝓝[>] 0]
        (fun ε => (1 / β) * Real.log (1 / ε) *
          Real.log (1 + 2 * c / η * Real.sqrt (Real.log (1 / ε))))) ∧
    ((fun ε : ℝ => η * Real.sinh (step β M (εm ε) *
      cutoff (selectedWindow n b c d η (εt ε)) (step β M (εm ε)))) =O[𝓝[>] 0]
        (fun ε => c * Real.sqrt (Real.log (1 / ε)) + η)) := by
  (try dsimp only)
  have hM := stripMass_pos n b c d η β hb hc hη hβ₀.le hβ T H L hw
  have hC := tailConstant_pos n b c d hb hc
  exact ⟨selected_nodes_isBigO c η β _ _ hc hη hηc hβ₀ hM hC εm εt hmpos htpos hmO htO,
    selected_radius_isBigO c η β _ _ hc hη hβ₀ hM hC εm εt hmpos htpos hmO htO⟩

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhGeometry
