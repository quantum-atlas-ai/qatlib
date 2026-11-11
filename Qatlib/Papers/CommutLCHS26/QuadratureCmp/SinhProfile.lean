/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhGeometry

/-!
# Asymptotic profiles for sinh quadrature

This module controls the strip mass and Gaussian tails of the sinh-transformed LCHS kernel
uniformly over bounded derivative orders and shifts. It derives finite quadrature error bounds
and asymptotic node counts for the free-scale geometry studied in [AftabAnTrivisa2026].

For fixed admissible strip width and scale `c = O(sqrt(log(1/ε)))`, `profile_rates` bounds the
node count by `O(log(1/ε) log(log(1/ε)))` and the physical radius by `O(log(1/ε))`, provided the
positive mesh and tail budgets are bounded below by constant multiples of `ε`.

## Main statements

* `uniform_mass_logs`: Uniform quadratic bounds for logarithms of the strip mass and tail
  constant.
* `kernel_profile_bounds`: Combines the selected finite-rule error with node-count and radius
  estimates.
* `width_growth_of_balanced_approx`: Transfers scale growth between comparable approximation
  budgets.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhProfile
open Set Filter Asymptotics
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)
open scoped Topology
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhGeometry

/-- Factors `stripMass` into an explicit geometric prefactor, the scale `c`, and the exponential
of `postExponent`, under the stated positivity assumptions. -/
theorem mass_factor (n : ℕ) (b c d η β K : ℝ) (hc : 0 < c) (hη : 0 < η)
    (hcos : 0 < Real.cos (2 * β)) :
    stripMass n b c d η β K =
      (2 * kernelPrefactor n b η β * Real.sqrt (2 * Real.pi / Real.cos (2 * β))) *
        c * Real.exp (postExponent c d η β K) := by
  have hq : 0 < η / (2 * c) := by positivity
  have he : 2 * Real.pi / (scaleSq c η * Real.cos (2 * β)) =
      (2 * Real.pi / Real.cos (2 * β)) / (η / (2 * c)) ^ 2 := by
    unfold scaleSq
    ring
  have hs : Real.sqrt (2 * Real.pi / (scaleSq c η * Real.cos (2 * β))) =
      Real.sqrt (2 * Real.pi / Real.cos (2 * β)) / (η / (2 * c)) := by
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hq]
  unfold stripMass stripAmplitude
  rw [hs]
  field_simp

/-- Bounds `postExponent` by an explicit affine function of `c ^ 2` when `η ≤ 2 * c`, the strip
angle is below `π / 4`, and `|d| ≤ D`. -/
theorem exponent_bound {c d η β K D : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hηc : η ≤ 2 * c) (hβ : 0 ≤ β) (hβπ : β < Real.pi / 4)
    (hK : 0 ≤ K) (hd : |d| ≤ D) :
    let G := η * Real.sin β * (D + K)
    postExponent c d η β K ≤ D + Real.sin β ^ 2 + G +
      (2 * G ^ 2 / (η ^ 2 * Real.cos (2 * β))) * c ^ 2 := by
  (try dsimp only)
  let G := η * Real.sin β * (D + K)
  have hs : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (2 * β) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hg₀ : 0 ≤ growth η β d K := by unfold growth; positivity
  have hg : growth η β d K ≤ G :=
      mul_le_mul_of_nonneg_left (by linarith : |d| + K ≤ D + K) (by positivity)
  have hG : 0 ≤ G := hg₀.trans hg
  have hratio : η / (2 * c) ≤ 1 := (div_le_one (by positivity)).mpr hηc
  have hr : 0 ≤ η / (2 * c) := by positivity
  have hscale : scaleSq c η ≤ 1 := by unfold scaleSq; nlinarith
  have hsq : growth η β d K ^ 2 ≤ G ^ 2 := by nlinarith
  have he : growth η β d K ^ 2 / (2 * (scaleSq c η * Real.cos (2 * β))) =
      (2 * growth η β d K ^ 2 / (η ^ 2 * Real.cos (2 * β))) * c ^ 2 := by
    unfold scaleSq
    field_simp
  have hcorr : (2 * growth η β d K ^ 2 / (η ^ 2 * Real.cos (2 * β))) * c ^ 2 ≤
      (2 * G ^ 2 / (η ^ 2 * Real.cos (2 * β))) * c ^ 2 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity : 0 ≤ η ^ 2 * Real.cos (2 * β)))
    (sq_nonneg c)
  have htrig := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Real.sin β))
  have hd' : d ≤ D := (le_abs_self d).trans hd
  have hneg : 0 ≤ 1 / (4 * c ^ 2) := by positivity
  unfold postExponent
  rw [he]
  dsimp [G] at *
  nlinarith

/-- The kernel prefactor is positive when `b` and `η` are positive and the strip angle satisfies
the stated pole-separation conditions. -/
theorem prefactor_pos (n : ℕ) {b η β : ℝ} (hb : 0 < b) (hη : 0 < η)
    (hβ : 0 ≤ β) (hβπ : β < Real.pi / 2) (hgap : η * Real.sin β < 1)
    (hbn : n = 0 ∨ η * Real.sin β < b) : 0 < kernelPrefactor n b η β := by
  have hD := distance_product_pos n hη hβ hβπ hgap hbn
  unfold kernelPrefactor
  apply div_pos (pow_pos (by linarith : 0 < b + 1) n)
  convert! mul_pos (show 0 < 2 * Real.pi by positivity) hD using 1
  ring

/-- For positive `c`, the logarithm `Real.log c` is bounded above by `c ^ 2`. -/
theorem log_c_le_sq {c : ℝ} (hc : 0 < c) : Real.log c ≤ c ^ 2 := by
  have h := Real.log_le_sub_one_of_pos hc
  nlinarith [sq_nonneg (c - 1 / 2)]

/-- For fixed admissible parameters and `0 < c` with `η ≤ 2 * c`, the strip mass and tail
constant are positive and their logarithms have common bounds `A + B * c ^ 2`, uniformly
over `n ≤ N` and `|d| ≤ D`. -/
theorem uniform_mass_logs (N : ℕ) (b η β K D : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hβ : 0 ≤ β) (hβπ : β < Real.pi / 4) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hgap : η * Real.sin β < 1) (hNb : N = 0 ∨ η * Real.sin β < b) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ n : ℕ, n ≤ N → ∀ c d : ℝ,
      0 < c → η ≤ 2 * c → |d| ≤ D →
      0 < stripMass n b c d η β K ∧ 0 < tailConstant n b c d ∧
      Real.log (stripMass n b c d η β K) ≤ A + B * c ^ 2 ∧
      Real.log (tailConstant n b c d) ≤ A + B * c ^ 2 := by
  let F := fun n : ℕ => 2 * kernelPrefactor n b η β * Real.sqrt (2 * Real.pi / Real.cos (2 * β))
  let P := fun n : ℕ => (1 / Real.sqrt Real.pi) * ((b + 1) / b) ^ n
  let S := ∑ j ∈ Finset.range (N + 1), (|Real.log (F j)| + |Real.log (P j)|)
  let G := η * Real.sin β * (D + K)
  let A := 1 + S + D + Real.sin β ^ 2 + G
  let B := 1 + 2 * G ^ 2 / (η ^ 2 * Real.cos (2 * β))
  have hs : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (2 * β) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, B, hA, hB, fun n hn c d hc hηc hd => ?_⟩
  have hbn : n = 0 ∨ η * Real.sin β < b := by
    rcases hNb with hN | hg
    · exact Or.inl (by omega)
    · exact Or.inr hg
  have hF : 0 < F n := by
    dsimp [F]
    exact mul_pos
        (mul_pos (by norm_num) (prefactor_pos n hb hη hβ (by linarith [Real.pi_pos]) hgap hbn))
        (Real.sqrt_pos.mpr (by positivity))
  have hP : 0 < P n := by dsimp [P]; positivity
  have hlogs : |Real.log (F n)| + |Real.log (P n)| ≤ S := by
    dsimp only [S]
    exact Finset.single_le_sum (f := fun j : ℕ => |Real.log (F j)| + |Real.log (P j)|)
      (fun j _ => by positivity) (Finset.mem_range.mpr (by omega))
  have hLF : Real.log (F n) ≤ S := by
    linarith [le_abs_self (Real.log (F n)), abs_nonneg (Real.log (P n))]
  have hLP : Real.log (P n) ≤ S := by
    linarith [le_abs_self (Real.log (P n)), abs_nonneg (Real.log (F n))]
  have hM : stripMass n b c d η β K = F n * c * Real.exp (postExponent c d η β K) :=
      mass_factor n b c d η β K hc hη hcos
  have hC : tailConstant n b c d = P n * c * Real.exp (d - 1 / (4 * c ^ 2)) := by
    unfold tailConstant P
    ring
  have hMp : 0 < stripMass n b c d η β K := by rw [hM]; positivity
  have hCp : 0 < tailConstant n b c d := tailConstant_pos n b c d hb hc
  refine ⟨hMp, hCp, ?_, ?_⟩
  · rw [hM, Real.log_mul (mul_pos hF hc).ne' (Real.exp_ne_zero _),
      Real.log_mul hF.ne' hc.ne', Real.log_exp]
    have he := exponent_bound hc hη hηc hβ hβπ hK hd
    have hl := log_c_le_sq hc
    dsimp [A, B, G] at *
    nlinarith
  · rw [hC, Real.log_mul (mul_pos hP hc).ne' (Real.exp_ne_zero _),
      Real.log_mul hP.ne' hc.ne', Real.log_exp]
    have hl := log_c_le_sq hc
    have hd' : d ≤ D := (le_abs_self d).trans hd
    have he : 0 ≤ 1 / (4 * c ^ 2) := by positivity
    have hB1 : 1 ≤ B := by
      have he : 0 ≤ 2 * G ^ 2 / (η ^ 2 * Real.cos (2 * β)) := by positivity
      dsimp [B]
      linarith
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr hB1) (sq_nonneg c)]

/-- If `x > 0` and `Real.log x ≤ R` with `R ≥ 0`, then `Real.log (1 + x) ≤ Real.log 2 + R`. -/
theorem log_one_add_bound {x R : ℝ} (hx : 0 < x) (hR : 0 ≤ R)
    (hlog : Real.log x ≤ R) : Real.log (1 + x) ≤ Real.log 2 + R := by
  rcases le_total x 1 with h | h
  · have hl := Real.log_le_log (by positivity : 0 < 1 + x) (show 1 + x ≤ 2 by linarith)
    linarith
  · have hl := Real.log_le_log (by positivity : 0 < 1 + x) (show 1 + x ≤ 2 * x by linarith)
    rw [Real.log_mul (by norm_num) hx.ne'] at hl
    linarith

/-- Converts quadratic bounds for `Real.log M` and `Real.log C` into explicit bounds
proportional to `log(1/ε)` for `meshLog` and `tailLog`, using the stated scale and budget
inequalities. -/
theorem logs_le_of_mass_logs {M C c ε εm εt A B U κm κt : ℝ}
    (hM : 0 < M) (hC : 0 < C) (hε : 0 < ε) (hA : 0 < A) (hB : 0 < B)
    (hU : 0 ≤ U) (hκm : 0 < κm) (hκt : 0 < κt)
    (hm : κm * ε ≤ εm) (ht : κt * ε ≤ εt)
    (hL : 1 ≤ Real.log (1 / ε)) (hc : c ^ 2 ≤ U * Real.log (1 / ε))
    (hLM : Real.log M ≤ A + B * c ^ 2) (hLC : Real.log C ≤ A + B * c ^ 2) :
    meshLog M εm ≤ (2 * Real.log 2 + A + |Real.log κm| + B * U + 1) * Real.log (1 / ε) ∧
    tailLog C εt ≤ (A + |Real.log κt| + B * U + 1) * Real.log (1 / ε) := by
  let L := Real.log (1 / ε)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hmp : 0 < εm := (mul_pos hκm hε).trans_le hm
  have htp : 0 < εt := (mul_pos hκt hε).trans_le ht
  have hlm := Real.log_le_log (mul_pos hκm hε) hm
  have hlt := Real.log_le_log (mul_pos hκt hε) ht
  rw [Real.log_mul hκm.ne' hε.ne'] at hlm
  rw [Real.log_mul hκt.ne' hε.ne'] at hlt
  have hlogε : L = - Real.log ε := by simp [L]
  have hBc := mul_le_mul_of_nonneg_left hc hB.le
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have hr : Real.log (2 * M / εm) ≤ Real.log 2 + A + B * c ^ 2 + |Real.log κm| + L := by
      rw [Real.log_div (mul_pos (by norm_num) hM).ne' hmp.ne',
        Real.log_mul (by norm_num) hM.ne']
      linarith [neg_le_abs (Real.log κm)]
    have hR : 0 ≤ Real.log 2 + A + B * c ^ 2 + |Real.log κm| + L := by positivity
    have hlog := log_one_add_bound (by positivity : 0 < 2 * M / εm) hR hr
    have hconst : 0 ≤ 2 * Real.log 2 + A + |Real.log κm| := by positivity
    have hscale := mul_le_mul_of_nonneg_left hL hconst
    dsimp only [meshLog]
    dsimp only [L] at *
    nlinarith
  · have hr : Real.log (C / εt) ≤ A + B * c ^ 2 + |Real.log κt| + L := by
      rw [Real.log_div hC.ne' htp.ne']
      linarith [neg_le_abs (Real.log κt)]
    have hconst : 0 ≤ A + |Real.log κt| := by positivity
    have hscale := mul_le_mul_of_nonneg_left hL hconst
    unfold tailLog
    apply max_le
    · have hcoef : 1 ≤ A + |Real.log κt| + B * U + 1 := by
        have he : 0 ≤ B * U := mul_nonneg hB.le hU
        linarith [abs_nonneg (Real.log κt)]
      nlinarith
    · dsimp only [L] at *
      nlinarith

/-- Under eventual admissibility, positive budgets bounded below in the Big-O sense by `ε`, and
square-root logarithmic scale growth, both budget logarithms are eventually bounded by a
common positive multiple of `log(1/ε)`. -/
theorem eventual_profile_logs (N : ℕ) (b η β K D : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hβ : 0 ≤ β) (hβπ : β < Real.pi / 4) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hgap : η * Real.sin β < 1) (hNb : N = 0 ∨ η * Real.sin β < b)
    (n : ℝ → ℕ) (c d εm εt : ℝ → ℝ)
    (ha : ∀ᶠ ε : ℝ in 𝓝[>] 0, n ε ≤ N ∧ 0 < c ε ∧ η ≤ 2 * c ε ∧ |d ε| ≤ D)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt)
    (hcO : c =O[𝓝[>] 0] (fun ε => Real.sqrt (Real.log (1 / ε)))) :
    ∃ J : ℝ, 0 < J ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ 1 ≤ Real.log (1 / ε) ∧
      0 < stripMass (n ε) b (c ε) (d ε) η β K ∧
      0 < tailConstant (n ε) b (c ε) (d ε) ∧
      meshLog (stripMass (n ε) b (c ε) (d ε) η β K) (εm ε) ≤ J * Real.log (1 / ε) ∧
      tailLog (tailConstant (n ε) b (c ε) (d ε)) (εt ε) ≤ J * Real.log (1 / ε) := by
  obtain ⟨A, B, hA, hB, hmass⟩ := uniform_mass_logs N b η β K D hb hη hβ hβπ hK hD hgap hNb
  obtain ⟨κm, hκm, hm⟩ := isBigO_iff''.mp hmO
  obtain ⟨κt, hκt, ht⟩ := isBigO_iff''.mp htO
  obtain ⟨κc, hκc, hcs⟩ := isBigO_iff''.mp hcO
  let U := 1 / κc ^ 2
  let Km := 2 * Real.log 2 + A + |Real.log κm| + B * U + 1
  let Kt := A + |Real.log κt| + B * U + 1
  have hU : 0 < U := by dsimp [U]; positivity
  have hKm : 0 < Km := by dsimp [Km]; positivity
  have hKt : 0 < Kt := by dsimp [Kt]; positivity
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / Real.exp 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity))
  refine ⟨Km + Kt, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hsmall, ha, hmpos, htpos, hm, ht, hcs]
    with ε hε hsmall ha hemp hetp hm ht hcs
  have hεp : 0 < ε := hε
  have hL := Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates.log_inv_ge_one hεp hsmall.le
  rcases ha with ⟨hn, hcp, hηc, hd⟩
  simp only [Real.norm_eq_abs, abs_of_pos hεp, abs_of_pos hemp] at hm
  simp only [Real.norm_eq_abs, abs_of_pos hεp, abs_of_pos hetp] at ht
  simp only [Real.norm_eq_abs, abs_of_pos hcp, Real.sqrt_nonneg, abs_of_nonneg] at hcs
  have hc2 : c ε ^ 2 ≤ U * Real.log (1 / ε) := by
    have hs := Real.sq_sqrt (show 0 ≤ Real.log (1 / ε) by linarith)
    have hp : 0 ≤ κc * c ε := by positivity
    have hsq : (κc * c ε) ^ 2 ≤ (Real.sqrt (Real.log (1 / ε))) ^ 2 :=
        sq_le_sq₀ hp (Real.sqrt_nonneg _) |>.mpr hcs
    calc
      _ ≤ Real.log (1 / ε) / κc ^ 2 := (le_div_iff₀ (sq_pos_of_pos hκc)).mpr (by nlinarith)
      _ = _ := by dsimp [U]; ring
  obtain ⟨hM, hC, hLM, hLC⟩ := hmass (n ε) hn (c ε) (d ε) hcp hηc hd
  obtain ⟨hlm, hlt⟩ := logs_le_of_mass_logs hM hC hεp hA hB hU.le hκm hκt hm ht hL hc2 hLM hLC
  refine ⟨hεp, hL, hM, hC, hlm.trans ?_, hlt.trans ?_⟩
  · change Km * _ ≤ _
    nlinarith [mul_nonneg hKt.le (show 0 ≤ Real.log (1 / ε) by linarith)]
  · change Kt * _ ≤ _
    nlinarith [mul_nonneg hKm.le (show 0 ≤ Real.log (1 / ε) by linarith)]

/-- If `u` is eventually nonnegative, `u = O(L)`, and `L` tends to infinity, then `log(1 + u) =
O(log L)` along the same filter. -/
theorem log_one_add_isBigO {α : Type*} {l : Filter α} {u L : α → ℝ}
    (hu : ∀ᶠ x in l, 0 ≤ u x) (hO : u =O[l] L) (hL : Tendsto L l atTop) :
    (fun x => Real.log (1 + u x)) =O[l] (fun x => Real.log (L x)) := by
  obtain ⟨κ, hκ, hb⟩ := isBigO_iff''.mp hO
  let C := 1 + 1 / κ
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [one_div_pos.mpr hκ]
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hlog := (Real.tendsto_log_atTop.comp hL).eventually_ge_atTop 1
  have hL1 := hL.eventually_ge_atTop 1
  apply IsBigO.of_bound (Real.log C + 1)
  filter_upwards [hu, hb, hlog, hL1] with x hu hb hlog hL1
  change 1 ≤ Real.log (L x) at hlog
  have hLp : 0 < L x := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg hu, abs_of_pos hLp] at hb
  have hule : u x ≤ L x / κ := (le_div_iff₀ hκ).mpr (by nlinarith)
  have harg : 1 + u x ≤ C * L x := by
    rw [show L x / κ = (1 / κ) * L x by ring] at hule
    dsimp [C]
    nlinarith
  have hle := Real.log_le_log (by positivity : 0 < 1 + u x) harg
  rw [Real.log_mul hC.ne' hLp.ne'] at hle
  have hln : 0 ≤ Real.log (1 + u x) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hln,
      abs_of_nonneg (by linarith : 0 ≤ Real.log (L x))]
  nlinarith

/-- For a fixed admissible sinh geometry and the stated budget and scale profiles, the selected
node count is `O(log(1/ε) log(log(1/ε)))` and the physical radius is `O(log(1/ε))` as `ε`
tends to zero from above. This gives the fixed-geometry profile estimates of
[AftabAnTrivisa2026]. -/
theorem profile_rates (N : ℕ) (b η β K D : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hβ : 0 < β) (hβπ : β < Real.pi / 4) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hgap : η * Real.sin β < 1) (hNb : N = 0 ∨ η * Real.sin β < b)
    (n : ℝ → ℕ) (c d εm εt : ℝ → ℝ)
    (ha : ∀ᶠ ε : ℝ in 𝓝[>] 0, n ε ≤ N ∧ 0 < c ε ∧ η ≤ 2 * c ε ∧ |d ε| ≤ D)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt)
    (hcO : c =O[𝓝[>] 0] (fun ε => Real.sqrt (Real.log (1 / ε)))) :
    let M := fun ε => stripMass (n ε) b (c ε) (d ε) η β K
    let Y := fun ε => selectedWindow (n ε) b (c ε) (d ε) η (εt ε)
    let h := fun ε => step β (M ε) (εm ε)
    ((fun ε => ((Finset.Icc (-(cutoff (Y ε) (h ε) : ℤ))
      (cutoff (Y ε) (h ε) : ℤ)).card : ℝ)) =O[𝓝[>] 0]
        (fun ε => Real.log (1 / ε) * Real.log (Real.log (1 / ε)))) ∧
    ((fun ε => η * Real.sinh (h ε * cutoff (Y ε) (h ε))) =O[𝓝[>] 0]
      (fun ε => Real.log (1 / ε))) := by
  let l := 𝓝[>] (0 : ℝ)
  let L := fun ε : ℝ => Real.log (1 / ε)
  let M := fun ε => stripMass (n ε) b (c ε) (d ε) η β K
  let C := fun ε => tailConstant (n ε) b (c ε) (d ε)
  let ℓm := fun ε => meshLog (M ε) (εm ε)
  let ℓt := fun ε => tailLog (C ε) (εt ε)
  have hLtop : Tendsto L l atTop := by
    change Tendsto (Real.log ∘ (fun x : ℝ => 1 / x)) (𝓝[>] 0) atTop
    apply Real.tendsto_log_atTop.comp
    convert! (tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop) using 1
    funext x
    rw [one_div]
  have hL0 : ∀ᶠ ε in l, 0 ≤ L ε := hLtop.eventually_ge_atTop 0
  obtain ⟨J, hJ, hlogs⟩ :=
      eventual_profile_logs N b η β K D hb hη hβ.le hβπ hK hD hgap hNb n c d εm εt ha hmpos htpos hmO htO hcO
  have hgeom := uniform_geometry_isBigO l c (fun _ => η) (fun _ => β) M C εm εt (by
    filter_upwards [ha, hmpos, hlogs] with ε ha hm hl
    exact ⟨ha.2.1, hη, ha.2.2.1, hβ, hl.2.2.1, hm⟩)
  have hmt : ℓm =O[l] L := by
    apply IsBigO.of_bound J
    filter_upwards [hlogs, hmpos] with ε hl hm
    have hp := meshLog_pos hl.2.2.1 hm
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp,
        abs_of_nonneg (by dsimp [L]; linarith [hl.2.1])]
    exact hl.2.2.2.2.1
  have htt : ℓt =O[l] L := by
    apply IsBigO.of_bound J
    filter_upwards [hlogs] with ε hl
    have hp : 0 ≤ ℓt ε := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp,
        abs_of_nonneg (by dsimp [L]; linarith [hl.2.1])]
    exact hl.2.2.2.2.2
  have hprod : (fun ε => c ε * Real.sqrt (ℓt ε)) =O[l] L := by
    have hp := hcO.mul (htt.sqrt hL0)
    apply hp.congr' (Eventually.of_forall (fun _ => rfl))
    filter_upwards [hL0] with ε hε
    exact Real.mul_self_sqrt hε
  have huO : (fun ε => 2 * c ε / η * Real.sqrt (ℓt ε)) =O[l] L :=
    (hprod.const_mul_left (2 / η)).congr_left (fun ε => by ring)
  have hu0 : ∀ᶠ ε in l, 0 ≤ 2 * c ε / η * Real.sqrt (ℓt ε) := by
    filter_upwards [ha] with ε ha
    have hcp := ha.2.1
    positivity
  have hlogO := log_one_add_isBigO hu0 huO hLtop
  have h1L : (fun _ : ℝ => (1 : ℝ)) =O[l] L := by
    simpa only [Function.comp_def, id_eq] using!
        (isLittleO_const_id_atTop (1 : ℝ)).isBigO.comp_tendsto hLtop
  have h1log : (fun _ : ℝ => (1 : ℝ)) =O[l] (fun ε => Real.log (L ε)) := by
    simpa only [Function.comp_def] using!
        (Real.isLittleO_const_log_atTop (c := 1)).isBigO.comp_tendsto hLtop
  have hmesh : (fun ε => 1 + ℓm ε / β) =O[l] L :=
    (h1L.add (hmt.const_mul_left (1 / β))).congr_left (fun ε => by ring)
  have hshape : (fun ε => 1 + Real.log (1 + 2 * c ε / η * Real.sqrt (ℓt ε)) * (1 + ℓm ε / β)) =O[l]
      (fun ε => L ε * Real.log (L ε)) := by
    have h1 := (h1L.mul h1log).congr_left (fun _ => one_mul (1 : ℝ))
    have hp := (hlogO.mul hmesh).congr_right (fun _ => mul_comm _ _)
    exact h1.add hp
  have hrad : (fun ε => c ε * Real.sqrt (ℓt ε) + η) =O[l] L :=
    hprod.add (by simpa only [Function.comp_def, id_eq] using! (isLittleO_const_id_atTop η).isBigO.comp_tendsto hLtop)
  exact ⟨hgeom.1.trans hshape, hgeom.2.trans hrad⟩

/-- For positive `b` and `η`, there is an angle `β` strictly between zero and `π / 4` such that
`η * Real.sin β < min 1 b`. -/
theorem exists_fixed_width (b η : ℝ) (hb : 0 < b) (hη : 0 < η) :
    ∃ β : ℝ, 0 < β ∧ β < Real.pi / 4 ∧ η * Real.sin β < min 1 b := by
  let β := min (Real.pi / 8) (min 1 b / (2 * η))
  have hm : 0 < min (1 : ℝ) b := lt_min (by norm_num) hb
  have hp : 0 < β := by dsimp [β]; positivity
  have hβπ : β < Real.pi / 4 := (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  have hβm : β ≤ min 1 b / (2 * η) := min_le_right _ _
  have hmul := (le_div_iff₀ (by positivity : 0 < 2 * η)).mp hβm
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le hp.le) hη.le
  exact ⟨β, hp, hβπ, by nlinarith⟩

open Complex Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

/-- Chooses a positive strip angle below `π / 4` satisfying the pole-separation bound and lying
below `analyticWidth` for every choice of kernel order, scale, shift, time, and matrices.
This supplies a uniform strip width for the sinh quadrature analysis in
[AftabAnTrivisa2026]. -/
theorem exists_uniform_width (b η : ℝ) (hb : 0 < b) (hη : 0 < η) :
    ∃ β : ℝ, 0 < β ∧ β < Real.pi / 4 ∧ η * Real.sin β < min 1 b ∧
      ∀ (n : ℕ) (c d T : ℝ) (H L : Matrix ι ι ℂ),
        (β : EReal) < analyticWidth n b c d T η H L := by
  obtain ⟨β, hp, hπ, hg⟩ := exists_fixed_width b η hb hη
  refine ⟨β, hp, hπ, hg, fun n c d T H L => ?_⟩
  exact lt_width_of_gaps n hη hp.le (by linarith [Real.pi_pos]) b c d T H L
    (hg.trans_le (min_le_left _ _)) (Or.inr (hg.trans_le (min_le_right _ _)))

/-- For eventually bounded orders and positive scales and budgets, the selected sinh rule
eventually has positive step size and operator error at most `εm ε + εt ε`, under the stated
matrix and strip conditions. -/
theorem profile_selected_error [Nonempty ι] (N : ℕ) (b η β T : ℝ)
    (hb : 0 < b) (hη : 0 < η) (hβ : 0 < β) (hβπ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hNb : N = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) (hT : 0 ≤ T)
    (n : ℝ → ℕ) (c d εm εt : ℝ → ℝ)
    (ha : ∀ᶠ ε : ℝ in 𝓝[>] 0, n ε ≤ N ∧ 0 < c ε)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      let h := step β (stripMass (n ε) b (c ε) (d ε) η β (T * ‖L‖)) (εm ε)
      let Y := selectedWindow (n ε) b (c ε) (d ε) η (εt ε)
      0 < h ∧ ‖(∫ k : ℝ, integrand (n ε) b (c ε) (d ε) T H L (k : ℂ)) -
        finiteIdeal (n ε) b (c ε) (d ε) T η h H L
          (cutoff Y h)‖ ≤ εm ε + εt ε := by
  filter_upwards [ha, hmpos, htpos] with ε ha hm ht
  have hbn : n ε = 0 ∨ η * Real.sin β < b := by
    rcases hNb with hN | hg
    · exact Or.inl (by omega)
    · exact Or.inr hg
  exact selected_error (n ε) b (c ε) (d ε) η β hb ha.2 hη hβ hβπ H L hH hL hT hm ht
    (lt_width_of_gaps (n ε) hη hβ.le (by linarith [Real.pi_pos]) b (c ε) (d ε) T H L hgap hbn)

/-- Combines the eventual error bound for the selected sinh rule with `O(log(1/ε)
log(log(1/ε)))` nodes and `O(log(1/ε))` physical radius under the stated profile hypotheses.
See [AftabAnTrivisa2026]. -/
theorem kernel_profile_bounds [Nonempty ι] (N : ℕ) (b η β T D : ℝ)
    (hb : 0 < b) (hη : 0 < η) (hβ : 0 < β) (hβπ : β < Real.pi / 4)
    (hD : 0 ≤ D) (hgap : η * Real.sin β < 1) (hNb : N = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) (hT : 0 ≤ T)
    (n : ℝ → ℕ) (c d εm εt : ℝ → ℝ)
    (ha : ∀ᶠ ε : ℝ in 𝓝[>] 0, n ε ≤ N ∧ 0 < c ε ∧ η ≤ 2 * c ε ∧ |d ε| ≤ D)
    (hmpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εm ε)
    (htpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < εt ε)
    (hmO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εm)
    (htO : (fun ε : ℝ => ε) =O[𝓝[>] 0] εt)
    (hcO : c =O[𝓝[>] 0] (fun ε => Real.sqrt (Real.log (1 / ε)))) :
    let M := fun ε => stripMass (n ε) b (c ε) (d ε) η β (T * ‖L‖)
    let Y := fun ε => selectedWindow (n ε) b (c ε) (d ε) η (εt ε)
    let h := fun ε => step β (M ε) (εm ε)
    (∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < h ε ∧
      ‖(∫ k : ℝ, integrand (n ε) b (c ε) (d ε) T H L (k : ℂ)) -
        finiteIdeal (n ε) b (c ε) (d ε) T η (h ε) H L
          (cutoff (Y ε) (h ε))‖ ≤ εm ε + εt ε) ∧
    ((fun ε => ((Finset.Icc (-(cutoff (Y ε) (h ε) : ℤ))
      (cutoff (Y ε) (h ε) : ℤ)).card : ℝ)) =O[𝓝[>] 0]
        (fun ε => Real.log (1 / ε) * Real.log (Real.log (1 / ε)))) ∧
    ((fun ε => η * Real.sinh (h ε * cutoff (Y ε) (h ε))) =O[𝓝[>] 0]
      (fun ε => Real.log (1 / ε))) := by
  have herr := profile_selected_error N b η β T hb hη hβ hβπ hgap hNb H L hH hL hT
    n c d εm εt (ha.mono fun _ h => ⟨h.1, h.2.1⟩) hmpos htpos
  have hcost := profile_rates N b η β (T * ‖L‖) D hb hη hβ hβπ (mul_nonneg hT (norm_nonneg _)) hD
    hgap hNb n c d εm εt ha hmpos htpos hmO htO hcO
  exact ⟨herr, hcost⟩

/-- If a positive approximation budget is asymptotically comparable to `ε`, then its square-root
logarithm is `O(sqrt(log(1/ε)))` as `ε` tends to zero from above. This transfers the
comparable-budget scale used in [AftabAnTrivisa2026]. -/
theorem sqrt_log_comparable_budget (a : ℝ → ℝ)
    (ha : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < a ε)
    (hΘ : a =Θ[𝓝[>] 0] (fun ε : ℝ => ε)) :
    (fun ε => Real.sqrt (Real.log (1 / a ε))) =O[𝓝[>] 0]
      (fun ε : ℝ => Real.sqrt (Real.log (1 / ε))) := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hatop := hΘ.1.trans_tendsto he
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, a ε < 1 := hatop.eventually (Iio_mem_nhds (by norm_num))
  have hlogs := Qatlib.Papers.CommutLCHS26.QuadratureCmp.BudgetRates.eventual_budget_logs
    1 1 (by norm_num) (by norm_num) a a ha ha hΘ.2 hΘ.2
  have hlogO : (fun ε => Real.log (1 / a ε)) =O[𝓝[>] 0] (fun ε : ℝ => Real.log (1 / ε)) := by
    apply IsBigO.of_bound 2
    filter_upwards [ha, hsmall, hlogs] with ε ha hs hl
    have hinv : 1 ≤ 1 / a ε := (le_div_iff₀ ha).mpr (by linarith)
    have hp : 0 ≤ Real.log (1 / a ε) := Real.log_nonneg hinv
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp,
      abs_of_nonneg (by linarith [hl.2.2.2] : 0 ≤ Real.log (1 / ε))]
    exact (le_max_right (1 : ℝ) (Real.log (1 / a ε))).trans hl.2.2.1
  apply hlogO.sqrt
  filter_upwards [hlogs] with ε hl
  change (0 : ℝ) ≤ Real.log (1 / ε)
  linarith [hl.2.2.2]

/-- Transfers a square-root logarithmic bound for `c` from an eventually positive budget
comparable to `ε` to the reference budget `ε`. This supplies a scale conversion for the
quadrature profiles in [AftabAnTrivisa2026]. -/
theorem width_growth_of_balanced_approx (a c : ℝ → ℝ)
    (ha : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < a ε)
    (hΘ : a =Θ[𝓝[>] 0] (fun ε : ℝ => ε))
    (hc : c =O[𝓝[>] 0] (fun ε => Real.sqrt (Real.log (1 / a ε)))) :
    c =O[𝓝[>] 0] (fun ε : ℝ => Real.sqrt (Real.log (1 / ε))) :=
  hc.trans (sqrt_log_comparable_budget a ha hΘ)

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhProfile
