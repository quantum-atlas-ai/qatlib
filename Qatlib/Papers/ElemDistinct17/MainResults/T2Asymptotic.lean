/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ElemDistinct17.MainResults.ReducedSubspace
public import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonPhaseAsymptoticQuan
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Asymptotic scale of the second walk duration

The phase in Eq. (19) is the Johnson-walk eigenphase. Its normalized limit
gives the leading term in Eq. (26) when the walk radius is asymptotic to
`N ^ (k / (k + 1))`, which includes the nearest-integer choice of §2.1. For at least three marked
elements the finite-size correction makes the additive remainder unbounded.
-/

set_option autoImplicit false

open Filter
open scoped Topology
open Qatlib.Papers.ElemDistinct17.MainResults

namespace Qatlib.Papers.ElemDistinct17.MainResults

/-- The reduced phase in Eq. (19) is the corresponding Johnson-walk phase. -/
theorem phi_eq_johnson (k N r : ℕ) :
    phi N r k = Qatlib.Concepts.WalkFind.SearchAlgorithm.johnsonPhase k N r := by
  unfold phi cosPhi Qatlib.Concepts.WalkFind.SearchAlgorithm.johnsonPhase
  congr 1
  ring

/-- Rounding a growing positive power by a bounded additive error preserves its leading term. -/
theorem radius_ratio_of_bounded_rounding {a : ℝ} (ha : 0 < a) (r : ℕ → ℕ) (C : ℝ)
    (hround : ∀ᶠ N : ℕ in atTop, |(r N : ℝ) - (N : ℝ) ^ a| ≤ C) :
    Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ a) atTop (𝓝 1) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun N : ℕ => (1 : ℝ) + C / (N : ℝ) ^ a) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hN.const_div_atTop C)
  have hlower : Tendsto (fun N : ℕ => (1 : ℝ) - C / (N : ℝ) ^ a) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hN.const_div_atTop C)
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < (N : ℝ) ^ a :=
    hN.eventually (eventually_gt_atTop 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hround, hpos] with N h hp
    rw [sub_div' hp.ne', one_mul, div_le_div_iff_of_pos_right hp]
    linarith [(abs_le.mp h).1]
  · filter_upwards [hround, hpos] with N h hp
    rw [add_div' C 1 _ hp.ne', one_mul, div_le_div_iff_of_pos_right hp]
    linarith [(abs_le.mp h).2]

/-- A radius asymptotic to a positive power grows unboundedly, while its fraction of the
input tends to zero when the exponent is less than one. -/
private theorem radius_limits {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (r : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ a) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (r N : ℝ)) atTop atTop ∧
      Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp hNat
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) := hNat.eventually (eventually_gt_atTop 0)
  have hratio : ∀ᶠ N in atTop, (1 / 2 : ℝ) < (r N : ℝ) / (N : ℝ) ^ a :=
    hr.eventually (eventually_gt_nhds (by norm_num))
  constructor
  · refine tendsto_atTop_mono' _ ?_ (hpow.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hNpos, hratio] with N hN h
    exact ((lt_div_iff₀ (Real.rpow_pos_of_pos hN _)).mp h).le
  · have hscale : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - a))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr ha1)).comp hNat
    have h := hr.mul hscale
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [hNpos] with N hN
    rw [show -(1 - a) = a - 1 by ring, Real.rpow_sub_one hN.ne']
    field_simp [Real.rpow_pos_of_pos hN a |>.ne', hN.ne']

/-- The ratio of the exact second walk duration to the leading term of Eq. (26)
tends to one for the radius scale of §2.1. -/
theorem t2Opt_ratio_tendsto (k : ℕ) (hk : 0 < k) (r : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ ((k : ℝ) / (k + 1))) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => t2Opt k N (r N) / (Real.pi * Real.sqrt (r N : ℝ) /
      (2 * Real.sqrt (k : ℝ)))) atTop (𝓝 1) := by
  let a : ℝ := (k : ℝ) / (k + 1)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < a := div_pos hkR (by positivity)
  have ha1 : a < 1 := (div_lt_one (by positivity)).2 (by linarith)
  change Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ a) atTop (𝓝 1) at hr
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨hrInf, hsmall⟩ := radius_limits ha ha1 r hr
  have hp := Qatlib.Concepts.WalkFind.WalkSpectrum.johnsonPhaseAsymptotic_answer
  change Qatlib.Concepts.WalkFind.SearchAlgorithm.JohnsonPhaseAsymptoticContract at hp
  have hinv := (hp k hk id r hNat hrInf hsmall).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  rw [inv_one] at hinv
  apply hinv.congr'
  filter_upwards [hrInf.eventually (eventually_gt_atTop 0)] with N hR
  change (Qatlib.Concepts.WalkFind.SearchAlgorithm.johnsonPhase k N (r N) /
    (2 * Real.sqrt ((k : ℝ) / (r N : ℝ))))⁻¹ = _
  rw [← phi_eq_johnson, inv_div, t2Opt_eq, Real.sqrt_div hkR.le]
  have hkr : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hkR).ne'
  have hrr : Real.sqrt (r N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  by_cases hphase : phi N (r N) k = 0
  · simp [hphase]
  · field_simp [Real.pi_ne_zero, hkr, hrr, hphase]

/-- The inverse-sine bound applied to the exact reduced phase gives a finite-size
upper bound on the optimal second walk duration. -/
theorem t2Opt_le_phase_scale (k N r : ℕ) (hk : 0 < k) (hkr : k ≤ r) (hhalf : 2 * r ≤ N)
    (hgap : k < N - r) :
    t2Opt k N r ≤ Real.pi / (2 * Real.sqrt (k : ℝ)) *
      Real.sqrt (((r : ℝ) + 1) * ((N : ℝ) - r) / ((N : ℝ) - k + 1)) := by
  let B : ℝ := ((r : ℝ) + 1) * ((N : ℝ) - r) / ((N : ℝ) - k + 1)
  let θ := phi N r k / 2
  have hrN : r < N := by omega
  have hkN : k ≤ N := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdiff : (0 : ℝ) < (N : ℝ) - r := sub_pos.mpr (by exact_mod_cast hrN)
  have hd : (0 : ℝ) < (N : ℝ) - k + 1 := by
    have : (k : ℝ) ≤ N := by exact_mod_cast hkN
    linarith
  have hB : 0 < B := div_pos (mul_pos (by positivity) hdiff) hd
  have hφ := phi_mem_Ioo N r k hkN hkr hrN hhalf hk hgap
  have hθ : 0 < θ := half_pos hφ.1
  have hθπ : θ ≤ Real.pi := by dsimp [θ]; linarith [hφ.2, Real.pi_pos]
  have hcos : Real.cos (2 * θ) = 1 - 2 * (k : ℝ) / B := by
    rw [show 2 * θ = phi N r k by dsimp [θ]; ring]
    have hc := cosPhi_mem_Icc N r k hkN hkr hrN hhalf
    rw [phi, Real.cos_arccos hc.1 hc.2]
    dsimp [cosPhi, B]
    field_simp [hd.ne', hdiff.ne', (show (r : ℝ) + 1 ≠ 0 by positivity)]
  have hsin : Real.sin θ = Real.sqrt ((k : ℝ) / B) := by
    rw [Real.cos_two_mul] at hcos
    have hs : Real.sin θ ^ 2 = (k : ℝ) / B := by
      linear_combination Real.sin_sq_add_cos_sq θ - hcos / 2
    rw [← hs, Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi hθ.le hθπ)]
  have hs : Real.sqrt (k : ℝ) / Real.sqrt B ≤ θ := by
    rw [← Real.sqrt_div hkR.le, ← hsin]
    exact Real.sin_le hθ.le
  have hsB := Real.sqrt_pos.mpr hB
  have hsk := Real.sqrt_pos.mpr hkR
  rw [t2Opt_eq, show phi N r k = 2 * θ by dsimp [θ]; ring]
  change Real.pi / (2 * θ) ≤ Real.pi / (2 * Real.sqrt (k : ℝ)) * Real.sqrt B
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos two_pos hθ) (mul_pos two_pos hsk)]
  have hh := (div_le_iff₀ hsB).mp hs
  nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]

/-- When the squared radius dominates the input size, the finite-size correction places the
exact second duration below its nominal leading term by at least a multiple of `r√r/N`. -/
theorem t2Opt_sub_le (k N r : ℕ) (hk : 0 < k) (hsize : 2 * k ≤ r) (hhalf : 2 * r ≤ N)
    (hquad : 4 * N ≤ r ^ 2) :
    t2Opt k N r - Real.pi * Real.sqrt (r : ℝ) / (2 * Real.sqrt (k : ℝ)) ≤
      -(Real.pi / (16 * Real.sqrt (k : ℝ))) * ((r : ℝ) * Real.sqrt (r : ℝ) / (N : ℝ)) := by
  let D : ℝ := (N : ℝ) - k + 1
  let B : ℝ := ((r : ℝ) + 1) * ((N : ℝ) - r) / D
  let s : ℝ := Real.sqrt (r : ℝ)
  let u : ℝ := Real.sqrt B
  have hkr : k ≤ r := by omega
  have hgap : k < N - r := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : 2 * (k : ℝ) ≤ r := by exact_mod_cast hsize
  have hqR : 4 * (N : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hquad
  have hrN : (r : ℝ) < N := by exact_mod_cast (show r < N by omega)
  have hD : 0 < D := by dsimp [D]; linarith
  have hDN : D ≤ (N : ℝ) := by dsimp [D]; linarith
  have hB : 0 ≤ B := by
    exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hrN.le)) hD.le
  have hBd : B * D = ((r : ℝ) + 1) * ((N : ℝ) - r) := div_mul_cancel₀ _ hD.ne'
  have hnum : (r : ℝ) ^ 2 / 4 ≤ ((r : ℝ) - B) * D := by
    rw [sub_mul, hBd]
    dsimp [D]
    nlinarith [mul_nonneg hR.le (show 0 ≤ (r : ℝ) - 2 * k by linarith)]
  have hBr : B ≤ r := by
    apply sub_nonneg.mp
    exact nonneg_of_mul_nonneg_left ((by positivity : 0 ≤ (r : ℝ) ^ 2 / 4).trans hnum) hD
  have hus : u ≤ s := Real.sqrt_le_sqrt hBr
  have hs : 0 < s := Real.sqrt_pos.mpr hR
  have hss : s ^ 2 = (r : ℝ) := Real.sq_sqrt hR.le
  have huu : u ^ 2 = B := Real.sq_sqrt hB
  have hgap' : (r : ℝ) ^ 2 / 4 ≤ (2 * s * (s - u)) * (N : ℝ) := calc
    _ ≤ ((r : ℝ) - B) * D := hnum
    _ ≤ ((r : ℝ) - B) * (N : ℝ) := mul_le_mul_of_nonneg_left hDN (sub_nonneg.mpr hBr)
    _ = ((s - u) * (s + u)) * (N : ℝ) := by rw [← hss, ← huu]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      rw [mul_comm (2 * s)]
      exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hus)) hN.le
  have hroot : (r : ℝ) * s / (8 * (N : ℝ)) ≤ s - u := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hN)]
    apply le_of_mul_le_mul_left _ hs
    calc
      _ = (r : ℝ) ^ 2 := by linear_combination (r : ℝ) * hss
      _ ≤ ((2 * s * (s - u)) * (N : ℝ)) * 4 := by linarith
      _ = _ := by ring
  have ht := t2Opt_le_phase_scale k N r hk hkr hhalf hgap
  change t2Opt k N r ≤ Real.pi / (2 * Real.sqrt (k : ℝ)) * u at ht
  have hmul := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ Real.pi / (2 * Real.sqrt (k : ℝ)) by positivity)
  change t2Opt k N r - Real.pi * s / (2 * Real.sqrt (k : ℝ)) ≤
    -(Real.pi / (16 * Real.sqrt (k : ℝ))) * ((r : ℝ) * s / (N : ℝ))
  have heq : Real.pi / (2 * Real.sqrt (k : ℝ)) * ((r : ℝ) * s / (8 * (N : ℝ))) =
      (Real.pi / (16 * Real.sqrt (k : ℝ))) * ((r : ℝ) * s / (N : ℝ)) := by ring
  rw [heq, mul_sub, div_mul_eq_mul_div _ _ s] at hmul
  rw [neg_mul]
  linarith

/-- Raising the radius to an exponent whose product with the radius exponent exceeds one
gives a power growing faster than the input size. -/
private theorem radius_power_over_input {a b : ℝ} (hab : 1 < a * b) (r : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ a) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (r N : ℝ) ^ b / (N : ℝ)) atTop atTop := by
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : ℕ => ((r N : ℝ) / (N : ℝ) ^ a) ^ b) atTop (𝓝 1) := by
    simpa using hr.rpow_const (p := b) (Or.inl one_ne_zero)
  have hratio' : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) ≤ ((r N : ℝ) / (N : ℝ) ^ a) ^ b :=
    (hratio.eventually (eventually_gt_nhds (by norm_num))).mono fun _ h => h.le
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (a * b - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hNat
  refine tendsto_atTop_mono' _ ?_ (hpow.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hNat.eventually (eventually_gt_atTop 0), hratio'] with N hN h
  calc
    _ ≤ ((r N : ℝ) / (N : ℝ) ^ a) ^ b * (N : ℝ) ^ (a * b - 1) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.rpow_sub_one hN.ne', Real.div_rpow (by positivity) (Real.rpow_nonneg hN.le a),
        Real.rpow_mul hN.le]
      field_simp [(Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN a) b).ne', hN.ne']

/-- For at least three marked elements and the radius scale in §2.1, the difference
between the exact second duration and the leading term in Eq. (26) tends to negative
infinity. Thus the stated additive `O(1)` remainder fails in this regime. -/
theorem t2Opt_sub_tendsto_atBot (k : ℕ) (hk : 3 ≤ k) (r : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ ((k : ℝ) / (k + 1))) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => t2Opt k N (r N) - Real.pi * Real.sqrt (r N : ℝ) /
      (2 * Real.sqrt (k : ℝ))) atTop atBot := by
  let a : ℝ := (k : ℝ) / (k + 1)
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < k := by omega
  have hkRp : (0 : ℝ) < k := by linarith
  have ha : 0 < a := div_pos hkRp (by positivity)
  have ha1 : a < 1 := (div_lt_one (by positivity)).2 (by linarith)
  change Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ a) atTop (𝓝 1) at hr
  obtain ⟨hInf, hsmall⟩ := radius_limits ha ha1 r hr
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 * k ≤ r N := by
    filter_upwards [hInf.eventually (eventually_ge_atTop (2 * (k : ℝ)))] with N h
    exact_mod_cast h
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N := hNat.eventually (eventually_gt_atTop 0)
  have hhalf : ∀ᶠ N : ℕ in atTop, 2 * r N ≤ N := by
    filter_upwards [hpos, hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with N hN h
    have hR := (div_lt_iff₀ hN).mp h
    exact_mod_cast (show 2 * (r N : ℝ) ≤ N by linarith)
  have ha3 : 1 < a * (3 / 2) := by
    dsimp [a]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    linarith
  have ha2 : 1 < a * 2 := by linarith
  have hquad : ∀ᶠ N : ℕ in atTop, 4 * N ≤ r N ^ 2 := by
    filter_upwards [hpos, (radius_power_over_input ha2 r hr).eventually (eventually_ge_atTop 4)]
      with N hN h
    rw [Real.rpow_two] at h
    exact_mod_cast (le_div_iff₀ hN).mp h
  have hscale : Tendsto (fun N : ℕ => (r N : ℝ) * Real.sqrt (r N : ℝ) / (N : ℝ))
      atTop atTop := by
    apply (radius_power_over_input ha3 r hr).congr
    intro N
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg (by positivity) zero_le_one (by norm_num), Real.rpow_one]
  have hc : 0 < Real.pi / (16 * Real.sqrt (k : ℝ)) := by positivity
  have hbound := tendsto_neg_atTop_atBot.comp (hscale.const_mul_atTop hc)
  apply tendsto_atBot_mono' _ _ hbound
  filter_upwards [hlarge, hhalf, hquad] with N hL hH hQ
  simpa only [Function.comp_apply, neg_mul] using t2Opt_sub_le k N (r N) hk0 hL hH hQ

/-- The nearest-integer radius of §2.1 tends to its specified real power in ratio. -/
theorem nearest_radius_ratio (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      ((round ((N : ℝ) ^ ((k : ℝ) / (k + 1)))).toNat : ℝ) /
        (N : ℝ) ^ ((k : ℝ) / (k + 1))) atTop (𝓝 1) := by
  let a : ℝ := (k : ℝ) / (k + 1)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine radius_ratio_of_bounded_rounding (a := a) (div_pos hkR (by positivity))
    (fun N => (round ((N : ℝ) ^ a)).toNat) (1 / 2) (Eventually.of_forall ?_)
  intro N
  have hnonneg : (0 : ℤ) ≤ round ((N : ℝ) ^ a) := by
    rw [round_eq]
    exact Int.floor_nonneg.2 (by positivity)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg, abs_sub_comm]
  exact abs_sub_round ((N : ℝ) ^ a)

/-- The constant absolute remainder asserted in Eq. (26) cannot hold when
there are at least three marked elements at the paper's radius scale. -/
theorem t2Opt_remainder_unbounded (k : ℕ) (hk : 3 ≤ k) (r : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (r N : ℝ) / (N : ℝ) ^ ((k : ℝ) / (k + 1))) atTop (𝓝 1)) :
    ¬ ∃ C : ℝ, ∀ᶠ N in atTop, |t2Opt k N (r N) - Real.pi * Real.sqrt (r N : ℝ) /
      (2 * Real.sqrt (k : ℝ))| ≤ C := by
  rintro ⟨C, hC⟩
  have h := (t2Opt_sub_tendsto_atBot k hk r hr).eventually (eventually_lt_atBot (-C))
  obtain ⟨N, hCN, hN⟩ := (hC.and h).exists
  exact not_lt_of_ge (abs_le.mp hCN).1 hN

end Qatlib.Papers.ElemDistinct17.MainResults
