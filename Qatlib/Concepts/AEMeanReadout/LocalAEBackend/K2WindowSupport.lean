/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# Wider phase-estimation success windows

This module relates local phase distance and QPE kernel masses to the BHMT phase-estimation
quantities of [BrassardEtAl2002]. A phase outcome within distance `k / M` yields an amplitude
estimate with an explicit error bound, and the phase-estimation tail estimate supplies a success
bound for `k ≥ 2`.

## Main statements

* `bhmt_k2_estimate_error`: turn a phase-window bound into an amplitude-estimation error bound.
* `bhmt_k2_qpe_success`: bound the mass of the resulting amplitude-estimation success event.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- The local phase distance equals the BHMT circular distance with the arguments in the
opposite order. -/
theorem bhmt_k2_distance_bridge (φ x : ℝ) :
    phaseDistance φ x = bhmt11CircleDist x φ := by
  rw [bhmt_phase_estimation_theorem11_distance_round, round_eq]
  rfl

/-- For a positive register size, the squared norm of a QPE kernel amplitude equals the
corresponding BHMT outcome mass. -/
theorem bhmt_k2_kernel_mass_bridge (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 0 < M) :
    ‖qpeKernel M φ z‖^2 = bhmt11OutcomeMass M φ z := by
  have he : qpeKernel M φ z = ((bhmt11QFT M)ᴴ *ᵥ bhmt11PhaseState M φ) z := by
    rw [(offgrid_phase_kernel_formula M φ z hM).2.1,
      bhmt_phase_estimation_theorem11_amplitude M φ hM z]
    congr 1
    unfold bhmt_phase_estimation_theorem11_expSum
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    push_cast
    ring
  rw [he]
  rfl

/-- The sum of QPE kernel masses in a circular phase window equals the BHMT window mass. -/
theorem bhmt_k2_window_mass_bridge (M : ℕ) (φ r : ℝ) (hM : 0 < M) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin M => phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ r),
      ‖qpeKernel M φ z‖^2) = bhmt11WindowMass M φ r := by
  rw [Finset.sum_filter]
  unfold bhmt11WindowMass
  apply Finset.sum_congr rfl
  intro z _
  rw [bhmt_k2_distance_bridge, bhmt_k2_kernel_mass_bridge M φ z hM]

/-- The change in squared sine under displacement `t` is at most `2√(sin² θ (1 - sin² θ)) |t| +
t²`. -/
private theorem bhmt_k2_sin_sq_displacement (θ t : ℝ) :
    |Real.sin (θ+t)^2-Real.sin θ^2| ≤
      2*Real.sqrt (Real.sin θ^2*(1-Real.sin θ^2))*|t|+t^2 := by
  have hi := Real.sin_sq_add_cos_sq θ
  have ht := Real.abs_sin_le_abs (x := t)
  have hc := Real.abs_cos_le_one t
  have hdiff : |Real.cos θ^2-Real.sin θ^2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
  have he : Real.sin (θ+t)^2-Real.sin θ^2 =
      2*Real.sin θ*Real.cos θ*Real.sin t*Real.cos t+
        (Real.cos θ^2-Real.sin θ^2)*Real.sin t^2 := by
    rw [Real.sin_add]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hsqrt : Real.sqrt (Real.sin θ^2*(1-Real.sin θ^2)) = |Real.sin θ*Real.cos θ| := by
    rw [show Real.sin θ^2*(1-Real.sin θ^2) = (Real.sin θ*Real.cos θ)^2 by nlinarith only [hi]]
    exact Real.sqrt_sq_eq_abs _
  rw [hsqrt, he]
  calc
    _ ≤ |2*Real.sin θ*Real.cos θ*Real.sin t*Real.cos t|+
        |(Real.cos θ^2-Real.sin θ^2)*Real.sin t^2| := abs_add_le _ _
    _ ≤ 2 * |Real.sin θ * Real.cos θ| * |t| + t^2 := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have h₁ : 2 * |Real.sin θ * Real.cos θ| * |Real.sin t| * |Real.cos t| ≤
          2 * |Real.sin θ * Real.cos θ| * |t| := by
        calc
          _ ≤ 2 * |Real.sin θ * Real.cos θ| * |t| * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left ht (by positivity)) hc
              (abs_nonneg _) (by positivity)
          _ = _ := by ring
      have h₂ : |Real.cos θ^2-Real.sin θ^2| * |Real.sin t|^2 ≤ t^2 := by
        calc
          _ ≤ 1*|t|^2 := mul_le_mul hdiff (pow_le_pow_left₀ (abs_nonneg _) ht 2)
            (by positivity) (by norm_num)
          _ = _ := by rw [sq_abs, one_mul]
      simpa only [abs_mul, mul_assoc] using add_le_add h₁ h₂

/-- Squared sine is unchanged by an integer multiple of `π`. -/
private theorem bhmt_k2_sin_sq_integer_shift (t : ℝ) (n : ℤ) :
    Real.sin (t+(n : ℝ)*Real.pi)^2 = Real.sin t^2 := by
  rw [Real.sin_add_int_mul_pi, mul_pow]
  have hs : ((-1 : ℝ)^n)^2 = 1 := by rw [← sq_abs, abs_zpow]; norm_num
  rw [hs, one_mul]

/-- A phase-distance bound `k / M` gives amplitude error at most `2πk√(a(1 - a))/M + k²π²/M²`,
where `a = sin²(πφ)` [BrassardEtAl2002]. -/
theorem bhmt_k2_estimate_error (M : ℕ) (hM : 0 < M) (φ : ℝ) (z : Fin M) (k : ℕ)
    (hd : phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ (k : ℝ)/(M : ℝ)) :
    let a := Real.sin (Real.pi*φ)^2
    |aeEstimate M z-a| ≤ 2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ)+
      (k : ℝ)^2*Real.pi^2/(M : ℝ)^2 := by
  let c : ℤ := ⌊φ-(z.val : ℝ)/(M : ℝ)+1/2⌋
  let t : ℝ := Real.pi*((z.val : ℝ)/(M : ℝ)-φ+(c : ℝ))
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have he : Real.sin (Real.pi*φ+t)^2 = aeEstimate M z := by
    rw [show Real.pi*φ+t = Real.pi*(z.val : ℝ)/(M : ℝ)+(c : ℝ)*Real.pi by dsimp [t]; ring,
      bhmt_k2_sin_sq_integer_shift]
    rfl
  have ht : |t| = Real.pi*phaseDistance φ ((z.val : ℝ)/(M : ℝ)) := by
    change |Real.pi*((z.val : ℝ)/(M : ℝ)-φ+(c : ℝ))| =
      Real.pi*|φ-(z.val : ℝ)/(M : ℝ)-(c : ℝ)|
    rw [show Real.pi*((z.val : ℝ)/(M : ℝ)-φ+(c : ℝ)) =
      -Real.pi*(φ-(z.val : ℝ)/(M : ℝ)-(c : ℝ)) by ring,
      abs_mul, abs_neg, abs_of_pos Real.pi_pos]
  have ht' : |t| ≤ Real.pi*(k : ℝ)/(M : ℝ) := by
    rw [ht]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hd Real.pi_pos.le
  have h := bhmt_k2_sin_sq_displacement (Real.pi*φ) t
  rw [he] at h
  (try dsimp only)
  calc
    _ ≤ 2*Real.sqrt (Real.sin (Real.pi*φ)^2*(1-Real.sin (Real.pi*φ)^2))*|t|+t^2 := h
    _ ≤ 2*Real.sqrt (Real.sin (Real.pi*φ)^2*(1-Real.sin (Real.pi*φ)^2))*
        (Real.pi*(k : ℝ)/(M : ℝ))+(Real.pi*(k : ℝ)/(M : ℝ))^2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left ht' (by positivity)
      · have hh := pow_le_pow_left₀ (abs_nonneg t) ht' 2
        simpa only [sq_abs] using hh
    _ = _ := by ring

/-- For `M ≥ 2` and `k ≥ 2`, the QPE mass of outcomes satisfying the stated amplitude error
bound is at least `1 - 1/(2(k - 1))` [BrassardEtAl2002]. -/
theorem bhmt_k2_qpe_success (M : ℕ) (hM : 2 ≤ M) (φ : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    let a := Real.sin (Real.pi*φ)^2
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a| ≤
        2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ)+(k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      ‖qpeKernel M φ z‖^2 ≥ 1-1/(2*((k : ℝ)-1)) := by
  have hm : 0 < M := by omega
  have hk' : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hw := bhmt_phase_estimation_theorem11_tail M φ hm (k : ℝ) hk'
  rw [← bhmt_k2_window_mass_bridge M φ ((k : ℝ)/(M : ℝ)) hm] at hw
  apply hw.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact bhmt_k2_estimate_error M hm φ z k hz
  · intro z _ _
    exact sq_nonneg _

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
