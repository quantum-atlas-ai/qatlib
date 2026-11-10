/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.AmpEstBrass00.OffGridQPE

open scoped BigOperators

theorem phaseDistance_eq_bhmt11CircleDist (x y : ℝ) :
    phaseDistance x y = bhmt11CircleDist x y := by
  have hz : |((⌊x - y + 1/2⌋ : ℤ) : ℝ)+y-x| ≤ 1/2 := by
    have h0 := Int.floor_le (x-y+1/2)
    have h1 := Int.lt_floor_add_one (x-y+1/2)
    rw [show ((⌊x - y + 1/2⌋ : ℤ) : ℝ)+y-x =
      -(x-y-((⌊x - y + 1/2⌋ : ℤ) : ℝ)) by ring, abs_neg, abs_le]
    constructor <;> linarith
  have h := bhmt_phase_estimation_theorem11_distance_small x y ⌊x - y + 1/2⌋ hz
  rw [phaseDistance, h, show x-y-((⌊x - y + 1/2⌋ : ℤ) : ℝ) =
    -(((⌊x - y + 1/2⌋ : ℤ) : ℝ)+y-x) by ring, abs_neg]

theorem phaseDistance_comm (x y : ℝ) : phaseDistance x y = phaseDistance y x := by
  rw [phaseDistance_eq_bhmt11CircleDist, phaseDistance_eq_bhmt11CircleDist,
    bhmt_phase_estimation_theorem11_distance_symm]

theorem phaseDistance_sub_right (a b c : ℝ) :
    phaseDistance (a-c) (b-c) = phaseDistance a b := by
  have h : (a-c)-(b-c) = a-b := by ring
  simp only [phaseDistance, h]

theorem offGridPhase_eq_bhmt11PhaseState (M : ℕ) (φ : ℝ) :
    offGridPhase M φ = bhmt11PhaseState M φ := by
  funext y
  rw [offGridPhase_apply]
  unfold bhmt11PhaseState
  congr 2
  push_cast
  ring

theorem qftMatrix_eq_bhmt11QFT (M : ℕ) : QFTMatrix M = bhmt11QFT M := by
  ext a b
  rw [qftMatrix_apply, primRoot_zpow_eq_exp]
  unfold bhmt11QFT
  congr 2
  push_cast
  ring

theorem qpeKernel_eq_bhmt11Amplitude (M : ℕ) (φ : ℝ) (z : Fin M) :
    qpeKernel M φ z = ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M φ)) z := by
  rw [qpeKernel_apply, ApplyGate, qftMatrix_eq_bhmt11QFT]
  exact congrFun (congrArg (fun ψ => (bhmt11QFT M).conjTranspose.mulVec ψ)
    (offGridPhase_eq_bhmt11PhaseState M φ)) z

theorem qpeKernel_norm_sq_eq_bhmt11OutcomeMass (M : ℕ) (φ : ℝ) (z : Fin M) :
    ‖qpeKernel M φ z‖^2 = bhmt11OutcomeMass M φ z := by
  rw [qpeKernel_eq_bhmt11Amplitude]
  rfl

noncomputable def offGridWindowMass (M : ℕ) (ω r : ℝ) : ℝ :=
  ∑ z : Fin M,
    if phaseDistance ω ((z.val : ℝ)/(M : ℝ)) ≤ r then ‖qpeKernel M ω z‖^2 else 0

theorem offGridWindowMass_eq_bhmt11WindowMass (M : ℕ) (ω r : ℝ) :
    offGridWindowMass M ω r = bhmt11WindowMass M ω r := by
  unfold offGridWindowMass bhmt11WindowMass
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [phaseDistance_eq_bhmt11CircleDist, qpeKernel_norm_sq_eq_bhmt11OutcomeMass,
    bhmt_phase_estimation_theorem11_distance_symm ω ((z.val : ℝ)/(M : ℝ))]

theorem offgrid_phase_total_mass (M : ℕ) (ω : ℝ) (hM : 0 < M) :
    ∑ z : Fin M, ‖qpeKernel M ω z‖^2 = 1 := by
  rw [Finset.sum_congr rfl (fun z _ => qpeKernel_norm_sq_eq_bhmt11OutcomeMass M ω z)]
  exact bhmt_phase_estimation_theorem11_normalization M ω hM

theorem offgrid_phase_grid_readout (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hgrid : ∃ j : ℤ, (M : ℝ)*ω = (j : ℝ)) :
    ∃ x : Fin M, (x.val : ℝ) = (M : ℝ)*ω ∧ ‖qpeKernel M ω x‖^2 = 1 := by
  obtain ⟨x, hx, hmass⟩ :=
    bhmt_phase_estimation_theorem11_grid M ω hM hω0 hω1 hgrid
  exact ⟨x, hx, by rw [qpeKernel_norm_sq_eq_bhmt11OutcomeMass, hmass]⟩

theorem offgrid_phase_mass_formula (M : ℕ) (ω : ℝ) (hM : 0 < M) (x : Fin M)
    (hd : 0 < phaseDistance ω ((x.val : ℝ)/(M : ℝ))) :
    ‖qpeKernel M ω x‖^2 =
      Real.sin ((M : ℝ)*phaseDistance ω ((x.val : ℝ)/(M : ℝ))*Real.pi)^2 /
        ((M : ℝ)^2*Real.sin (phaseDistance ω ((x.val : ℝ)/(M : ℝ))*Real.pi)^2) := by
  have hd' : 0 < bhmt11CircleDist ω ((x.val : ℝ)/(M : ℝ)) := by
    rw [← phaseDistance_eq_bhmt11CircleDist]
    exact hd
  rw [qpeKernel_norm_sq_eq_bhmt11OutcomeMass]
  rw [bhmt_phase_estimation_theorem11_mass_formula M ω hM x hd']
  rw [← phaseDistance_eq_bhmt11CircleDist ω ((x.val : ℝ)/(M : ℝ))]

theorem offgrid_phase_mass_bound (M : ℕ) (ω : ℝ) (hM : 0 < M) (x : Fin M)
    (hd : 0 < phaseDistance ω ((x.val : ℝ)/(M : ℝ))) :
    ‖qpeKernel M ω x‖^2 ≤
      (1 : ℝ)/(2*(M : ℝ)*phaseDistance ω ((x.val : ℝ)/(M : ℝ)))^2 := by
  have hd' : 0 < bhmt11CircleDist ω ((x.val : ℝ)/(M : ℝ)) := by
    rw [← phaseDistance_eq_bhmt11CircleDist]
    exact hd
  calc ‖qpeKernel M ω x‖^2 = bhmt11OutcomeMass M ω x :=
        qpeKernel_norm_sq_eq_bhmt11OutcomeMass M ω x
    _ ≤ (1 : ℝ)/(2*(M : ℝ)*bhmt11CircleDist ω ((x.val : ℝ)/(M : ℝ)))^2 :=
        bhmt_phase_estimation_theorem11_mass_bound M ω hM x hd'
    _ = (1 : ℝ)/(2*(M : ℝ)*phaseDistance ω ((x.val : ℝ)/(M : ℝ)))^2 := by
        rw [← phaseDistance_eq_bhmt11CircleDist ω ((x.val : ℝ)/(M : ℝ))]

theorem offgrid_phase_window_tail (M : ℕ) (ω : ℝ) (hM : 0 < M) (k : ℝ) (hk : 1 < k) :
    1 - 1/(2*(k - 1)) ≤ offGridWindowMass M ω (k/(M : ℝ)) := by
  rw [offGridWindowMass_eq_bhmt11WindowMass]
  exact bhmt_phase_estimation_theorem11_tail M ω hM k hk

theorem offgrid_phase_tail_mass (M : ℕ) (ω : ℝ) (hM : 0 < M) (k : ℝ) (hk : 1 < k) :
    ∑ z ∈ Finset.univ.filter
        (fun z : Fin M => k/(M : ℝ) < phaseDistance ω ((z.val : ℝ)/(M : ℝ))),
        ‖qpeKernel M ω z‖^2 ≤ 1/(2*(k - 1)) := by
  have htot := offgrid_phase_total_mass M ω hM
  have hwin := offgrid_phase_window_tail M ω hM k hk
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin M))
    (fun z : Fin M => phaseDistance ω ((z.val : ℝ)/(M : ℝ)) ≤ k/(M : ℝ))
    (fun z => ‖qpeKernel M ω z‖^2)
  have hwin' : ∑ z ∈ Finset.univ.filter
      (fun z : Fin M => phaseDistance ω ((z.val : ℝ)/(M : ℝ)) ≤ k/(M : ℝ)),
      ‖qpeKernel M ω z‖^2 = offGridWindowMass M ω (k/(M : ℝ)) := by
    unfold offGridWindowMass
    rw [Finset.sum_filter]
  rw [hwin', htot] at hsplit
  have hnot : (Finset.univ.filter
      (fun z : Fin M => ¬ phaseDistance ω ((z.val : ℝ)/(M : ℝ)) ≤ k/(M : ℝ))) =
      Finset.univ.filter
        (fun z : Fin M => k/(M : ℝ) < phaseDistance ω ((z.val : ℝ)/(M : ℝ))) := by
    apply Finset.filter_congr
    intro z _
    simp only [not_le]
  rw [hnot] at hsplit
  linarith

theorem offgrid_phase_window_radius_one (M : ℕ) (ω : ℝ) (hM : 2 < M)
    (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    8/Real.pi^2 ≤ offGridWindowMass M ω (1/(M : ℝ)) := by
  rw [offGridWindowMass_eq_bhmt11WindowMass]
  exact bhmt_phase_estimation_theorem11_nearest M ω hM hω0 hω1

theorem offgrid_phase_readout_theorem11 :
    ∀ (M : ℕ) (ω : ℝ), 0 < M → 0 ≤ ω → ω < 1 →
      (∑ x : Fin M, ‖qpeKernel M ω x‖^2) = 1 ∧
      ((∃ j : ℤ, (M : ℝ)*ω = (j : ℝ)) →
        ∃ x : Fin M, (x.val : ℝ) = (M : ℝ)*ω ∧ ‖qpeKernel M ω x‖^2 = 1) ∧
      ((¬ ∃ j : ℤ, (M : ℝ)*ω = (j : ℝ)) →
        ∀ x : Fin M,
          let Δ := phaseDistance ω ((x.val : ℝ)/(M : ℝ));
          ‖qpeKernel M ω x‖^2 =
            Real.sin ((M : ℝ)*Δ*Real.pi)^2/((M : ℝ)^2*Real.sin (Δ*Real.pi)^2) ∧
          ‖qpeKernel M ω x‖^2 ≤ (1 : ℝ)/(2*(M : ℝ)*Δ)^2) ∧
      (∀ k : ℝ, 1 < k → 1 - 1/(2*(k - 1)) ≤ offGridWindowMass M ω (k/(M : ℝ))) ∧
      (2 < M → 8/Real.pi^2 ≤ offGridWindowMass M ω (1/(M : ℝ))) := by
  intro M ω hM hω0 hω1
  refine ⟨offgrid_phase_total_mass M ω hM,
    offgrid_phase_grid_readout M ω hM hω0 hω1, ?_,
    fun k hk => offgrid_phase_window_tail M ω hM k hk, ?_⟩
  · intro hoff x
    have hd : 0 < phaseDistance ω ((x.val : ℝ)/(M : ℝ)) := by
      rw [phaseDistance_eq_bhmt11CircleDist]
      apply lt_of_le_of_ne (bhmt_phase_estimation_theorem11_distance_bounds _ _).1
      intro he
      exact hoff (bhmt_phase_estimation_theorem11_integral_of_distance_zero M ω hM x he.symm)
    exact ⟨offgrid_phase_mass_formula M ω hM x hd,
      offgrid_phase_mass_bound M ω hM x hd⟩
  · intro hM2
    exact offgrid_phase_window_radius_one M ω hM2 hω0 hω1

noncomputable def offGridPhaseOverlap (M : ℕ) (ω₀ ω₁ : ℝ) : ℂ :=
  ∑ y : Fin M, star (offGridPhase M ω₀ y) * offGridPhase M ω₁ y

private theorem offGridPhaseOverlap_term (M : ℕ) (hM : 0 < M) (ω₀ ω₁ : ℝ) (y : Fin M) :
    star (offGridPhase M ω₀ y) * offGridPhase M ω₁ y =
      (M : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*(ω₁ - ω₀))) := by
  have hsqrt : star ((Real.sqrt (M : ℝ) : ℂ)⁻¹) = (Real.sqrt (M : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hexp : star (Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*ω₀))) =
      Complex.exp (-(2*Real.pi*Complex.I*((y.val : ℝ)*ω₀))) := by
    change (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*ω₀))) = _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [offGridPhase_apply, offGridPhase_apply, star_mul, hsqrt, hexp]
  calc
    _ = ((Real.sqrt (M : ℝ) : ℂ)⁻¹*(Real.sqrt (M : ℝ) : ℂ)⁻¹) *
        (Complex.exp (-(2*Real.pi*Complex.I*((y.val : ℝ)*ω₀))) *
          Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*ω₁))) := by ring
    _ = (M : ℂ)⁻¹ *
        (Complex.exp (-(2*Real.pi*Complex.I*((y.val : ℝ)*ω₀))) *
          Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*ω₁))) := by
      rw [inv_sqrt_mul_inv_sqrt hM]
    _ = (M : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*((y.val : ℝ)*(ω₁ - ω₀))) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem offGridPhaseOverlap_eq_kernel_zero (M : ℕ) (hM : 0 < M) (ω₀ ω₁ : ℝ) :
    offGridPhaseOverlap M ω₀ ω₁ = qpeKernel M (ω₁ - ω₀) ⟨0, hM⟩ := by
  rw [(offgrid_phase_kernel_formula M (ω₁ - ω₀) ⟨0, hM⟩ hM).2.1]
  unfold offGridPhaseOverlap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [offGridPhaseOverlap_term M hM]
  congr 2
  simp

theorem offgrid_phase_overlap_zero_distance (M : ℕ) (hM : 0 < M) (ω₀ ω₁ : ℝ)
    (hΔ : phaseDistance ω₀ ω₁ = 0) : ‖offGridPhaseOverlap M ω₀ ω₁‖^2 = 1 := by
  have hdiff : ω₁ - ω₀ = ((-⌊ω₀ - ω₁ + 1/2⌋ : ℤ) : ℝ) := by
    have h0 : ω₀ - ω₁ - ((⌊ω₀ - ω₁ + 1/2⌋ : ℤ) : ℝ) = 0 := by
      have := hΔ
      simpa only [phaseDistance, abs_eq_zero] using this
    push_cast
    linarith
  have hk : qpeKernel M (ω₁ - ω₀) ⟨0, hM⟩ = 1 := by
    rw [hdiff, show ((-⌊ω₀ - ω₁ + 1/2⌋ : ℤ) : ℝ) =
      0 + ((-⌊ω₀ - ω₁ + 1/2⌋ : ℤ) : ℝ) from (zero_add _).symm, qpeKernel_int_add]
    have hgrid := (offgrid_phase_geometric_and_periodic M 0 ⟨0, hM⟩ hM).2.2 ⟨0, hM⟩
    simpa [Ket] using hgrid
  rw [offGridPhaseOverlap_eq_kernel_zero M hM ω₀ ω₁, hk, norm_one, one_pow]

theorem offgrid_phase_overlap_nonzero_distance (M : ℕ) (hM : 0 < M) (ω₀ ω₁ : ℝ)
    (hΔ : phaseDistance ω₀ ω₁ ≠ 0) :
    ‖offGridPhaseOverlap M ω₀ ω₁‖^2 =
      Real.sin ((M : ℝ)*phaseDistance ω₀ ω₁*Real.pi)^2 /
        ((M : ℝ)^2*Real.sin (phaseDistance ω₀ ω₁*Real.pi)^2) := by
  have hcomm : phaseDistance (ω₁ - ω₀) 0 = phaseDistance ω₀ ω₁ := by
    have h1 : phaseDistance (ω₁ - ω₀) (ω₀ - ω₀) = phaseDistance ω₁ ω₀ :=
      phaseDistance_sub_right ω₁ ω₀ ω₀
    rw [sub_self] at h1
    rw [h1, phaseDistance_comm]
  have hpos : 0 < phaseDistance ω₀ ω₁ :=
    lt_of_le_of_ne (by rw [phaseDistance]; exact abs_nonneg _) (Ne.symm hΔ)
  have hd : 0 < phaseDistance (ω₁ - ω₀) ((⟨0, hM⟩ : Fin M).val/(M : ℝ)) := by
    simp only [Nat.cast_zero, zero_div]
    rwa [hcomm]
  rw [offGridPhaseOverlap_eq_kernel_zero M hM ω₀ ω₁]
  rw [offgrid_phase_mass_formula M (ω₁ - ω₀) hM ⟨0, hM⟩ hd]
  simp only [Nat.cast_zero, zero_div, hcomm]

theorem offgrid_phase_state_overlap (M : ℕ) (hM : 0 < M) (ω₀ ω₁ : ℝ) :
    let Δ := phaseDistance ω₀ ω₁
    (Δ = 0 → ‖offGridPhaseOverlap M ω₀ ω₁‖^2 = 1) ∧
    (Δ ≠ 0 → ‖offGridPhaseOverlap M ω₀ ω₁‖^2 =
      Real.sin ((M : ℝ)*Δ*Real.pi)^2/((M : ℝ)^2*Real.sin (Δ*Real.pi)^2)) :=
  ⟨offgrid_phase_overlap_zero_distance M hM ω₀ ω₁,
    offgrid_phase_overlap_nonzero_distance M hM ω₀ ω₁⟩

end Qatlib.Papers.AmpEstBrass00.OffGridQPE
