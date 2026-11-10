/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.ReductionDefs
import Mathlib.Analysis.Real.Pi.Bounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

theorem abs_sub_round_le_half (t : ℝ) : |t - (⌊t + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  apply abs_le.mpr
  constructor <;> linarith

theorem abs_sub_round_le (t : ℝ) (m : ℤ) :
    |t - (⌊t + 1 / 2⌋ : ℝ)| ≤ |t - (m : ℝ)| := by
  have hhalf := abs_sub_round_le_half t
  by_cases hm : m = ⌊t + 1 / 2⌋
  · rw [hm]
  · have hgapI : (1 : ℤ) ≤ |m - ⌊t + 1 / 2⌋| := by
      by_cases hp : (0 : ℤ) ≤ m - ⌊t + 1 / 2⌋
      · rw [abs_of_nonneg hp]; omega
      · rw [abs_of_neg (by omega)]; omega
    have hgap : (1 : ℝ) ≤ |(m : ℝ) - (⌊t + 1 / 2⌋ : ℝ)| := by
      have hcast : ((m - ⌊t + 1 / 2⌋ : ℤ) : ℝ) = (m : ℝ) - (⌊t + 1 / 2⌋ : ℝ) := by
        push_cast; ring
      rw [← hcast, ← Int.cast_abs]
      exact_mod_cast hgapI
    have htri : |(m : ℝ) - (⌊t + 1 / 2⌋ : ℝ)| ≤
        |t - (m : ℝ)| + |t - (⌊t + 1 / 2⌋ : ℝ)| := by
      have h1 : |(m : ℝ) - (⌊t + 1 / 2⌋ : ℝ)| =
          |(t - (m : ℝ)) - (t - (⌊t + 1 / 2⌋ : ℝ))| := by
        rw [show (m : ℝ) - (⌊t + 1 / 2⌋ : ℝ)
          = -((t - (m : ℝ)) - (t - (⌊t + 1 / 2⌋ : ℝ))) by ring, abs_neg]
      rw [h1]
      have h2 := abs_add_le (t - (m : ℝ)) (-(t - (⌊t + 1 / 2⌋ : ℝ)))
      have h2' : |(t - (m : ℝ)) + (-(t - (⌊t + 1 / 2⌋ : ℝ)))|
          = |(t - (m : ℝ)) - (t - (⌊t + 1 / 2⌋ : ℝ))| := by
        rw [show (t - (m : ℝ)) + (-(t - (⌊t + 1 / 2⌋ : ℝ)))
          = (t - (m : ℝ)) - (t - (⌊t + 1 / 2⌋ : ℝ)) by ring]
      rw [h2'] at h2
      simpa [abs_sub_comm] using h2
    linarith

theorem phaseDistance_nonneg (x y : ℝ) : 0 ≤ phaseDistance x y := by
  unfold phaseDistance
  positivity

theorem phaseDistance_le_half (x y : ℝ) : phaseDistance x y ≤ 1 / 2 := by
  unfold phaseDistance
  exact abs_sub_round_le_half (x - y)

theorem phaseDistance_self (x : ℝ) : phaseDistance x x = 0 := by
  unfold phaseDistance
  have h1 : x - x + 1 / 2 = (1 / 2 : ℝ) := by ring
  rw [h1, show (⌊(1 / 2 : ℝ)⌋ : ℤ) = 0 by norm_num]
  simp

theorem phaseDistance_symm (x y : ℝ) : phaseDistance x y = phaseDistance y x := by
  unfold phaseDistance
  have h1 : |x - y - (⌊x - y + 1 / 2⌋ : ℝ)| ≤
      |y - x - (⌊y - x + 1 / 2⌋ : ℝ)| := by
    have h := abs_sub_round_le (x - y) (-(⌊y - x + 1 / 2⌋))
    rw [Int.cast_neg] at h
    have hkey : |x - y - -(⌊y - x + 1 / 2⌋ : ℝ)| =
        |y - x - (⌊y - x + 1 / 2⌋ : ℝ)| := by
      rw [show (x - y) - -(⌊y - x + 1 / 2⌋ : ℝ)
        = -((y - x) - (⌊y - x + 1 / 2⌋ : ℝ)) by ring, abs_neg]
    rw [← hkey]
    exact h
  have h2 : |y - x - (⌊y - x + 1 / 2⌋ : ℝ)| ≤
      |x - y - (⌊x - y + 1 / 2⌋ : ℝ)| := by
    have h := abs_sub_round_le (y - x) (-(⌊x - y + 1 / 2⌋))
    rw [Int.cast_neg] at h
    have hkey : |y - x - -(⌊x - y + 1 / 2⌋ : ℝ)| =
        |x - y - (⌊x - y + 1 / 2⌋ : ℝ)| := by
      rw [show (y - x) - -(⌊x - y + 1 / 2⌋ : ℝ)
        = -((x - y) - (⌊x - y + 1 / 2⌋ : ℝ)) by ring, abs_neg]
    rw [← hkey]
    exact h
  exact le_antisymm h1 h2

theorem phaseDistance_le_abs_sub_int (x y : ℝ) (m : ℤ) :
    phaseDistance x y ≤ |x - y - (m : ℝ)| := by
  unfold phaseDistance
  exact abs_sub_round_le (x - y) m

theorem phaseDistance_tri (x y z : ℝ) :
    phaseDistance x z ≤ phaseDistance x y + phaseDistance y z := by
  have h := phaseDistance_le_abs_sub_int x z
    (⌊x - y + 1 / 2⌋ + ⌊y - z + 1 / 2⌋)
  have hcast : ((⌊x - y + 1 / 2⌋ + ⌊y - z + 1 / 2⌋ : ℤ) : ℝ) =
      (⌊x - y + 1 / 2⌋ : ℝ) + (⌊y - z + 1 / 2⌋ : ℝ) := by push_cast; ring
  rw [hcast] at h
  have htri := abs_add_le (x - y - (⌊x - y + 1 / 2⌋ : ℝ))
    (y - z - (⌊y - z + 1 / 2⌋ : ℝ))
  have hkey : x - z - ((⌊x - y + 1 / 2⌋ : ℝ) + (⌊y - z + 1 / 2⌋ : ℝ)) =
      (x - y - (⌊x - y + 1 / 2⌋ : ℝ)) + (y - z - (⌊y - z + 1 / 2⌋ : ℝ)) := by ring
  rw [hkey] at h
  unfold phaseDistance at h ⊢
  linarith

theorem recordConsistent_of_windows (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (x : Fin M) (y : Fin N) (φ : ℝ)
    (hx : phaseDistance φ (labelPosition M x) ≤ 1 / (M : ℝ))
    (hy : phaseDistance φ (labelPosition N y) ≤ 1 / (N : ℝ)) :
    recordConsistent M N x y := by
  unfold recordConsistent
  have h := phaseDistance_tri (labelPosition M x) φ (labelPosition N y)
  rw [phaseDistance_symm] at hx
  linarith

theorem recordDecode_eq_some_iff (M N : ℕ) (x : Fin M) (y : Fin N) :
    recordDecode M N x y = some y ↔ recordConsistent M N x y := by
  simp [recordDecode]

theorem recordDecode_of_window (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (x : Fin M) (y : Fin N) (φ : ℝ)
    (hx : phaseDistance φ (labelPosition M x) ≤ 1 / (M : ℝ))
    (hy : phaseDistance φ (labelPosition N y) ≤ 1 / (N : ℝ)) :
    recordDecode M N x y = some y := by
  rw [recordDecode_eq_some_iff]
  exact recordConsistent_of_windows M N hM hN x y φ hx hy

theorem recordDecode_failure_certifies (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (x : Fin M) (y : Fin N) (φ : ℝ)
    (hfail : recordDecode M N x y = none) :
    ¬ (phaseDistance φ (labelPosition M x) ≤ 1 / (M : ℝ) ∧
        phaseDistance φ (labelPosition N y) ≤ 1 / (N : ℝ)) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have := recordDecode_of_window M N hM hN x y φ hx hy
  rw [hfail] at this
  cases this

theorem recordWindowEvent_subset_decodeEvent (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (φ : ℝ) :
    ∀ p : RecordSpace M N I,
      phaseDistance φ (labelPosition M p.1) ≤ 1 / (M : ℝ) ∧
        phaseDistance φ (labelPosition N p.2.2.1) ≤ 1 / (N : ℝ) →
      p ∈ recordDecodeEvent M N := by
  intro p hp
  simp only [recordDecodeEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact recordConsistent_of_windows M N hM hN p.1 p.2.2.1 φ hp.1 hp.2

theorem recordWindowEvent_eq (M N : ℕ) (φ : ℝ) :
    recordWindowEvent M N φ =
      (Finset.univ : Finset (Fin M × Fin N)).filter
        fun r => r.1 ∈ phaseWindow M φ ∧ r.2 ∈ phaseWindow N φ := by
  ext r
  simp only [recordWindowEvent, phaseWindow, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · intro h
    exact ⟨h.1, h.2⟩

theorem normalized_qpeKernel (M : ℕ) (hM : 0 < M) (φ : ℝ) : Normalized (qpeKernel M φ) := by
  have hfun : qpeKernel M φ = ApplyGate (QFTMatrix M)ᴴ (offGridPhase M φ) := by
    funext z; exact qpeKernel_apply M φ z
  rw [hfun]
  exact normalized_applyGate (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM))
    (offgrid_phase_kernel_formula M φ ⟨0, hM⟩ hM).2.2

theorem measureProb_recordEvent_sum {M N : ℕ} (ψ : QState (RecordSpace M N I))
    (S : Finset (Fin M)) (T : Finset (Fin N)) :
    MeasureProb ψ (recordEvent M N S T) =
      ∑ x ∈ S, ∑ y ∈ T, MeasureProb ψ (recordEvent M N {x} {y}) := by
  have key : ∀ (x : Fin M) (y : Fin N),
      MeasureProb ψ (recordEvent M N {x} {y}) =
      (∑ b ∈ (Finset.univ : Finset Bool), ∑ k ∈ (Finset.univ : Finset I),
        BornProb ψ (x, (b, (y, k)))) := by
    intro x y
    unfold MeasureProb recordEvent
    rw [Finset.sum_product' {x} (Finset.univ ×ˢ ({y} ×ˢ Finset.univ))
      (fun p q => BornProb ψ (p, q))]
    simp only [Finset.sum_singleton]
    rw [Finset.sum_product' (Finset.univ : Finset Bool) ({y} ×ˢ Finset.univ)
      (fun b q => BornProb ψ (x, (b, q)))]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_product' {y} (Finset.univ : Finset I)
      (fun y k => BornProb ψ (x, (b, (y, k))))]
    simp only [Finset.sum_singleton]
  have hL : MeasureProb ψ (recordEvent M N S T) =
      ∑ x ∈ S, ∑ b ∈ (Finset.univ : Finset Bool),
        ∑ y ∈ T, ∑ k ∈ (Finset.univ : Finset I), BornProb ψ (x, (b, (y, k))) := by
    unfold MeasureProb recordEvent
    rw [Finset.sum_product' S (Finset.univ ×ˢ (T ×ˢ Finset.univ))
      (fun x p => BornProb ψ (x, p))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_product' (Finset.univ : Finset Bool) (T ×ˢ Finset.univ)
      (fun b q => BornProb ψ (x, (b, q)))]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_product' T (Finset.univ : Finset I)
      (fun y k => BornProb ψ (x, (b, (y, k))))]
  have hR : (∑ x ∈ S, ∑ y ∈ T, MeasureProb ψ (recordEvent M N {x} {y})) =
      ∑ x ∈ S, ∑ y ∈ T, ∑ b ∈ (Finset.univ : Finset Bool),
        ∑ k ∈ (Finset.univ : Finset I), BornProb ψ (x, (b, (y, k))) := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => key x y))]
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

theorem recordRun_label_law_repeated {J : Type} [Fintype J]
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (U : Matrix I I ℂ)
    (v : J → QState I) (c : J → ℂ) (φ₀ : ℝ)
    (hv : ∀ j k, Qatlib.Foundations.PureStateMath.Inner (v j) (v k) = if j = k then 1 else 0)
    (he : ∀ j, ApplyGate U (v j) = Complex.exp (2 * Real.pi * Complex.I * φ₀) • v j)
    (x : Fin M) (y : Fin N) :
    MeasureProb (recordRun M N hM hN U (∑ j, c j • v j)) (recordEvent M N {x} {y}) =
      (∑ j, ‖c j‖ ^ 2) * (‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2) := by
  have h := recordRun_spectral_law (M := M) (N := N) hM hN U v c (fun _ => φ₀) hv he x y
  have hre : ∀ j : J,
      (‖c j‖ ^ 2 * ‖qpeKernel M φ₀ x‖ ^ 2) * ‖qpeKernel N φ₀ y‖ ^ 2 =
        ‖c j‖ ^ 2 * (‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2) := by
    intro j; ring
  simp_rw [hre] at h
  rw [← Finset.sum_mul] at h
  exact h

theorem recordRun_window_law_repeated {J : Type} [Fintype J]
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (U : Matrix I I ℂ)
    (v : J → QState I) (c : J → ℂ) (φ₀ : ℝ)
    (hv : ∀ j k, Qatlib.Foundations.PureStateMath.Inner (v j) (v k) = if j = k then 1 else 0)
    (he : ∀ j, ApplyGate U (v j) = Complex.exp (2 * Real.pi * Complex.I * φ₀) • v j)
    (S : Finset (Fin M)) (T : Finset (Fin N)) :
    MeasureProb (recordRun M N hM hN U (∑ j, c j • v j)) (recordEvent M N S T) =
      (∑ j, ‖c j‖ ^ 2) *
        (∑ x ∈ S, ‖qpeKernel M φ₀ x‖ ^ 2) *
        (∑ y ∈ T, ‖qpeKernel N φ₀ y‖ ^ 2) := by
  rw [measureProb_recordEvent_sum]
  have hlabel : ∀ (x : Fin M) (y : Fin N),
      MeasureProb (recordRun M N hM hN U (∑ j, c j • v j)) (recordEvent M N {x} {y}) =
        (∑ j, ‖c j‖ ^ 2) * (‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2) :=
    fun x y => recordRun_label_law_repeated M N hM hN U v c φ₀ hv he x y
  simp_rw [hlabel]
  have hinner : (∑ x ∈ S, ∑ y ∈ T,
        ‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2)
      = (∑ x ∈ S, ‖qpeKernel M φ₀ x‖ ^ 2) *
        (∑ y ∈ T, ‖qpeKernel N φ₀ y‖ ^ 2) := by
    calc
      (∑ x ∈ S, ∑ y ∈ T,
          ‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2)
          = ∑ x ∈ S, ‖qpeKernel M φ₀ x‖ ^ 2 *
            (∑ y ∈ T, ‖qpeKernel N φ₀ y‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact (Finset.mul_sum T (fun y => ‖qpeKernel N φ₀ y‖ ^ 2)
                (‖qpeKernel M φ₀ x‖ ^ 2)).symm
      _ = (∑ x ∈ S, ‖qpeKernel M φ₀ x‖ ^ 2) *
          (∑ y ∈ T, ‖qpeKernel N φ₀ y‖ ^ 2) := by
            exact (Finset.sum_mul S (fun x => ‖qpeKernel M φ₀ x‖ ^ 2)
              (∑ y ∈ T, ‖qpeKernel N φ₀ y‖ ^ 2)).symm
  calc
    (∑ x ∈ S, ∑ y ∈ T, (∑ j, ‖c j‖ ^ 2) *
          (‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2))
        = ∑ x ∈ S, (∑ j, ‖c j‖ ^ 2) *
          (∑ y ∈ T, ‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (Finset.mul_sum T (fun y => ‖qpeKernel M φ₀ x‖ ^ 2 *
            ‖qpeKernel N φ₀ y‖ ^ 2) (∑ j, ‖c j‖ ^ 2)).symm
    _ = (∑ j, ‖c j‖ ^ 2) *
          (∑ x ∈ S, ∑ y ∈ T,
            ‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2) := by
          exact (Finset.mul_sum S (fun x => ∑ y ∈ T,
            ‖qpeKernel M φ₀ x‖ ^ 2 * ‖qpeKernel N φ₀ y‖ ^ 2)
            (∑ j, ‖c j‖ ^ 2)).symm
    _ = ((∑ j, ‖c j‖ ^ 2) * (∑ x ∈ S, ‖qpeKernel M φ₀ x‖ ^ 2)) *
          (∑ y ∈ T, ‖qpeKernel N φ₀ y‖ ^ 2) := by
          rw [hinner]
          ring

theorem recordRun_joint_window_conditional (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ)
    (hnorm : Normalized ψ) :
    MeasureProb (recordRun M N (by omega) (by omega) U ψ)
        (recordEvent M N (phaseWindow M φ) Finset.univ) * (8 / Real.pi^2)
      ≤ MeasureProb (recordRun M N (by omega) (by omega) U ψ)
        (recordEvent M N (phaseWindow M φ) (phaseWindow N φ)) := by
  have hlaw := recordRun_joint_law M N (by omega) (by omega) U ψ φ hψ hnorm
    (phaseWindow M φ) (phaseWindow N φ)
  have hlawC := recordRun_joint_law M N (by omega) (by omega) U ψ φ hψ hnorm
    (phaseWindow M φ) Finset.univ
  have hN : 8 / Real.pi^2 ≤ MeasureProb (qpeKernel N φ) (phaseWindow N φ) :=
    offgrid_phase_window_probability N φ hN
  rw [hlaw, hlawC]
  have hunit : MeasureProb (qpeKernel N φ) Finset.univ = 1 :=
    measureProb_univ (normalized_qpeKernel N (by omega) φ)
  rw [hunit]
  have hpos : (0 : ℝ) ≤ MeasureProb (qpeKernel M φ) (phaseWindow M φ) :=
    measureProb_nonneg _ _
  nlinarith [mul_le_mul_of_nonneg_left hN hpos]

theorem recordEffectiveQueries_eq (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    recordEffectiveQueries M N = QueryCount (recordCircuit (I := I) M N) := by
  unfold recordEffectiveQueries
  exact (recordCircuit_resources (I := I) M N hM hN).1.symm

theorem recordEffectiveGates_eq (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    recordEffectiveGates M N = GateCount (recordCircuit (I := I) M N) := by
  unfold recordEffectiveGates
  exact (recordCircuit_resources (I := I) M N hM hN).2.1.symm

theorem recordEffectiveConfidence_eq : recordEffectiveConfidence = (8 / Real.pi^2)^2 := rfl

theorem recordEffective_radius (ε δ : ℝ) : recordEffectiveRadius ε δ = min ε δ := rfl

theorem recordEffective_dominated_by_fine_record (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    (N - 1) ≤ recordEffectiveQueries M N ∧
      recordEffectiveConfidence ≤ 8 / Real.pi^2 ∧
      QueryCount (countedPhaseCircuit (I := Fin N × I) N) = N - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold recordEffectiveQueries
    omega
  · unfold recordEffectiveConfidence
    have h8 : (8 : ℝ) ≤ Real.pi^2 := by
      have hpi := Real.pi_gt_three
      nlinarith [sq_nonneg (Real.pi - 3)]
    have hpos : (0 : ℝ) < Real.pi^2 := by positivity
    have hx : (8 : ℝ) / Real.pi^2 ≤ 1 := by
      exact (div_le_one hpos).2 h8
    have hnonneg : (0 : ℝ) ≤ 8 / Real.pi^2 := by positivity
    nlinarith
  · exact (counted_offgrid_qpe_clean_flag N hN
      (1 : Matrix (Fin N × I) (Fin N × I) ℂ) (0 : QState (Fin N × I))).2.1

theorem abs_intFloor_le (t : ℝ) : |((Int.floor t : ℤ) : ℝ)| ≤ |t| + 1 := by
  by_cases h : (0 : ℤ) ≤ Int.floor t
  · rw [abs_of_nonneg (by exact_mod_cast h)]
    have hpos : t ≤ |t| := le_abs_self t
    calc (Int.floor t : ℝ) ≤ t := by exact_mod_cast Int.floor_le t
      _ ≤ |t| + 1 := by linarith [hpos]
  · rw [abs_of_neg (by exact_mod_cast (by omega : Int.floor t < 0))]
    have h1 : (Int.floor t : ℝ) > t - 1 := by
      have := Int.lt_floor_add_one t
      linarith
    have hneg : -t ≤ |t| := by simpa using le_abs_self (-t)
    have h2 : -(Int.floor t : ℝ) < 1 - t := by linarith
    have h3 : 1 - t ≤ |t| + 1 := by linarith [hneg]
    exact le_of_lt (lt_of_lt_of_le h2 h3)

theorem two_pow_ge_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · simp [hn]
    · calc 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
        _ ≥ n * 2 := Nat.mul_le_mul_right 2 ih
        _ ≥ n + 1 := by omega

theorem hasGeneralRealQuantization : HasGeneralRealQuantization := by
  intro x eps hε
  obtain ⟨r₀, hr₀⟩ := exists_nat_ge (1 / eps : ℝ)
  set r := max r₀ 1 with hrdef
  have hrge : (1 / eps : ℝ) ≤ r := by
    have hle : (r₀ : ℝ) ≤ (max r₀ 1 : ℕ) := by
      exact_mod_cast (Nat.le_max_left r₀ 1)
    rw [hrdef]; linarith
  have htwo : r ≤ 2 ^ r := two_pow_ge_self r
  have hpow : (1 / eps : ℝ) ≤ 2 ^ r := by
    calc (1 / eps : ℝ) ≤ r := hrge
      _ ≤ (2 ^ r : ℝ) := by exact_mod_cast htwo
  set c : ℤ := Int.floor (x * (2 ^ r : ℝ)) with hc
  have hden : (0 : ℝ) < 2 ^ r := by positivity
  have hcast : ((c : ℤ) : ℝ) = ((Int.floor (x * (2 ^ r : ℝ)) : ℤ) : ℝ) := by
    rw [hc]
  have hfl : ((Int.floor (x * (2 ^ r : ℝ)) : ℤ) : ℝ) ≤ x * (2 ^ r : ℝ) := by
    have h1 := Int.floor_le (x * (2 ^ r : ℝ))
    exact_mod_cast h1
  have hfl' : x * (2 ^ r : ℝ) < ((Int.floor (x * (2 ^ r : ℝ)) : ℤ) : ℝ) + 1 := by
    have h1 := Int.lt_floor_add_one (x * (2 ^ r : ℝ))
    exact h1
  have hdiff : |x * (2 ^ r : ℝ) - (Int.floor (x * (2 ^ r : ℝ)) : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hone : (1 : ℝ) / (2 ^ r : ℝ) ≤ eps := by
    apply (div_le_iff₀ hden).2
    have h1 : (1 : ℝ) ≤ eps * (2 ^ r : ℝ) := by
      calc (1 : ℝ) ≤ eps * (1 / eps) := by
            rw [div_eq_mul_inv, one_mul, mul_inv_cancel₀ (ne_of_gt hε)]
        _ ≤ eps * (2 ^ r : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hε)
    linarith
  have herr : |x - dyadicDecode c r| ≤ eps := by
    rw [dyadicDecode, hcast]
    have hkey : x - ((Int.floor (x * (2 ^ r : ℝ)) : ℤ) : ℝ) / (2 ^ r : ℝ)
        = (x * (2 ^ r : ℝ) - ((Int.floor (x * (2 ^ r : ℝ)) : ℤ) : ℝ)) / (2 ^ r : ℝ) := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hden]
    have hlt : |x * (2 ^ r : ℝ) - ((Int.floor (x * (2 ^ r : ℝ)) : ℤ) : ℝ)| / (2 ^ r : ℝ)
        < 1 / (2 ^ r : ℝ) := by
      exact (div_lt_iff₀ hden).mpr (by simpa using hdiff)
    exact le_of_lt (lt_of_lt_of_le hlt hone)
  have hwit : ((c.natAbs : ℕ) : ℝ) ≤ (|x| + 1) * (2 ^ r : ℝ) := by
    have habs : ((c.natAbs : ℕ) : ℝ) ≤ |((c : ℤ) : ℝ)| := by
      have hstep : ((c.natAbs : ℕ) : ℝ) = ((|c| : ℤ) : ℝ) := by
        have h1 : (↑(c.natAbs : ℕ) : ℤ) = |c| := by simp
        have h2 : ((c.natAbs : ℕ) : ℝ) = ((↑(c.natAbs : ℕ) : ℤ) : ℝ) := by rfl
        rw [h2, h1]
      rw [hstep, Int.cast_abs]
    have hfa := abs_intFloor_le (x * (2 ^ r : ℝ))
    have habs2 : |x * (2 ^ r : ℝ)| = |x| * (2 ^ r : ℝ) := by
      rw [abs_mul, abs_of_pos hden]
    have hone : (1 : ℝ) ≤ 2 ^ r := by
      have h1 := Nat.one_le_two_pow (n := r)
      exact_mod_cast h1
    calc ((c.natAbs : ℕ) : ℝ) ≤ |((c : ℤ) : ℝ)| := habs
      _ ≤ |x * (2 ^ r : ℝ)| + 1 := by rw [hcast]; exact hfa
      _ = |x| * (2 ^ r : ℝ) + 1 := by rw [habs2]
      _ ≤ (|x| + 1) * (2 ^ r : ℝ) := by nlinarith [hone]
  refine ⟨r, c, herr, hpow, ?_, hwit⟩
  rw [dyadicCode]

theorem mul_upow_comm {H : Type} [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) :
    ∀ n : ℕ, U * U ^ n = U ^ n * U := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc U * U ^ (n + 1) = U * (U ^ n * U) := by rw [pow_succ]
      _ = (U * U ^ n) * U := by rw [mul_assoc]
      _ = (U ^ n * U) * U := congrArg (fun M => M * U) ih
      _ = U ^ (n + 1) * U := by rw [pow_succ]

theorem powerTwoOracleWord_eval {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (j : ℕ) :
    evaluate U (powerTwoOracleWord j) = oraclePowerIterate U (2 ^ j) := by
  have key : ∀ (n : ℕ), evaluate U (List.replicate n AdjointStep.forward) = U ^ n := by
    intro n
    induction n with
    | zero => simp [evaluate]
    | succ n ih =>
      show evaluate U (List.replicate (n + 1) AdjointStep.forward) = U ^ (n + 1)
      rw [List.replicate_succ, evaluate, instructionMatrix, ih, pow_succ, mul_upow_comm U n]
  have key2 : ∀ (n : ℕ), oraclePowerIterate U n = U ^ n := by
    intro n
    induction n with
    | zero => simp [oraclePowerIterate]
    | succ n ih =>
      show oraclePowerIterate U (n + 1) = U ^ (n + 1)
      rw [oraclePowerIterate, ih, pow_succ]
  show evaluate U (List.replicate (2 ^ j) AdjointStep.forward) = oraclePowerIterate U (2 ^ j)
  rw [key, key2]

theorem powerTwoOracleWord_costs {H : Type} [Fintype H] [DecidableEq H] (j : ℕ) :
    adjointQueryCount (powerTwoOracleWord (H := H) j) = 2 ^ j ∧
      adjointGateCount (powerTwoOracleWord (H := H) j) = 0 := by
  constructor
  · have key : ∀ n : ℕ,
        adjointQueryCount (H := H) (List.replicate n (AdjointStep.forward : AdjointStep H)) = n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, adjointQueryCount, ih]
    show adjointQueryCount (H := H)
        (List.replicate (2 ^ j) (AdjointStep.forward : AdjointStep H)) = 2 ^ j
    exact key _
  · have key : ∀ n : ℕ,
        adjointGateCount (H := H) (List.replicate n (AdjointStep.forward : AdjointStep H)) = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, adjointGateCount, ih]
    show adjointGateCount (H := H)
        (List.replicate (2 ^ j) (AdjointStep.forward : AdjointStep H)) = 0
    exact key _

theorem zeroQueryWordOracleIndependent : zeroQueryWordOracleIndependent := by
  intro H _ _ word U V hq
  induction word generalizing U V with
  | nil => rfl
  | cons s cs ih =>
    cases s with
    | gate W => exact congrArg (fun M => W * M) (ih U V hq)
    | forward => rw [adjointQueryCount] at hq; omega
    | backward => rw [adjointQueryCount] at hq; omega

end Qatlib.Concepts.FourierRecovery.ModularFourier
