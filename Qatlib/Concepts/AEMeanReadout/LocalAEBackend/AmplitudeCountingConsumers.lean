/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# Amplitude estimation consumers for quantum counting

This module specializes amplitude estimation to a uniform state prepared by `QFTMatrix`. It
identifies the marked probability with the marked fraction and derives a cardinality error bound
from [BrassardEtAl2002], together with an exact-grid example on four elements.

## Main statements

* `amplitude_counting_actual_consumer`: gives the counting error window with success mass at
  least `8/π²`.
* `amplitude_counting_exact_grid_consumer`: proves exact estimation of one quarter when `6 ∣ M`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Matrix
open scoped Classical
set_option autoImplicit false

/-- The marked probability in the QFT preparation from label zero is the marked cardinality
divided by `N`. -/
theorem prepared_qft_mark_mass (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) :
    MeasureProb (preparedAAState (QFTMatrix N) (⟨0,hN⟩ : Fin N)) S =
      (S.card : ℝ)/(N : ℝ) := by
  rw [preparedAAState,qftMatrix_ket_zero N hN]
  have hn : ‖(Real.sqrt (N : ℝ) : ℂ)⁻¹‖^2=(N : ℝ)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt (by positivity)]
  simp only [MeasureProb,BornProb,hn,Finset.sum_const,nsmul_eq_mul]
  ring

/-- QFT-prepared amplitude estimation approximates the marked cardinality within
`2*π*√(t*(N-t))/M + π²*N/M²` with probability at least `8/π²`, where `t` is the marked
cardinality [BrassardEtAl2002]. -/
theorem amplitude_counting_actual_consumer (N M : ℕ) (hN : 0 < N) (hM : 2 ≤ M)
    (S : Finset (Fin N)) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
        2*Real.pi*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)+
          Real.pi^2*(N : ℝ)/(M : ℝ)^2),
      (aeLaw M (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hM).prob z ≥ 8/Real.pi^2 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsuccess := (prepared_ae_bhmt_error_and_endpoints M hM (QFTMatrix N)
    (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN)).1
  rw [prepared_qft_mark_mass N hN S] at hsuccess
  have hsqrt : (N : ℝ)*Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))) =
      Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card)) := by
    have he : (N : ℝ)^2*((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))) =
        (S.card : ℝ)*((N : ℝ)-S.card) := by field_simp [hn.ne']
    have h := Real.sqrt_mul (sq_nonneg (N : ℝ))
      ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ)))
    rw [he,Real.sqrt_sq_eq_abs,abs_of_pos hn] at h
    exact h.symm
  apply hsuccess.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    have h := mul_le_mul_of_nonneg_left hz hn.le
    have habs : |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| =
        (N : ℝ)*|aeEstimate M z-(S.card : ℝ)/(N : ℝ)| := by
      have he : (N : ℝ)*(aeEstimate M z-(S.card : ℝ)/(N : ℝ)) =
          (N : ℝ)*aeEstimate M z-(S.card : ℝ) := by field_simp [hn.ne']
      rw [← he,abs_mul,abs_of_pos hn]
    have he : (N : ℝ)*(2*Real.pi*
        Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ)))/(M : ℝ)+
          Real.pi^2/(M : ℝ)^2) =
        2*Real.pi*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)+
          Real.pi^2*(N : ℝ)/(M : ℝ)^2 := by
      calc
        _ = 2*Real.pi*((N : ℝ)*Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))))/
            (M : ℝ)+Real.pi^2*(N : ℝ)/(M : ℝ)^2 := by ring
        _ = _ := by rw [hsqrt]
    rw [← habs,he] at h
    exact h
  · intro z _ _
    exact (aeLaw M (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hM).nonneg z

/-- For one marked element among four and `6 ∣ M`, amplitude estimation returns the estimate
`1/4` with probability one. -/
theorem amplitude_counting_exact_grid_consumer (M : ℕ) (hM : 2 ≤ M) (hdiv : 6 ∣ M) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z=1/4),
      (aeLaw M (QFTMatrix 4) (0 : Fin 4) {0} (qftMatrix_unitary (by omega)) hM).prob z=1 := by
  obtain ⟨k,hMk⟩ := hdiv
  have hk0 : 0 < k := by omega
  let z₀ : Fin M := ⟨k,by omega⟩
  let z₁ : Fin M := ⟨5*k,by omega⟩
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hcast : (M : ℝ)=6*(k : ℝ) := by exact_mod_cast hMk
  have hz₀ : (z₀.val : ℝ)/(M : ℝ)=1/6 := by
    apply (div_eq_iff hm).mpr
    change (k : ℝ)=1/6*(M : ℝ)
    linarith
  have hz₁ : (z₁.val : ℝ)/(M : ℝ)=5/6 := by
    apply (div_eq_iff hm).mpr
    change ((5*k : ℕ) : ℝ)=5/6*(M : ℝ)
    push_cast
    linarith
  have hprob : MeasureProb (preparedAAState (QFTMatrix 4) (0 : Fin 4)) {0} =
      (Real.sin (Real.pi/6))^2 := by
    change MeasureProb (preparedAAState (QFTMatrix 4) (⟨0,by omega⟩ : Fin 4)) {0} = _
    rw [prepared_qft_mark_mass 4 (by omega) {0},Real.sin_pi_div_six]
    norm_num
  have hp : (Real.pi/6)/Real.pi=(1/6 : ℝ) := by field_simp
  have hn : -(Real.pi/6)/Real.pi=(-1/6 : ℝ) := by field_simp
  have hmass (y : Fin M) := prepared_ae_two_phase_distribution M hM (QFTMatrix 4)
    (0 : Fin 4) {0} (qftMatrix_unitary (by omega)) (Real.pi/6)
    (by positivity) (by linarith [Real.pi_pos]) hprob y
  have hkernel₀ (y : Fin M) : qpeKernel M (1/6) y=Ket z₀ y := by
    rw [← hz₀]
    exact (offgrid_phase_geometric_and_periodic M 0 y (by omega)).2.2 z₀
  have hkernel₁ (y : Fin M) : qpeKernel M (-1/6) y=Ket z₁ y := by
    have hperiod := qpeKernel_int_add M (-1/6) y 1
    norm_num at hperiod
    have hperiod' : qpeKernel M (5/6) y=qpeKernel M (-1/6) y := by
      simpa only [neg_div] using hperiod
    rw [← hperiod',← hz₁]
    exact (offgrid_phase_geometric_and_periodic M 0 y (by omega)).2.2 z₁
  have he₀ : aeEstimate M z₀=1/4 := by
    rw [aeEstimate,mul_div_assoc,hz₀,mul_one_div,Real.sin_pi_div_six]
    norm_num
  have he₁ : aeEstimate M z₁=1/4 := by
    rw [aeEstimate,mul_div_assoc,hz₁,
      show Real.pi*(5/6)=Real.pi-Real.pi/6 by ring,
      Real.sin_pi_sub,Real.sin_pi_div_six]
    norm_num
  have hsum (w : Fin M) (he : aeEstimate M w=1/4) :
      (∑ y ∈ Finset.univ.filter (fun y : Fin M => aeEstimate M y=1/4), ‖Ket w y‖^2)=1 := by
    rw [Finset.sum_eq_single w]
    · simp [Ket]
    · intro y _ hy
      simp [Ket,hy]
    · simp [Finset.mem_filter,he]
  simp_rw [hmass,hp,hn,hkernel₀,hkernel₁]
  rw [← Finset.sum_div,Finset.sum_add_distrib,hsum z₀ he₀,hsum z₁ he₁]
  norm_num

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
