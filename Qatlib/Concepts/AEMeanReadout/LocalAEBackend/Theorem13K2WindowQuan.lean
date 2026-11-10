/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem13K2WindowStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem12K2WindowQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical
set_option autoImplicit false

theorem bhmt_counting_k2_window (N M : ℕ) (S : Finset (Fin N)) (hN : 0 < N)
    (hM : 2 ≤ M) (k : ℕ) (hk : 2 ≤ k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)+
            Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
      (aeLaw M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z ≥
        1-1/(2*((k : ℝ)-1)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsuccess := bhmt_amplitude_estimation_k2_window (Fin N) M (QFTMatrix N)
    (⟨0,hN⟩ : Fin N) S hM (qftMatrix_unitary hN) k hk
  rw [prepared_qft_mark_mass N hN S] at hsuccess
  have hsqrt : (N : ℝ)*Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))) =
      Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card)) := by
    have he : (N : ℝ)^2*((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))) =
        (S.card : ℝ)*((N : ℝ)-S.card) := by field_simp [hn.ne']
    have h := Real.sqrt_mul (sq_nonneg (N : ℝ))
      ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ)))
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos hn] at h
    exact h.symm
  apply hsuccess.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have h := mul_le_mul_of_nonneg_left hz hn.le
    have habs : |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| =
        (N : ℝ)*|aeEstimate M z-(S.card : ℝ)/(N : ℝ)| := by
      have he : (N : ℝ)*(aeEstimate M z-(S.card : ℝ)/(N : ℝ)) =
          (N : ℝ)*aeEstimate M z-(S.card : ℝ) := by field_simp [hn.ne']
      rw [← he, abs_mul, abs_of_pos hn]
    have he : (N : ℝ)*(2*Real.pi*(k : ℝ)*
        Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ)))/(M : ℝ)+
          (k : ℝ)^2*Real.pi^2/(M : ℝ)^2) =
        2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)+
          Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2 := by
      calc
        _ = 2*Real.pi*(k : ℝ)*((N : ℝ)*Real.sqrt
            ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))))/(M : ℝ)+
              Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2 := by ring
        _ = _ := by rw [hsqrt]
    rw [← habs, he] at h
    exact h
  · intro z _ _
    exact (aeLaw M (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hM).nonneg z

theorem bhmt_counting_k2_window_contract :
    Theorem13K2WindowSpec.expected :=
  bhmt_counting_k2_window

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
