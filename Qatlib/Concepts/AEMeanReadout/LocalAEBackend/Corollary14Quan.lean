/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Stat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Spec
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical
set_option autoImplicit false

theorem bhmt_corollary14_rounded_count :
    ∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N), 2 ≤ N →
      ∀ (hM : 2 ≤ approxCountCor14Grid N),
      let t : ℝ := (S.card : ℝ)
      ∑ z ∈ Finset.univ.filter (fun z : Fin (approxCountCor14Grid N) =>
        |(approxCountCor14Output N z : ℝ)-t| <
          2*Real.pi*Real.sqrt (t*((N : ℝ)-t)/(N : ℝ))+11),
        (aeLaw (approxCountCor14Grid N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM).prob z ≥ 8/Real.pi^2 := by
  intro N S hN _hN2 hM
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hm : (0:ℝ) < approxCountCor14Grid N := by
    exact_mod_cast (by omega : 0 < approxCountCor14Grid N)
  have hgrid : Real.sqrt (N : ℝ) ≤ (approxCountCor14Grid N : ℝ) := Nat.le_ceil _
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hm2 : (N : ℝ) ≤ (approxCountCor14Grid N : ℝ)^2 := by
    nlinarith [Real.sq_sqrt hn.le]
  have ht : 0 ≤ (S.card : ℝ)*((N : ℝ)-S.card) := by
    have hc : (S.card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show S.card ≤ N from (Finset.card_le_univ S).trans_eq (Fintype.card_fin N))
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hc)
  have hfirst : 2*Real.pi*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(approxCountCor14Grid N : ℝ) ≤
      2*Real.pi*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card)/(N : ℝ)) := by
    rw [Real.sqrt_div ht]
    calc
      _ ≤ 2*Real.pi*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/Real.sqrt (N : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hroot hgrid
      _ = _ := by ring
  have hsecond : Real.pi^2*(N : ℝ)/(approxCountCor14Grid N : ℝ)^2 ≤ Real.pi^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    exact mul_le_mul_of_nonneg_left hm2 (sq_nonneg Real.pi)
  have hpi : Real.pi^2+(1/2 : ℝ) < 11 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsuccess := amplitude_counting_actual_consumer N (approxCountCor14Grid N) hN hM S
  apply hsuccess.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hround : |(approxCountCor14Output N z : ℝ) -
        (N : ℝ)*aeEstimate (approxCountCor14Grid N) z| ≤ 1/2 := by
      unfold approxCountCor14Output
      apply abs_le.mpr
      have hfl := Int.floor_le ((N : ℝ)*aeEstimate (approxCountCor14Grid N) z+1/2)
      have hfu := Int.lt_floor_add_one ((N : ℝ)*aeEstimate (approxCountCor14Grid N) z+1/2)
      constructor <;> linarith
    have htriangle := abs_sub_le (approxCountCor14Output N z : ℝ)
      ((N : ℝ)*aeEstimate (approxCountCor14Grid N) z) (S.card : ℝ)
    linarith
  · intro z _ _
    exact (aeLaw (approxCountCor14Grid N) (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hM).nonneg z

theorem bhmt_corollary14_rounded_count_contract :
    Corollary14Spec.expected :=
  bhmt_corollary14_rounded_count

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
