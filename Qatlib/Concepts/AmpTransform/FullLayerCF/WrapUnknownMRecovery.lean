/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamSuccessMass
import Mathlib.Analysis.Real.Pi.Irrational
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.FullLayerCF

theorem aqRetry_cost_cap {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ) (xs : List (Fin N)) :
    (aqRetry h s M B k xs).2 ≤ xs.length * (k + 3) := by
  have hc (y : Fin N) : (aqAttempt h s M B y).2.1 ≤ 3 := by
    unfold aqAttempt
    (try dsimp only)
    split
    · simp
    · exact aqVerify_cost _ _ _ _
  induction xs with
  | nil => simp [aqRetry]
  | cons y ys ih =>
    simp only [aqRetry, List.length_cons]
    split
    · have ht := hc y
      (try dsimp only)
      nlinarith
    · have ht := hc y
      (try dsimp only)
      nlinarith

theorem wrapping_progression_retry_none (h : Fin 128 → Bool) (B k : ℕ)
    (xs : List (Fin 128)) : (aqRetry h 127 2 B k xs).1 = none := by
  have hv (q : ℕ) : (aqVerify h 127 2 q).1 = false := by
    rw [aqVerify, dif_neg (by omega)]
  have ha (y : Fin 128) : (aqAttempt h 127 2 B y).1 = none := by
    unfold aqAttempt
    (try dsimp only)
    split
    · rfl
    · simp [hv]
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [aqRetry, ha, ih]

open scoped Classical BigOperators

def aqCyclicVerify (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ) : Bool × ℕ :=
  if 0 < q ∧ 2 ≤ M ∧ M * q ≤ N then
    ([⟨s % N, Nat.mod_lt _ hN⟩, ⟨(s + q) % N, Nat.mod_lt _ hN⟩,
      ⟨(s + (M - 1) * q) % N, Nat.mod_lt _ hN⟩] : List (Fin N)).foldl
      (fun a x => (a.1 && h x, a.2 + 1)) (true, 0)
  else (false, 0)

theorem aqCyclicVerify_cost (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ) :
    (aqCyclicVerify N hN h s M q).2 ≤ 3 := by
  unfold aqCyclicVerify
  split <;> simp

theorem aqCyclicVerify_true (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N) (G : Finset (Fin N))
    (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
      (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)) :
    aqCyclicVerify N hN h s M P = (true, 3) := by
  have hm (r : ℕ) (hr : r < M) : h ⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ = true := by
    rw [hmark]
    apply decide_eq_true
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩)
  have hz := hm 0 (by omega)
  have h1 := hm 1 (by omega)
  have hlast := hm (M - 1) (by omega)
  simp only [zero_mul, add_zero] at hz
  simp only [one_mul] at h1
  simp [aqCyclicVerify, hP, hM, hMP, hz, h1, hlast]

noncomputable def aqPublicDensityReadout (N : ℕ) (z : Fin (32 * N)) : ℕ :=
  Nat.floor ((N : ℝ) * aeEstimate (32 * N) z + 1 / 2)

theorem aqPublicDensityCounting_actual (N : ℕ) (hN : 0 < N) (C : Finset (Fin N)) :
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin (32 * N) => aqPublicDensityReadout N z = C.card),
        (aeLaw (32 * N) (QFTMatrix N) ⟨0, hN⟩ C (qftMatrix_unitary hN)
          (by omega)).prob z ∧
    QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 ∧
    GateCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) =
      5 * (32 * N - 1) + 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : (C.card : ℝ) ≤ N := by
    have hh := Finset.card_le_card (Finset.subset_univ C)
    simpa using! hh
  have hs : Real.sqrt ((C.card : ℝ) * ((N : ℝ) - C.card)) ≤ N := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hn.le, by nlinarith [sq_nonneg ((C.card : ℝ) - N / 2)]⟩
  have he : 2 * Real.pi * Real.sqrt ((C.card : ℝ) * ((N : ℝ) - C.card)) /
      (32 * (N : ℝ)) + Real.pi ^ 2 * N / (32 * (N : ℝ)) ^ 2 < 1 / 2 := by
    have h1 : 2 * Real.pi * Real.sqrt ((C.card : ℝ) * ((N : ℝ) - C.card)) /
        (32 * (N : ℝ)) ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith [mul_nonneg hn.le (sub_nonneg.mpr Real.pi_lt_four.le)]
    have hp : Real.pi ^ 2 ≤ 16 * (N : ℝ) := by
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    have h2 : Real.pi ^ 2 * N / (32 * (N : ℝ)) ^ 2 ≤ 1 / 64 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hp hn.le
      nlinarith
    linarith
  have hmass := amplitude_counting_actual_consumer N (32 * N) hN (by omega) C
  have hc := prepared_ae_access_ledger (32 * N) (by omega) (QFTMatrix N) (⟨0,hN⟩ : Fin N)
  refine ⟨hmass.trans ?_, hc.1, hc.2.1⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hw : |(N : ℝ) * aeEstimate (32 * N) z - (C.card : ℝ)| < 1 / 2 := by
      apply hz.trans_lt
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using! he
    have hw' := abs_lt.mp hw
    unfold aqPublicDensityReadout
    apply (Nat.floor_eq_iff (show 0 ≤ (N : ℝ) * aeEstimate (32 * N) z + 1 / 2 by
      have hh := Nat.cast_nonneg (α := ℝ) C.card
      linarith)).mpr
    constructor <;> linarith
  · intro z _ _
    exact (aeLaw (32 * N) (QFTMatrix N) ⟨0,hN⟩ C (qftMatrix_unitary hN) (by omega)).nonneg z

end Qatlib.Concepts.AmpTransform.FullLayerCF
