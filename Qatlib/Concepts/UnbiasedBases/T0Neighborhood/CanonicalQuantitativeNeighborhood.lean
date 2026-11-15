/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeBridge

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeBridge

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeNeighborhood
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

noncomputable def certifiedRadius : ℝ := 1 / 20180737924704

/-- The certified neighborhood radius is positive. -/
theorem certifiedRadius_pos : 0 < certifiedRadius := by norm_num [certifiedRadius]

/-- The certified neighborhood radius is at most one. -/
theorem certifiedRadius_le_one : certifiedRadius ≤ 1 := by norm_num [certifiedRadius]

/-- Bounds the overlap norm by six times a coordinate bound on `a` when every coordinate of `z`
has norm at most one. -/
theorem overlap_norm_le_six (a z : QState (Fin 6)) (q : ℝ)
    (hq : 0 ≤ q) (ha : ∀ i, ‖a i‖ ≤ q) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖Inner a z‖ ≤ 6 * q := by
  rw [inner_apply]
  calc
    _ ≤ ∑ i : Fin 6, ‖(starRingEnd ℂ) (a i) * z i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 6, q := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_conj]
      simpa only [mul_one] using mul_le_mul (ha i) (hz i) (norm_nonneg (z i)) hq
    _ = 6 * q := by simp

/-- Bounds the difference of squared norms by the norm of the difference times the sum of the
norms. -/
private theorem normSq_difference (x y : ℂ) :
    |Complex.normSq y - Complex.normSq x| ≤ ‖y - x‖ * (‖y‖ + ‖x‖) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have he : ‖y‖ ^ 2 - ‖x‖ ^ 2 = (‖y‖ - ‖x‖) * (‖y‖ + ‖x‖) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg y) (norm_nonneg x))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le y x)
    (add_nonneg (norm_nonneg y) (norm_nonneg x))

/-- Bounds the overlap residual from six by 108 times the coordinate perturbation when the
perturbed overlap has squared norm six. -/
private theorem overlap_residual_le (a b z : QState (Fin 6)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hba : ∀ i, ‖b i - a i‖ ≤ δ)
    (hb : Complex.normSq (Inner b z) = 6) :
    |Complex.normSq (Inner a z) - 6| ≤ 108 * δ := by
  have hx : ‖Inner a z‖ ≤ 6 := by
    simpa using overlap_norm_le_six a z 1 (by norm_num) ha hz
  have hid : Inner b z - Inner a z = Inner (fun i => b i - a i) z := by
    simp only [inner_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  have hd : ‖Inner b z - Inner a z‖ ≤ 6 * δ := by
    rw [hid]
    exact overlap_norm_le_six _ z δ hδ hba hz
  have hy : ‖Inner b z‖ ≤ 6 * δ + 6 := by
    calc
      _ = ‖(Inner b z - Inner a z) + Inner a z‖ := by rw [sub_add_cancel]
      _ ≤ ‖Inner b z - Inner a z‖ + ‖Inner a z‖ := norm_add_le _ _
      _ ≤ 6 * δ + 6 := add_le_add hd hx
  calc
    _ = |Complex.normSq (Inner b z) - Complex.normSq (Inner a z)| := by
      rw [hb, abs_sub_comm]
    _ ≤ ‖Inner b z - Inner a z‖ * (‖Inner b z‖ + ‖Inner a z‖) :=
      normSq_difference _ _
    _ ≤ (6 * δ) * ((6 * δ + 6) + 6) :=
      mul_le_mul hd (add_le_add hy hx) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (by norm_num) hδ)
    _ ≤ 108 * δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]

/-- No flat vector with first coordinate one has squared overlaps six with all columns of both
matrices in the certified neighborhood of `H` and `K`. -/
theorem no_flat_extension_within_radius (A B : MatrixSix) (z : QState (Fin 6))
    (hz0 : z 0 = 1) (hz : ∀ i, Complex.normSq (z i) = 1)
    (hA : ∀ i j, ‖A i j - H i j‖ ≤ certifiedRadius)
    (hB : ∀ i j, ‖B i j - K i j‖ ≤ certifiedRadius)
    (hAz : ∀ j, Complex.normSq (Inner (fun i => A i j) z) = 6)
    (hBz : ∀ j, Complex.normSq (Inner (fun i => B i j) z) = 6) : False := by
  have hn (i : Fin 6) : ‖z i‖ ≤ 1 := by
    have h := hz i
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (z i)]
  have hu (M : MatrixSix) (hM : ∀ i j, Complex.normSq (M i j) = 1) (i j : Fin 6) :
      ‖M i j‖ ≤ 1 := by
    have h := hM i j
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (M i j)]
  have h := flat_residual_barrier z hz0 hz (108 * certifiedRadius)
    (mul_nonneg (by norm_num) certifiedRadius_pos.le)
    (fun j => overlap_residual_le _ _ z certifiedRadius certifiedRadius_pos.le
      certifiedRadius_le_one hn (fun i => hu H H_entry_normSq i j)
      (fun i => hA i j) (hAz j))
    (fun j => overlap_residual_le _ _ z certifiedRadius certifiedRadius_pos.le
      certifiedRadius_le_one hn (fun i => hu K K_entry_normSq i j)
      (fun i => hB i j) (hBz j))
  norm_num [certifiedRadius] at h

/-- Removes Hadamard normalization from an overlap of squared norm one sixth, giving an
unnormalized overlap of squared norm one. -/
private theorem unscale_overlap (A : MatrixSix) (j : Fin 6) (ψ : QState (Fin 6))
    (h : Complex.normSq (Inner (fun i => normalizeHadamard A i j) ψ) = (1 : ℝ) / 6) :
    Complex.normSq (Inner (fun i => A i j) ψ) = 1 := by
  have he := inner_rephase (sixthAmplitude : ℂ) 1 (fun i => A i j) ψ
  simp only [one_mul, mul_one] at he
  change Inner (fun i => normalizeHadamard A i j) ψ =
    (starRingEnd ℂ) (sixthAmplitude : ℂ) * Inner (fun i => A i j) ψ at he
  rw [he, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_ofReal, ← pow_two, sixthAmplitude_sq] at h
  linarith

/-- No vector with coordinate squared norms one sixth is unbiased to both normalized matrices in
the certified neighborhood of `H` and `K`. -/
theorem no_unbiased_vector_within_radius (A B : MatrixSix) (ψ : QState (Fin 6))
    (hψ : ∀ i, Complex.normSq (ψ i) = (1 : ℝ) / 6)
    (hA : ∀ i j, ‖A i j - H i j‖ ≤ certifiedRadius)
    (hB : ∀ i j, ‖B i j - K i j‖ ≤ certifiedRadius)
    (hAz : ∀ j, Complex.normSq (Inner (fun i => normalizeHadamard A i j) ψ) = (1 : ℝ) / 6)
    (hBz : ∀ j, Complex.normSq (Inner (fun i => normalizeHadamard B i j) ψ) = (1 : ℝ) / 6) : False := by
  let c : ℂ := 6 * (starRingEnd ℂ) (ψ 0)
  let z : QState (Fin 6) := fun i => c * ψ i
  have hc : Complex.normSq c = 6 := by
    simp only [c, Complex.normSq_mul, Complex.normSq_conj, hψ]
    norm_num
  have hz0 : z 0 = 1 := by
    dsimp [z, c]
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, hψ]
    norm_num
  have hz (i : Fin 6) : Complex.normSq (z i) = 1 := by
    change Complex.normSq (c * ψ i) = 1
    rw [Complex.normSq_mul, hc, hψ]
    norm_num
  have hs (M : MatrixSix) (j : Fin 6)
      (hm : Complex.normSq (Inner (fun i => normalizeHadamard M i j) ψ) = (1 : ℝ) / 6) :
      Complex.normSq (Inner (fun i => M i j) z) = 6 := by
    have he := inner_rephase 1 c (fun i => M i j) ψ
    simp only [one_mul, map_one] at he
    change Inner (fun i => M i j) z = c * Inner (fun i => M i j) ψ at he
    rw [he, Complex.normSq_mul, hc, unscale_overlap M j ψ hm]
    norm_num
  exact no_flat_extension_within_radius A B z hz0 hz hA hB
    (fun j => hs A j (hAz j)) (fun j => hs B j (hBz j))

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeNeighborhood
