/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeNeighborhood

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeNeighborhood

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis
open scoped Matrix

noncomputable def basisRadius : ℝ := 1 / 423795496418784

/-- The explicit basis radius `basisRadius` is positive. -/
theorem basisRadius_pos : 0 < basisRadius := by norm_num [basisRadius]

/-- The inverse of `sixthAmplitude` has complex norm at most three. -/
private theorem inv_amplitude_norm_le : ‖(sixthAmplitude : ℂ)⁻¹‖ ≤ 3 := by
  have hq := sixthAmplitude_pos
  have hl : (1 / 3 : ℝ) ≤ sixthAmplitude := by
    apply (sq_le_sq₀ (by norm_num) hq.le).mp
    rw [sixthAmplitude_sq]
    norm_num
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  simpa only [one_div] using (one_div_le hq (show (0 : ℝ) < 3 by norm_num)).mpr hl

/-- Four mutually unbiased bases cannot have their first three bases within `basisRadius` of the
canonical bases in every coordinate. -/
theorem canonical_no_four_within_explicit_radius
    (B : Fin 4 → Fin 6 → QState (Fin 6))
    (hclose : ∀ (r : Fin 3) (j i : Fin 6),
      ‖B r.castSucc j i - bases r j i‖ ≤ basisRadius) : ¬ IsFamily B := by
  intro hB
  let A0 : MatrixSix := columnMatrix (B 0)
  have hA0 : A0ᴴ * A0 = 1 := by
    have h := columnMatrix_mem_unitary (B 0) (hB.1 0)
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hAdj : A0ᴴ ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 6))).mp hA0
  let C := applyCommonUnitary A0ᴴ B
  have hC : IsFamily C := (isFamily_applyCommonUnitary_iff hAdj B).mpr hB
  have hC0 (j : Fin 6) : C 0 j = Ket j := by
    change ApplyGate A0ᴴ (B 0 j) = Ket j
    rw [← applyGate_columnMatrix_ket (B 0) j]
    change ApplyGate A0ᴴ (ApplyGate A0 (Ket j)) = Ket j
    rw [← applyGate_mul, hA0, applyGate_one]
  have hcoord (r : Fin 4) (j i : Fin 6) : ‖B r j i‖ ≤ 1 := by
    have hs : (∑ t : Fin 6, ‖B r j t‖ ^ 2) = 1 := normalized_column (hB.1 r) j
    have hi : ‖B r j i‖ ^ 2 ≤ ∑ t : Fin 6, ‖B r j t‖ ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg ‖B r j t‖) (Finset.mem_univ i)
    rw [hs] at hi
    nlinarith [norm_nonneg (B r j i)]
  have happ (r : Fin 4) (j i : Fin 6) : C r j i = Inner (B 0 i) (B r j) := by
    change (∑ t : Fin 6, (starRingEnd ℂ) (B 0 i t) * B r j t) = _
    exact (inner_apply _ _).symm
  have hc0 (i t : Fin 6) : ‖B 0 i t - Ket i t‖ ≤ basisRadius := by
    have h := hclose (0 : Fin 3) i t
    change ‖B 0 i t - Ket i t‖ ≤ basisRadius at h
    exact h
  have hrot (r : Fin 4) (j i : Fin 6) : ‖C r j i - B r j i‖ ≤ 6 * basisRadius := by
    have hid : C r j i - B r j i = Inner (fun t => B 0 i t - Ket i t) (B r j) := by
      rw [happ, ← inner_ket_eq_coordinate i (B r j)]
      simp only [inner_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hid]
    exact overlap_norm_le_six _ _ basisRadius basisRadius_pos.le (hc0 i) (hcoord r j)
  have hnear (r : Fin 3) (j i : Fin 6) :
      ‖C r.castSucc j i - bases r j i‖ ≤ 7 * basisRadius := by
    calc
      _ = ‖(C r.castSucc j i - B r.castSucc j i) + (B r.castSucc j i - bases r j i)‖ := by ring_nf
      _ ≤ ‖C r.castSucc j i - B r.castSucc j i‖ + ‖B r.castSucc j i - bases r j i‖ := norm_add_le _ _
      _ ≤ 6 * basisRadius + basisRadius := add_le_add (hrot r.castSucc j i) (hclose r j i)
      _ = 7 * basisRadius := by ring
  have hqNe : (sixthAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt sixthAmplitude_pos)
  let unscale (r : Fin 4) : MatrixSix := fun i j => (sixthAmplitude : ℂ)⁻¹ * C r j i
  have hnorm (r : Fin 4) (i j : Fin 6) : normalizeHadamard (unscale r) i j = C r j i := by
    change (sixthAmplitude : ℂ) * ((sixthAmplitude : ℂ)⁻¹ * C r j i) = _
    rw [← mul_assoc, mul_inv_cancel₀ hqNe, one_mul]
  have hmatrix (r : Fin 3) (M : MatrixSix)
      (hm : ∀ j i, bases r j i = normalizeHadamard M i j) :
      ∀ i j, ‖unscale r.castSucc i j - M i j‖ ≤ certifiedRadius := by
    intro i j
    have hd := hnear r j i
    rw [hm j i] at hd
    have he : unscale r.castSucc i j - M i j =
        (sixthAmplitude : ℂ)⁻¹ * (C r.castSucc j i - normalizeHadamard M i j) := by
      change (sixthAmplitude : ℂ)⁻¹ * C r.castSucc j i - M i j =
        (sixthAmplitude : ℂ)⁻¹ * (C r.castSucc j i - (sixthAmplitude : ℂ) * M i j)
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hqNe, one_mul]
    rw [he, norm_mul]
    calc
      _ ≤ 3 * (7 * basisRadius) :=
        mul_le_mul inv_amplitude_norm_le hd (norm_nonneg _) (by norm_num)
      _ = certifiedRadius := by norm_num [basisRadius, certifiedRadius]
  have hψ (i : Fin 6) : Complex.normSq (C 3 0 i) = (1 : ℝ) / 6 := by
    have h := hC.2 0 3 (by decide) i 0
    rw [hC0 i, inner_ket_eq_coordinate] at h
    exact h
  apply no_unbiased_vector_within_radius (unscale 1) (unscale 2) (C 3 0) hψ
  · exact hmatrix (1 : Fin 3) H (by intro j i; rfl)
  · exact hmatrix (2 : Fin 3) K (by intro j i; rfl)
  · intro j
    have heq : (fun i => normalizeHadamard (unscale 1) i j) = C 1 j :=
      funext (fun i => hnorm 1 i j)
    rw [heq]
    exact hC.2 1 3 (by decide) j 0
  · intro j
    have heq : (fun i => normalizeHadamard (unscale 2) i j) = C 2 j :=
      funext (fun i => hnorm 2 i j)
    rw [heq]
    exact hC.2 2 3 (by decide) j 0

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood
