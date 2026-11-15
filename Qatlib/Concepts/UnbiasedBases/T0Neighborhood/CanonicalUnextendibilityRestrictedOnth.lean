/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedStat
public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalBridge

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib.Concepts.UnbiasedBases.T0Neighborhood
open Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalBridge

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

/-- Removes Hadamard normalization from an overlap of squared norm one sixth, giving an
unnormalized overlap of squared norm one. -/
private theorem unscale_overlap (A : MatrixSix) (j : Fin 6)
    (ψ : QState (Fin 6))
    (h : Complex.normSq (Inner (fun i => normalizeHadamard A i j) ψ) = (1 : ℝ) / 6) :
    Complex.normSq (Inner (fun i => A i j) ψ) = 1 := by
  have he := inner_rephase (sixthAmplitude : ℂ) 1 (fun i => A i j) ψ
  simp only [one_mul, mul_one] at he
  change Inner (fun i => normalizeHadamard A i j) ψ =
    (starRingEnd ℂ) (sixthAmplitude : ℂ) * Inner (fun i => A i j) ψ at he
  rw [he, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_ofReal, ← pow_two, sixthAmplitude_sq] at h
  linarith

/-- Establishes `CanonicalUnextendibilityRestricted` for the canonical bases. -/
theorem canonicalUnextendibilityRestricted : CanonicalUnextendibilityRestricted := by
  intro ψ hb
  have hψ (i : Fin 6) : Complex.normSq (ψ i) = (1 : ℝ) / 6 := by
    have h := hb (0 : Fin 3) i
    change Complex.normSq (Inner (Ket i) ψ) = (1 : ℝ) / 6 at h
    rw [inner_ket_eq_coordinate] at h
    exact h
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
  have hs (A : MatrixSix) (j : Fin 6)
      (h : Complex.normSq (Inner (fun i => normalizeHadamard A i j) ψ) = (1 : ℝ) / 6) :
      Complex.normSq (Inner (fun i => A i j) z) = 6 := by
    have he := inner_rephase 1 c (fun i => A i j) ψ
    simp only [one_mul, map_one] at he
    change Inner (fun i => A i j) z = c * Inner (fun i => A i j) ψ at he
    rw [he, Complex.normSq_mul, hc, unscale_overlap A j ψ h]
    norm_num
  apply no_flat_extension z hz0 hz
  · intro j; apply hs H j; simpa [Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases] using! hb 1 j
  · intro j; apply hs K j; simpa [Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases] using! hb 2 j

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth
