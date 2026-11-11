/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SolovayKitaevStep

/-!
# Perturbation bounds for unitary commutators

This module bounds the distance between unitaries in a C*-ring and proves
`lemma1_commutator_perturbation`, an explicit polynomial bound for perturbing both factors of a
group commutator. The estimate retains the dependence on the original factors' distances from
the identity, following the commutator analysis of [DawsonNielsen2006].

## Main statements

* `lemma1_commutator_perturbation`: If the original unitary factors are within `δ` of the
  identity and each perturbation is smaller than `Δ`, their commutators differ by less than
  `8*Δ*δ + 4*Δ*δ^2 + 8*Δ^2 + 4*Δ^3 + Δ^4`, as in [DawsonNielsen2006].

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.CommutatorPerturbation

open Qatlib.Concepts.UnbiasedBases.ThreeBasis.CSD.SolovayKitaev

set_option autoImplicit false

/-- The distance between two unitary elements of a C*-ring is at most `2`. -/
theorem unitary_norm_sub_le_two {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {K K' : E} (hK : K ∈ unitary E) (hK' : K' ∈ unitary E) : ‖K - K'‖ ≤ 2 := by
  by_cases hN : Nontrivial E
  · haveI := hN
    calc ‖K - K'‖ ≤ ‖K‖ + ‖K'‖ := norm_sub_le _ _
      _ = 1 + 1 := by
          rw [CStarRing.norm_of_mem_unitary hK, CStarRing.norm_of_mem_unitary hK']
      _ = 2 := by norm_num
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hN
    rw [Subsingleton.elim K K', sub_self, norm_zero]
    norm_num

/-- If the original unitary factors are within `δ` of the identity and each perturbation is
smaller than `Δ`, their commutators differ by less than `8*Δ*δ + 4*Δ*δ^2 + 8*Δ^2 + 4*Δ^3 +
Δ^4`, as in [DawsonNielsen2006]. -/
theorem lemma1_commutator_perturbation {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {V W V' W' : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E)
    {Δ δ : ℝ} (hVV' : ‖V - V'‖ < Δ) (hWW' : ‖W - W'‖ < Δ)
    (hV1 : ‖V - 1‖ < δ) (hW1 : ‖W - 1‖ < δ) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖ <
      8 * Δ * δ + 4 * Δ * δ ^ 2 + 8 * Δ ^ 2 + 4 * Δ ^ 3 + Δ ^ 4 := by
  have hΔpos : 0 < Δ := lt_of_le_of_lt (norm_nonneg _) hVV'
  have hδpos : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hV1

  have haV : ‖V - 1‖ ≤ δ + Δ := by linarith [hV1.le]
  have haW : ‖W - 1‖ ≤ δ + Δ := by linarith [hW1.le]
  have haV' : ‖V' - 1‖ ≤ δ + Δ := by
    have h : ‖V' - 1‖ ≤ ‖V - V'‖ + ‖V - 1‖ := by
      have e : V' - 1 = (V' - V) + (V - 1) := by abel
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_sub_rev V' V]
    linarith [hVV'.le, hV1.le]
  have haW' : ‖W' - 1‖ ≤ δ + Δ := by
    have h : ‖W' - 1‖ ≤ ‖W - W'‖ + ‖W - 1‖ := by
      have e : W' - 1 = (W' - W) + (W - 1) := by abel
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_sub_rev W' W]
    linarith [hWW'.le, hW1.le]
  by_cases hΔ : Δ ≤ 1 / 2
  · have hfrozen := norm_groupCommutator_sub_le hV hW hV' hW'
      (a := δ + Δ) (δ := Δ) haV haW haV' haW' hVV'.le hWW'.le
    refine lt_of_le_of_lt hfrozen ?_
    have hkey : 8 * Δ * δ + 4 * Δ * δ ^ 2 + 8 * Δ ^ 2 + 4 * Δ ^ 3 + Δ ^ 4
        - 4 * (δ + Δ) * Δ * (1 + (δ + Δ))
        = Δ * (4 * δ * (1 - 2 * Δ) + 4 * Δ + Δ ^ 3) := by ring
    have h1 : 0 ≤ 4 * δ * (1 - 2 * Δ) := by nlinarith [hδpos, hΔ]
    have h2 : 0 < 4 * Δ + Δ ^ 3 := by nlinarith [hΔpos, pow_pos hΔpos 3]
    have hpos : 0 < Δ * (4 * δ * (1 - 2 * Δ) + 4 * Δ + Δ ^ 3) := by
      nlinarith [hΔpos, h1, h2]
    linarith [hkey, hpos]
  · push_neg at hΔ
    have hK : V * W * star V * star W ∈ unitary E :=
      mul_mem (mul_mem (mul_mem hV hW) (Unitary.star_mem hV)) (Unitary.star_mem hW)
    have hK' : V' * W' * star V' * star W' ∈ unitary E :=
      mul_mem (mul_mem (mul_mem hV' hW') (Unitary.star_mem hV')) (Unitary.star_mem hW')
    have htwo := unitary_norm_sub_le_two hK hK'
    refine lt_of_le_of_lt htwo ?_
    nlinarith [hΔpos, hδpos, hΔ, sq_nonneg Δ]

end Qatlib.Papers.SolovayKitaev05.MainResults.CommutatorPerturbation
