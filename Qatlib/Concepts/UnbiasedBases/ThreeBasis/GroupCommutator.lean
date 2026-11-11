/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Norm estimates for unitary group commutators

This module bounds additive and multiplicative commutators in normed rings and C*-algebras. The
estimates express the quadratic smallness of the group commutator near the identity and its
stability under perturbations of unitary factors, as used in Solovay–Kitaev approximation
[DawsonNielsen2006].

## Main statements

* `norm_mul_sub_mul_comm_le`: bounds the additive commutator by distances from the identity.
* `norm_groupCommutator_sub_one_lt`: gives a strict contraction for distances below one half.
* `norm_groupCommutator_sub_groupCommutator_le`: bounds the change in a unitary commutator.

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

open CStarRing

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

section

variable {E : Type*}

/-- The norm of `V * W - W * V` is at most `2 * ‖V - 1‖ * ‖W - 1‖` in a normed ring. -/
theorem norm_mul_sub_mul_comm_le [NormedRing E] (V W : E) :
    ‖V * W - W * V‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  have key : V * W - W * V = (V - 1) * (W - 1) - (W - 1) * (V - 1) := by noncomm_ring
  rw [key]
  calc ‖(V - 1) * (W - 1) - (W - 1) * (V - 1)‖
      ≤ ‖(V - 1) * (W - 1)‖ + ‖(W - 1) * (V - 1)‖ := norm_sub_le _ _
    _ ≤ ‖V - 1‖ * ‖W - 1‖ + ‖W - 1‖ * ‖V - 1‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖V - 1‖ * ‖W - 1‖ := by ring

namespace CStarRing

variable [NormedRing E] [StarRing E] [CStarRing E]

omit [CStarRing E] in

/-- For unitary `V` and `W`, the group commutator minus the identity equals the additive
commutator multiplied by `star V * star W`. -/
theorem groupCommutator_sub_one_eq {V W : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E) :
    V * W * star V * star W - 1 = (V * W - W * V) * (star V * star W) := by
  have h1 : W * V * (star V * star W) = 1 := by
    rw [show W * V * (star V * star W) = W * (V * star V) * star W from by noncomm_ring,
      Unitary.mul_star_self_of_mem hV, mul_one, Unitary.mul_star_self_of_mem hW]
  rw [sub_mul, h1]
  noncomm_ring

/-- For unitary `V` and `W`, the distance of their group commutator from the identity is at most
`2 * ‖V - 1‖ * ‖W - 1‖`. -/
theorem norm_groupCommutator_sub_one_le {V W : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E) :
    ‖V * W * star V * star W - 1‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  rw [groupCommutator_sub_one_eq hV hW,
    norm_mul_mem_unitary _ (mul_mem (Unitary.star_mem hV) (Unitary.star_mem hW))]
  exact norm_mul_sub_mul_comm_le V W

/-- If two unitaries are each within `δ` of the identity, their group commutator is within `2 *
δ ^ 2` of the identity. -/
theorem norm_groupCommutator_sub_one_le_two_mul_sq {V W : E} (hV : V ∈ unitary E)
    (hW : W ∈ unitary E) {δ : ℝ} (hV' : ‖V - 1‖ ≤ δ) (hW' : ‖W - 1‖ ≤ δ) :
    ‖V * W * star V * star W - 1‖ ≤ 2 * δ ^ 2 := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hV'
  refine le_trans (norm_groupCommutator_sub_one_le hV hW) ?_
  calc 2 * ‖V - 1‖ * ‖W - 1‖ ≤ 2 * δ * δ := by gcongr
    _ = 2 * δ ^ 2 := by ring

/-- If `0 < δ < 1 / 2` and both unitaries are within `δ` of the identity, their group commutator
has distance strictly less than `δ` from the identity. -/
theorem norm_groupCommutator_sub_one_lt {V W : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    {δ : ℝ} (hpos : 0 < δ) (hhalf : δ < 1 / 2) (hV' : ‖V - 1‖ ≤ δ) (hW' : ‖W - 1‖ ≤ δ) :
    ‖V * W * star V * star W - 1‖ < δ := by
  refine lt_of_le_of_lt (norm_groupCommutator_sub_one_le_two_mul_sq hV hW hV' hW') ?_
  nlinarith

/-- The distance between `A * B` and `A' * B'` is at most `‖A - A'‖ + ‖B - B'‖` when `B` and
`A'` are unitary. -/
theorem norm_mul_sub_mul_le {A B A' B' : E} (hB : B ∈ unitary E) (hA' : A' ∈ unitary E) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ + ‖B - B'‖ := by
  have key : A * B - A' * B' = (A - A') * B + A' * (B - B') := by noncomm_ring
  rw [key]
  refine le_trans (norm_add_le _ _) (le_of_eq ?_)
  rw [norm_mul_mem_unitary _ hB, norm_mem_unitary_mul _ hA']

/-- If corresponding unitary factors differ by at most `ε`, their group commutators differ by at
most `4 * ε`. -/
theorem norm_groupCommutator_sub_groupCommutator_le {V W V' W' : E} (hV : V ∈ unitary E)
    (hW : W ∈ unitary E) (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E) {ε : ℝ}
    (hVe : ‖V - V'‖ ≤ ε) (hWe : ‖W - W'‖ ≤ ε) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖ ≤ 4 * ε := by
  have hstarV : ‖star V - star V'‖ ≤ ε := by
    rw [← star_sub, norm_star]
    exact hVe
  have hstarW : ‖star W - star W'‖ ≤ ε := by
    rw [← star_sub, norm_star]
    exact hWe
  have h1 : ‖V * W - V' * W'‖ ≤ ε + ε := by
    refine le_trans (norm_mul_sub_mul_le hW hV') ?_
    exact add_le_add hVe hWe
  have h2 : ‖V * W * star V - V' * W' * star V'‖ ≤ ε + ε + ε := by
    refine le_trans (norm_mul_sub_mul_le (Unitary.star_mem hV) (mul_mem hV' hW')) ?_
    exact add_le_add h1 hstarV
  refine le_trans (norm_mul_sub_mul_le (Unitary.star_mem hW)
    (mul_mem (mul_mem hV' hW') (Unitary.star_mem hV'))) ?_
  calc ‖V * W * star V - V' * W' * star V'‖ + ‖star W - star W'‖
      ≤ (ε + ε + ε) + ε := add_le_add h2 hstarW
    _ = 4 * ε := by ring

end CStarRing

end

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
