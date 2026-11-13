/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSearch02.MainResults.WalkDefs

/-!
# Coordinate-swap symmetry of the search walk

Bit flips transform equivariantly under coordinate swaps, making both the hypercube shift and
the marked coin commute with the induced swap operator. Their composition therefore has the
symmetry stated in Theorem 1 of [ShenviKempeWhaley2003].

## Main statements

* `flipBit_swapBits`: relates a swapped bit flip to the corresponding swapped direction.
* `theorem1_perturbed_commutes_swap`: proves commutation of the perturbed walk with coordinate
  swaps.

## References

* [Shenvi et al., 2003][ShenviKempeWhaley2003]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace Qatlib.Papers.QWalkSearch02.MainResults

/-- Swapping coordinates after flipping bit `d` equals flipping the swapped direction after
swapping coordinates. -/
lemma flipBit_swapBits {n : ℕ} (i j d : Fin n) (x : BitVec n) :
    swapBits i j (flipBit d x) = flipBit (Equiv.swap i j d) (swapBits i j x) := by
  funext k
  simp only [swapBits, flipBit, Equiv.swap_apply_eq_iff]

/-- The hypercube shift commutes with the simultaneous swap of direction and bit coordinates. -/
lemma shiftOp_swap {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) :
    shiftOp n (swapOp i j v) = swapOp i j (shiftOp n v) := by
  funext p
  obtain ⟨d, x⟩ := p
  simp only [shiftOp, swapOp, swapDir]
  rw [flipBit_swapBits]

/-- The marked coin operator commutes with the simultaneous swap of direction and bit
coordinates. -/
lemma coinOp_swap {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) :
    coinOp n (swapOp i j v) = swapOp i j (coinOp n v) := by
  funext p
  obtain ⟨d, x⟩ := p
  simp only [coinOp, swapOp]
  by_cases hx : x = zeroVec n
  · subst hx
    simp [swapBits_zero]
  · have hx' : swapBits i j x ≠ zeroVec n := by
      intro h
      exact hx ((swapBits_eq_zero_iff i j x).mp h)
    simp only [hx, hx', if_false, swapDir]

    conv_rhs =>
      rw [← Equiv.sum_comp (Equiv.swap i j)
        (fun d' => groverEntry n (Equiv.swap i j d) d' * v (d', swapBits i j x))]
    refine Finset.sum_congr rfl ?_
    intro d' _
    rw [groverEntry_swap]

/-- The perturbed hypercube walk commutes with every coordinate-swap operator. See [Shenvi et
al., Theorem 1][ShenviKempeWhaley2003]. -/
theorem theorem1_perturbed_commutes_swap {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) :
    perturbedWalkOp n (swapOp i j v) = swapOp i j (perturbedWalkOp n v) := by
  unfold perturbedWalkOp
  rw [coinOp_swap, shiftOp_swap]

end Qatlib.Papers.QWalkSearch02.MainResults
