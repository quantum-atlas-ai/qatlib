/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSearch02.MainResults.WalkDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace Qatlib.Papers.QWalkSearch02.MainResults

lemma flipBit_swapBits {n : ℕ} (i j d : Fin n) (x : BitVec n) :
    swapBits i j (flipBit d x) = flipBit (Equiv.swap i j d) (swapBits i j x) := by
  funext k
  simp only [swapBits, flipBit, Equiv.swap_apply_eq_iff]

lemma shiftOp_swap {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) :
    shiftOp n (swapOp i j v) = swapOp i j (shiftOp n v) := by
  funext p
  obtain ⟨d, x⟩ := p
  simp only [shiftOp, swapOp, swapDir]
  rw [flipBit_swapBits]

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

theorem theorem1_perturbed_commutes_swap {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) :
    perturbedWalkOp n (swapOp i j v) = swapOp i j (perturbedWalkOp n v) := by
  unfold perturbedWalkOp
  rw [coinOp_swap, shiftOp_swap]

end Qatlib.Papers.QWalkSearch02.MainResults
