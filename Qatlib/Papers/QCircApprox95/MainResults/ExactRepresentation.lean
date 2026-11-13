/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Parameter counts and prefix projection kernels

The module records the scalar parameter counts for U(4) and U(2), together with their elementary
phase reductions. It also defines `prefixProjection` and proves a lower bound on the kernel
dimension of its difference from a rectangular matrix, as used in exact unitary completion. See
[Knill1995].

## Main statements

* `lemma_three_two_nullity`: bounds the kernel dimension below by m − k.
* `lemma_three_two_first_rows`: identifies the first rows under the prefix projection equation.

## References

* [Knill, 1995][Knill1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LocalCircuits.LocalGateCosts
open Matrix

namespace Qatlib.Papers.QCircApprox95.MainResults

/-- The value sixteen used for the source parameter count of U(4). -/
def sourceU4Params : ℕ := 16

/-- The value four used for the source parameter count of U(2). -/
def sourceU2Params : ℕ := 4

/-- Removing one phase parameter from `sourceU4Params` leaves at most fifteen parameters. -/
theorem phase_parameter_arithmetic : sourceU4Params - 1 ≤ 15 := by
  norm_num [sourceU4Params]

/-- Subtracting the phase-reduced U(2) count from the phase-reduced U(4) count leaves at most
twelve parameters. -/
theorem one_input_parameter_arithmetic : sourceU4Params - 1 - (sourceU2Params - 1) ≤ 12 := by
  norm_num [sourceU4Params, sourceU2Params]

/-- Subtracting two phase-reduced U(2) counts from the phase-reduced U(4) count leaves at most
nine parameters. -/
theorem two_input_parameter_arithmetic :
    sourceU4Params - 1 - 2 * (sourceU2Params - 1) ≤ 9 := by
  norm_num [sourceU4Params, sourceU2Params]

/-- The rectangular coordinate projection with entry one exactly when the row and column have
the same natural-number index. -/
def prefixProjection (k m : ℕ) : Matrix (Fin k) (Fin m) ℂ :=
  fun i j => if (j : ℕ) = (i : ℕ) then 1 else 0

/-- For `k ≤ m`, the kernel of the linear map associated with `V - prefixProjection k m` has
complex dimension at least `m - k`. This is the dimension estimate used in Lemma 3.2 of
[Knill1995]. -/
theorem lemma_three_two_nullity (k m : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin m) ℂ) :
    m - k ≤ Module.finrank ℂ
      (LinearMap.ker (V - prefixProjection k m).mulVecLin) := by
  set W := V - prefixProjection k m with hW
  have h := LinearMap.finrank_range_add_finrank_ker (f := W.mulVecLin)
  have hm : Module.finrank ℂ (Fin m → ℂ) = m := by simp
  have hk' : Module.finrank ℂ (Fin k → ℂ) = k := by simp
  have hle : Module.finrank ℂ (LinearMap.range W.mulVecLin) ≤ k := by
    have hr := Submodule.finrank_le (LinearMap.range W.mulVecLin)
    rw [hk'] at hr
    exact hr
  have hker_eq : Module.finrank ℂ (LinearMap.ker W.mulVecLin)
      = m - Module.finrank ℂ (LinearMap.range W.mulVecLin) := by
    rw [hm] at h
    omega
  rw [hker_eq]
  omega

/-- The matrix equation `(V - prefixProjection k m) * X = 0` is equivalent to `V * X =
prefixProjection k m * X`. -/
theorem sub_prefixProjection_mul_eq_zero_iff (k m r : ℕ)
    (V : Matrix (Fin k) (Fin m) ℂ) (X : Matrix (Fin m) (Fin r) ℂ) :
    (V - prefixProjection k m) * X = 0 ↔ V * X = prefixProjection k m * X := by
  rw [Matrix.sub_mul, sub_eq_zero]

/-- When `k ≤ m`, left multiplication by `prefixProjection k m` selects the first `k` rows of
`X`. -/
theorem prefixProjection_mul_apply (k m r : ℕ) (hk : k ≤ m)
    (X : Matrix (Fin m) (Fin r) ℂ) (i : Fin k) (j : Fin r) :
    (prefixProjection k m * X) i j = X ⟨i.1, lt_of_lt_of_le i.2 hk⟩ j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨i.1, lt_of_lt_of_le i.2 hk⟩]
  · simp [prefixProjection]
  · intro a _ ha
    have hv : ¬ ((a : ℕ) = (i : ℕ)) := by
      intro h
      exact ha (Fin.ext h)
    simp [prefixProjection, hv]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- If `V * X = prefixProjection k m * X` and `k ≤ m`, each entry of `V * X` is the
corresponding entry in the first `k` rows of `X`. This is the prefix-row identity used in
Lemma 3.2 of [Knill1995]. -/
theorem lemma_three_two_first_rows (k m r : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin m) ℂ) (X : Matrix (Fin m) (Fin r) ℂ)
    (hX : V * X = prefixProjection k m * X) (i : Fin k) (j : Fin r) :
    (V * X) i j = X ⟨i.1, lt_of_lt_of_le i.2 hk⟩ j := by
  rw [hX, prefixProjection_mul_apply k m r hk X i j]

end Qatlib.Papers.QCircApprox95.MainResults
