/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Integrated distance and overlap-sum estimates

This module proves the real-variable integration step `lemma1_permutation_distance` from an
assumed derivative bound and zero initial value. It also proves `sum_norm_inner_le`, a finite
Cauchy–Schwarz estimate for sums of absolute inner products used in the permutation-distance
argument. The mathematical context is [FarhiGoldstoneGutmannNagaj2008].

## Main statements

* `lemma1_permutation_distance`: For nonnegative `T`, a function continuous on `[0, T]`,
  differentiable in its interior, zero at zero, and with derivative at most `4 * hstar *
  Real.sqrt (Nat.factorial N) * Real.sqrt (N - 1)` satisfies the corresponding bound multiplied
  by `T` at its endpoint.
* `sum_norm_inner_le`: The sum of the norms of inner products over a finite set is at most the
  product of the square roots of the two sums of squared vector norms.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmannNagaj2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.MainResults

open scoped BigOperators ComplexInnerProductSpace
open Finset

/-- For nonnegative `T`, a function continuous on `[0, T]`, differentiable in its interior, zero
at zero, and with derivative at most `4 * hstar * Real.sqrt (Nat.factorial N) * Real.sqrt (N
- 1)` satisfies the corresponding bound multiplied by `T` at its endpoint
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem lemma1_permutation_distance
    (F : ℝ → ℝ) (N : ℕ) (T hstar : ℝ) (_hN : 1 ≤ N) (hT : 0 ≤ T)
    (hcont : ContinuousOn F (Set.Icc 0 T))
    (hdiff : DifferentiableOn ℝ F (interior (Set.Icc 0 T)))
    (hF0 : F 0 = 0)
    (hderiv : ∀ t ∈ interior (Set.Icc 0 T),
        deriv F t ≤ 4 * hstar * Real.sqrt (Nat.factorial N : ℝ) * Real.sqrt ((N : ℝ) - 1)) :
    F T ≤ 4 * hstar * T * Real.sqrt (Nat.factorial N : ℝ) * Real.sqrt ((N : ℝ) - 1) := by

  have key := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc 0 T) hcont hdiff hderiv
    0 ⟨le_refl 0, hT⟩ T ⟨hT, le_refl T⟩ hT

  nlinarith [key, hF0]

/-- The sum of the norms of inner products over a finite set is at most the product of the
square roots of the two sums of squared vector norms [FarhiGoldstoneGutmannNagaj2008]. -/
theorem sum_norm_inner_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} (s : Finset ι) (u v : ι → V) :
    ∑ i ∈ s, ‖⟪u i, v i⟫‖
      ≤ Real.sqrt (∑ i ∈ s, ‖u i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
  have h1 : ∑ i ∈ s, ‖⟪u i, v i⟫‖ ≤ ∑ i ∈ s, ‖u i‖ * ‖v i‖ :=
    Finset.sum_le_sum fun i _ => norm_inner_le_norm _ _
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖u i‖) (fun i => ‖v i‖))

end Qatlib.Papers.AdiabaticFail05.MainResults
