/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.LchsRep.ImaginaryTimeProduct

/-!
# Exact imaginary-time products for commuting matrices

`imaginary_product_commuting_exact_consumer` specializes the imaginary-time product error
theorem to commuting positive semidefinite matrices. For positive repetition count and
nonnegative time, the finite product equals the exact exponential. See [ChildsEtAl2021Trotter]
for the mathematical setting.

## Main statements

* `imaginary_product_commuting_exact_consumer`: For commuting positive semidefinite `A` and `B`,
  nonnegative `t`, and positive `r`, `imaginaryRun A B t r` equals `exp (-t • (A + B))`.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.LchsSimulation.LchsRep

open Matrix
open scoped Classical Matrix.Norms.L2Operator ComplexOrder

/-- For commuting positive semidefinite `A` and `B`, nonnegative `t`, and positive `r`,
`imaginaryRun A B t r` equals `exp (-t • (A + B))`. See [ChildsEtAl2021Trotter]. -/
theorem imaginary_product_commuting_exact_consumer :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
      (t : ℝ) (r : ℕ), A.PosSemidef → B.PosSemidef → 0 ≤ t → 0 < r →
      A * B = B * A → imaginaryRun A B t r = NormedSpace.exp (-t • (A + B)) := by
  intro I _ _ A B t r hA hB ht hr hcomm
  have h := (imaginary_product_contraction_and_commutator_error I A B t r hA hB ht hr).2.2
  rw [hcomm, sub_self, norm_zero, mul_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end Qatlib.Concepts.LchsSimulation.LchsRep
