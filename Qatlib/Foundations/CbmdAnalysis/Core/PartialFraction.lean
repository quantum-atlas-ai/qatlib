/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Complex.Basic

/-!
# Partial fractions for finite simple pole sets

`finite_simple_pole_partial_fraction` decomposes the reciprocal of a finite product of distinct
linear factors into simple fractions. Each coefficient is the reciprocal product of separations
from the corresponding pole.

`finite_pole_weight_eq_derivative_inv` identifies this coefficient with the reciprocal
derivative of the Lagrange nodal polynomial at that pole. These algebraic identities provide the
finite residue weights used in [WangEtAl2026].

## Main statements

* `finite_simple_pole_partial_fraction`: gives the finite simple-fraction expansion.
* `finite_pole_weight_eq_derivative_inv`: relates pole weights to polynomial derivatives.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section

namespace CBMD

open scoped BigOperators

/-- For a nonempty finite set of distinct poles and `z` away from them, the reciprocal pole
product equals the sum of simple fractions with coefficients given by reciprocal
pole-separation products. -/
theorem finite_simple_pole_partial_fraction {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℂ) (hs : s.Nonempty) (hv : Set.InjOn v s)
    (z : ℂ) (hz : ∀ i ∈ s, z ≠ v i) :
    (∏ i ∈ s, (z - v i))⁻¹ =
      ∑ i ∈ s, (∏ j ∈ s.erase i, (v i - v j))⁻¹ * (z - v i)⁻¹ := by
  have he := Lagrange.eval_interpolate_not_at_node (1 : ι → ℂ) hz
  simp only [Lagrange.interpolate_one hv hs, Polynomial.eval_one, Pi.one_apply,
    mul_one, Lagrange.eval_nodal, Lagrange.nodalWeight, Finset.prod_inv_distrib] at he
  have hn : (∏ i ∈ s, (z - v i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (hz i hi)
  apply (mul_left_cancel₀ hn)
  rw [mul_inv_cancel₀ hn]
  exact he

/-- At a pole indexed by `i ∈ s`, the reciprocal product of separations from the other indexed
poles equals the reciprocal derivative of the Lagrange nodal polynomial evaluated there. -/
theorem finite_pole_weight_eq_derivative_inv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℂ) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s.erase i, (v i - v j))⁻¹ =
      (Polynomial.eval (v i) (Polynomial.derivative (Lagrange.nodal s v)))⁻¹ := by
  simpa only [Lagrange.nodalWeight, Finset.prod_inv_distrib] using
    Lagrange.nodalWeight_eq_eval_derivative_nodal (v := v) hi

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
