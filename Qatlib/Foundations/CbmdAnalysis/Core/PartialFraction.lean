/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Complex.Basic

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section

namespace CBMD

open scoped BigOperators

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

theorem finite_pole_weight_eq_derivative_inv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℂ) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s.erase i, (v i - v j))⁻¹ =
      (Polynomial.eval (v i) (Polynomial.derivative (Lagrange.nodal s v)))⁻¹ := by
  simpa only [Lagrange.nodalWeight, Finset.prod_inv_distrib] using
    Lagrange.nodalWeight_eq_eval_derivative_nodal (v := v) hi

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
