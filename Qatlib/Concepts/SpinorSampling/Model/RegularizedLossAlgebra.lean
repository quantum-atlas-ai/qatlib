/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# Regularized Loss Algebra

Regularized Loss Algebra constructions and identities for Spinor Sampling.
-/
set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.SpinorSampling.Model

/-- Construction for squared Derivative in the regularized loss algebra model. -/
def squaredDerivative (da db dc dd : ℝ) : ℝ := da^2 + db^2 + dc^2 + dd^2

/-- Construction for shifted Energy in the regularized loss algebra model. -/
def shiftedEnergy (a b c d da db dc dd κ t : ℝ) : ℝ :=
  (κ*da+t*b)^2 + (κ*db-t*a)^2 + (κ*dc+t*d)^2 + (κ*dd-t*c)^2

/-- Complete original `horizontal_identity` guarantee for `RegularizedLossAlgebra`; all source hypotheses and output obligations are retained. -/
theorem horizontal_identity (a b c d da db dc dd κ v : ℝ)
    (hnorm : a^2+b^2+c^2+d^2=1)
    (hcurrent : v=κ*(a*db-b*da+c*dd-d*dc)) :
    shiftedEnergy a b c d da db dc dd κ v =
      κ^2 * squaredDerivative da db dc dd - v^2 := by
  unfold shiftedEnergy squaredDerivative
  linear_combination v^2 * hnorm + 2*v * hcurrent

/-- Complete original `unit_regularizer_is_quadratic` guarantee for `RegularizedLossAlgebra`; all source hypotheses and output obligations are retained. -/
theorem unit_regularizer_is_quadratic (a b c d da db dc dd κ v u : ℝ)
    (hnorm : a^2+b^2+c^2+d^2=1)
    (hcurrent : v=κ*(a*db-b*da+c*dd-d*dc)) :
    (v-u)^2 + shiftedEnergy a b c d da db dc dd κ v =
      shiftedEnergy a b c d da db dc dd κ u := by
  unfold shiftedEnergy
  linear_combination (v^2-u^2)*hnorm + 2*(v-u)*hcurrent


open scoped BigOperators

/-- Construction for central Difference in the regularized loss algebra model. -/
def centralDifference {N : ℕ} [NeZero N] (h : ℝ) (f : Fin N → ℝ) (j : Fin N) : ℝ :=
  (f (j+1)-f (j-1))/(2*h)

/-- Construction for grid Velocity in the regularized loss algebra model. -/
def gridVelocity {N : ℕ} [NeZero N] (κ h : ℝ)
    (a b c d : Fin N → ℝ) (j : Fin N) : ℝ :=
  κ*(a j * centralDifference h b j - b j * centralDifference h a j +
    c j * centralDifference h d j - d j * centralDifference h c j)

/-- Construction for grid Shifted Energy in the regularized loss algebra model. -/
def gridShiftedEnergy {N : ℕ} [NeZero N] (κ h : ℝ)
    (a b c d t : Fin N → ℝ) (j : Fin N) : ℝ :=
  shiftedEnergy (a j) (b j) (c j) (d j)
    (centralDifference h a j) (centralDifference h b j)
    (centralDifference h c j) (centralDifference h d j) κ (t j)

/-- Complete original `periodic_grid_unit_regularizer` guarantee for `RegularizedLossAlgebra`; all source hypotheses and output obligations are retained. -/
theorem periodic_grid_unit_regularizer {N : ℕ} [NeZero N] (κ h : ℝ)
    (a b c d u : Fin N → ℝ)
    (hnorm : ∀ j, (a j)^2+(b j)^2+(c j)^2+(d j)^2=1) :
    (∑ j : Fin N, ((gridVelocity κ h a b c d j-u j)^2 +
      gridShiftedEnergy κ h a b c d (gridVelocity κ h a b c d) j)) =
    ∑ j : Fin N, gridShiftedEnergy κ h a b c d u j := by
  apply Finset.sum_congr rfl
  intro j _
  exact unit_regularizer_is_quadratic (a j) (b j) (c j) (d j)
    (centralDifference h a j) (centralDifference h b j)
    (centralDifference h c j) (centralDifference h d j)
    κ (gridVelocity κ h a b c d j) (u j) (hnorm j) rfl

#print axioms Qatlib.Concepts.SpinorSampling.Model.periodic_grid_unit_regularizer

#print axioms Qatlib.Concepts.SpinorSampling.Model.horizontal_identity
#print axioms Qatlib.Concepts.SpinorSampling.Model.unit_regularizer_is_quadratic
#eval Lean.versionString

end Qatlib.Concepts.SpinorSampling.Model
