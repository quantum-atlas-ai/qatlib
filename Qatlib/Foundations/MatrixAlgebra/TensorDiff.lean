/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Differentiation of ordered tensor energies

`Tensor` and `tensorEnergy` encode homogeneous real polynomial energies indexed by ordered
tuples. `tensorDirectional` sums the contribution from differentiating each slot, and
`tensorGradient` specializes this derivative to coordinate directions without a symmetry
assumption on the tensor.

The module proves directional derivative formulas, joint continuity in coefficients and
coordinates, and single-entry and quadratic special cases. These calculations apply to the
tensor energy models in [GohMuller2026].

## Main statements

* `tensor_energy_hasDerivAt`: the slotwise formula differentiates the energy along a line.
* `tensor_gradient_partial`: coordinate directions give the defined gradient entries.
* `quadratic_directional`: the explicit derivative of a real quadratic matrix energy.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace Qatlib.Foundations.MatrixAlgebra.TensorDiff

/-- A real tensor indexed by ordered `q`-tuples of coordinates in `Fin N`. -/
abbrev Tensor (q N : ℕ) := (Fin q → Fin N) → ℝ

/-- The homogeneous polynomial obtained by contracting each ordered tensor entry with the
product of its selected coordinates. -/
def tensorEnergy {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) : ℝ :=
  ∑ k, J k * ∏ a, z (k a)

/-- The slotwise directional derivative formula for the ordered tensor energy, summed over all
tuples and differentiated slots. -/
def tensorDirectional {q N : ℕ} (J : Tensor q N) (z v : Fin N → ℝ) : ℝ :=
  ∑ k, J k * ∑ a, (∏ b ∈ Finset.univ.erase a, z (k b)) * v (k a)

/-- Along the line `z + t * v`, the tensor energy has derivative `tensorDirectional J z v` at
zero. This supplies the ordered tensor differentiation used in [GohMuller2026]. -/
theorem tensor_energy_hasDerivAt {q N : ℕ} (J : Tensor q N) (z v : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => tensorEnergy J (fun i => z i+t*v i))
      (tensorDirectional J z v) 0 := by
  have hp (k : Fin q → Fin N) : HasDerivAt
      (fun t : ℝ => J k * ∏ a, (z (k a)+t*v (k a)))
      (J k * ∑ a, (∏ b ∈ Finset.univ.erase a, z (k b))*v (k a)) 0 := by
    have hz (a : Fin q) : HasDerivAt (fun t : ℝ => z (k a)+t*v (k a)) (v (k a)) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v (k a))).const_add (z (k a))
    simpa only [zero_mul, add_zero, smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun a _ => hz a)).const_mul (J k)
  exact HasDerivAt.fun_sum (u:=Finset.univ) (fun k _ => hp k)

/-- The directional derivative formula evaluated at the coordinate basis vector for `i`. -/
def tensorGradient {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) (i : Fin N) : ℝ :=
  tensorDirectional J z (Pi.single i 1)

/-- The derivative of the tensor energy in coordinate direction `i` at zero is `tensorGradient J
z i`, for the tensor energy setting of [GohMuller2026]. -/
theorem tensor_gradient_partial {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun t : ℝ => tensorEnergy J (fun j => z j+t*((Pi.single i (1:ℝ) : Fin N → ℝ) j)))
      (tensorGradient J z i) 0 := tensor_energy_hasDerivAt J z _

/-- The vector-valued contraction obtained by fixing the output index and summing each tensor
slice against products of `r` coordinates. -/
def interaction {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (z : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ k, J i k * ∏ a, z (k a)

/-- The interaction vector depends continuously on both the tensor coefficients and the input
coordinates. -/
theorem continuous_interaction {r N : ℕ} :
    Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin N → ℝ) =>
      interaction p.1 p.2) := by
  apply continuous_pi
  intro i
  unfold interaction
  fun_prop

/-- The tensor energy depends continuously on both its tensor coefficients and its input
coordinates. -/
theorem continuous_tensorEnergy {q N : ℕ} :
    Continuous (fun p : Tensor q N × (Fin N → ℝ) => tensorEnergy p.1 p.2) := by
  unfold tensorEnergy
  fun_prop

/-- A tensor supported at one ordered tuple has energy equal to its coefficient times the
corresponding coordinate monomial. -/
theorem tensorEnergy_single {q N : ℕ} (u : Fin q → Fin N) (c : ℝ) (z : Fin N → ℝ) :
    tensorEnergy (Pi.single u c) z=c*∏ a,z (u a) := by
  classical
  simp [tensorEnergy,Pi.single_apply]

/-- The directional derivative formula for a tensor supported at one tuple is its coefficient
times the sum of the slotwise differentiated monomials. -/
theorem tensorDirectional_single {q N : ℕ} (u : Fin q → Fin N) (c : ℝ) (z v : Fin N → ℝ) :
    tensorDirectional (Pi.single u c) z v=
      c*∑ a,(∏ b∈Finset.univ.erase a,z (u b))*v (u a) := by
  classical
  simp [tensorDirectional,Pi.single_apply]

/-- The derivative at zero of the quadratic energy along `z + t * v` is the sum of the two terms
obtained by differentiating each factor, without requiring matrix symmetry. -/
theorem quadratic_directional {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z v : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ i, ∑ j, A i j*(z i+t*v i)*(z j+t*v j))
      (∑ i, ∑ j, A i j*(v i*z j+z i*v j)) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have hi : HasDerivAt (fun t : ℝ => z i+t*v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (z i)
  have hj : HasDerivAt (fun t : ℝ => z j+t*v j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (z j)
  convert! (hi.const_mul (A i j)).mul hj using 1; (try simp); ring

end Qatlib.Foundations.MatrixAlgebra.TensorDiff
