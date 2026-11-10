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
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace Qatlib.Foundations.MatrixAlgebra.TensorDiff

abbrev Tensor (q N : ℕ) := (Fin q → Fin N) → ℝ

def tensorEnergy {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) : ℝ :=
  ∑ k, J k * ∏ a, z (k a)

def tensorDirectional {q N : ℕ} (J : Tensor q N) (z v : Fin N → ℝ) : ℝ :=
  ∑ k, J k * ∑ a, (∏ b ∈ Finset.univ.erase a, z (k b)) * v (k a)

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

def tensorGradient {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) (i : Fin N) : ℝ :=
  tensorDirectional J z (Pi.single i 1)

theorem tensor_gradient_partial {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun t : ℝ => tensorEnergy J (fun j => z j+t*((Pi.single i (1:ℝ) : Fin N → ℝ) j)))
      (tensorGradient J z i) 0 := tensor_energy_hasDerivAt J z _

def interaction {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (z : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ k, J i k * ∏ a, z (k a)

theorem continuous_interaction {r N : ℕ} :
    Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin N → ℝ) =>
      interaction p.1 p.2) := by
  apply continuous_pi
  intro i
  unfold interaction
  fun_prop

theorem continuous_tensorEnergy {q N : ℕ} :
    Continuous (fun p : Tensor q N × (Fin N → ℝ) => tensorEnergy p.1 p.2) := by
  unfold tensorEnergy
  fun_prop

theorem tensorEnergy_single {q N : ℕ} (u : Fin q → Fin N) (c : ℝ) (z : Fin N → ℝ) :
    tensorEnergy (Pi.single u c) z=c*∏ a,z (u a) := by
  classical
  simp [tensorEnergy,Pi.single_apply]

theorem tensorDirectional_single {q N : ℕ} (u : Fin q → Fin N) (c : ℝ) (z v : Fin N → ℝ) :
    tensorDirectional (Pi.single u c) z v=
      c*∑ a,(∏ b∈Finset.univ.erase a,z (u b))*v (u a) := by
  classical
  simp [tensorDirectional,Pi.single_apply]

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
