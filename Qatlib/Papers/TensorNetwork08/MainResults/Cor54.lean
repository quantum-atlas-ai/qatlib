/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Norm

/-!
# General-model tensor-network scale

Defines `generalModelScale` as the product of edge norms multiplied by `√q` for each of `b`
extreme vertices, following the scale calculation of Corollary 5.4 in [AradLandau2010]. The
identities record the unit intermediate factors and simplify the expression at `b = 2`.

The module also records the Euclidean norm of an all-ones diagonal tensor and the independence
of that norm from the number of tensor indices for fixed diagonal coefficients.

## Main statements

* `corollary5_4_general_model_scale`: includes the unit intermediate factors in the scale.
* `extreme_vertex_norm`: computes the norm of the all-ones diagonal tensor.
* `corollary5_4_finite_lattice_scale`: simplifies the scale for two extreme vertices.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor54

open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
open Qatlib.Papers.TensorNetwork08.MainResults.Norm

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The scale `(√q)^b` multiplied by the product of the supplied edge norms. -/
noncomputable def generalModelScale (q b : ℕ) (eNorm : E → ℝ) : ℝ :=
  (Real.sqrt q) ^ b * ∏ e : E, eNorm e

/-- The product of the extreme-vertex factor, any number of unit factors, and the edge norms
equals `generalModelScale`. See [AradLandau2010]. -/
theorem generalModelScale_eq_bubble_prod (q b m : ℕ) (eNorm : E → ℝ) :
    (Real.sqrt q) ^ b * (1 : ℝ) ^ m * ∏ e : E, eNorm e
      = generalModelScale q b eNorm := by
  simp [generalModelScale]

/-- Expands the general-model scale with an explicit factor `1^m` for the intermediate
contributions. -/
theorem corollary5_4_general_model_scale (q b m : ℕ) (eNorm : E → ℝ) :
    generalModelScale q b eNorm
      = (Real.sqrt q) ^ b * (1 : ℝ) ^ m * ∏ e : E, eNorm e :=
  (generalModelScale_eq_bubble_prod q b m eNorm).symm

/-- The Euclidean tensor norm of the diagonal tensor with every diagonal coefficient equal to
one is the square root of the color count. -/
theorem extreme_vertex_norm {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] (a : Fin n) :
    tensorNorm (diagTensor a (fun _ : C => (1 : ℂ))) = Real.sqrt (Fintype.card C) :=
  deltaTensor_norm a

/-- Diagonal tensors with the same coefficient vector have equal Euclidean tensor norms
regardless of their numbers of indices. -/
theorem identity_vertex_norm {n m : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (a : Fin n) (b : Fin m) (α : C → ℂ) :
    tensorNorm (diagTensor a α) = tensorNorm (diagTensor b α) :=
  identityTensor_norm_eq a b α

/-- With two extreme vertices, the general-model scale equals `q` times the product of edge
norms. See [AradLandau2010]. -/
theorem corollary5_4_finite_lattice_scale (q : ℕ) (eNorm : E → ℝ) :
    generalModelScale q 2 eNorm = (q : ℝ) * ∏ e : E, eNorm e := by
  unfold generalModelScale
  rw [show (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) from Real.sq_sqrt (Nat.cast_nonneg q)]

end Qatlib.Papers.TensorNetwork08.MainResults.Cor54
