/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Cor54

/-!
# Euclidean-norm scale for difference models

Defines real Boltzmann edge weights `edgeWeight`, their Euclidean norms `energyNorm`, and the
scale expressions used in Corollary 5.9 of [AradLandau2010]. The four-plane product
`bubblePlaneScale` carries a factor `(√q)^(n - 1)`.

For positive `n`, multiplying the four-plane scale by `q` gives `differenceScale`, whose power
of `√q` is `n + 1`.

## Main statements

* `corollary5_9_four_plane_norms`: simplifies the four-plane norm product.
* `corollary5_9_bubbling_scale`: accounts for the additional factor `q`.
* `corollary5_9_difference_scale`: specializes the scale to the color cardinality.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor59

open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
open Qatlib.Papers.TensorNetwork08.MainResults.Norm

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

/-- The real Boltzmann weight `exp (-β * h e j)` for an edge label. -/
noncomputable def edgeWeight (h : E → C → ℝ) (β : ℝ) (e : E) (j : C) : ℝ :=
  Real.exp (-(β * h e j))

/-- The Euclidean norm of the real Boltzmann edge-weight vector. -/
noncomputable def energyNorm (h : E → C → ℝ) (β : ℝ) (e : E) : ℝ :=
  Real.sqrt (∑ j : C, |edgeWeight h β e j| ^ 2)

/-- The difference-model scale `(√q)^(n + 1)` multiplied by the product of all edge-weight
Euclidean norms. -/
noncomputable def differenceScale (q n : ℕ) (h : E → C → ℝ) (β : ℝ) : ℝ :=
  (Real.sqrt (q : ℝ)) ^ (n + 1) * ∏ e : E, energyNorm h β e

/-- The four-plane scale `(√q)^(n - 1)` multiplied by the product of all edge-weight Euclidean
norms. -/
noncomputable def bubblePlaneScale (q n : ℕ) (h : E → C → ℝ) (β : ℝ) : ℝ :=
  (Real.sqrt (q : ℝ)) ^ (n - 1) * ∏ e : E, energyNorm h β e

/-- The four-plane product with its two families of unit factors equals `bubblePlaneScale`. See
[AradLandau2010]. -/
theorem corollary5_9_four_plane_norms (q n m₁ m₂ : ℕ) (h : E → C → ℝ) (β : ℝ) :
    (Real.sqrt (q : ℝ)) ^ (n - 1) * (1 : ℝ) ^ m₁ * (1 : ℝ) ^ m₂ * ∏ e : E, energyNorm h β e
      = bubblePlaneScale q n h β := by
  simp [bubblePlaneScale]

/-- For positive vertex count `n`, multiplying `bubblePlaneScale` by `q` yields
`differenceScale`. See [AradLandau2010]. -/
theorem corollary5_9_bubbling_scale {q n : ℕ} (hn : 0 < n) (hq : 0 ≤ (q : ℝ))
    (h : E → C → ℝ) (β : ℝ) :
    (q : ℝ) * bubblePlaneScale q n h β = differenceScale q n h β := by
  unfold bubblePlaneScale differenceScale
  have hpow : (q : ℝ) = (Real.sqrt (q : ℝ)) ^ 2 := (Real.sq_sqrt hq).symm
  have hstep : (q : ℝ) * (Real.sqrt (q : ℝ)) ^ (n - 1) = (Real.sqrt (q : ℝ)) ^ (n + 1) := by
    nth_rewrite 1 [hpow]
    rw [← pow_add]
    congr 1
    omega
  calc (q : ℝ) * ((Real.sqrt (q : ℝ)) ^ (n - 1) * ∏ e : E, energyNorm h β e)
      = ((q : ℝ) * (Real.sqrt (q : ℝ)) ^ (n - 1)) * ∏ e : E, energyNorm h β e := by ring
    _ = (Real.sqrt (q : ℝ)) ^ (n + 1) * ∏ e : E, energyNorm h β e := by rw [hstep]

/-- At `q = Fintype.card C`, expands the difference-model scale into the square-root cardinality
factor and the product of edge norms. -/
theorem corollary5_9_difference_scale (h : E → C → ℝ) (β : ℝ) (n : ℕ) :
    differenceScale (Fintype.card C) n h β
      = (Real.sqrt (Fintype.card C : ℝ)) ^ (n + 1) * ∏ e : E, energyNorm h β e := rfl

end Qatlib.Papers.TensorNetwork08.MainResults.Cor59
