/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Examples

/-!
# Image closures and spectral obstructions

`ImageClosure` is the topological closure of a paired five- and eight-dimensional matrix image.
This module proves its elementary closure properties and spectral obstructions used in the
density discussion of [FreedmanLarsenWang2000].

The spectral lemmas rule out closure of a set of the form `{-1, q}` under certain scalar
multiplications.

## Main statements

* `theorem4_1_isClosed`: The paired image closure is closed.
* `theorem4_1_negation_twist_forces_one`: Negation closure forces `q = 1`.
* `theorem4_1_no_fifth_root_multiplicative_closure`: A nontrivial fifth root cannot preserve the
  two-element spectral set.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Density

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.ModularFunct00.MainResults.Examples

/-- The topological closure of the paired matrix image `b ↦ (ρ5 b, ρ8 b)`. -/
def ImageClosure {G : Type*} [Group G] (ρ5 : G → CM 5) (ρ8 : G → CM 8) :
    Set (CM 5 × CM 8) :=
  closure (Set.range (fun b : G => (ρ5 b, ρ8 b)))

/-- Every point of the paired matrix image belongs to `ImageClosure`; see
[FreedmanLarsenWang2000]. -/
theorem theorem4_1_image_subset_closure {G : Type*} [Group G]
    (ρ5 : G → CM 5) (ρ8 : G → CM 8) :
    Set.range (fun b : G => (ρ5 b, ρ8 b)) ⊆ ImageClosure ρ5 ρ8 :=
  subset_closure

/-- The set `ImageClosure ρ5 ρ8` is topologically closed; see [FreedmanLarsenWang2000]. -/
theorem theorem4_1_isClosed {G : Type*} [Group G]
    (ρ5 : G → CM 5) (ρ8 : G → CM 8) :
    IsClosed (ImageClosure ρ5 ρ8) :=
  isClosed_closure

/-- If `q` is a nontrivial fifth root of unity, the ratio `q / (-1)` is neither one nor minus
one; see [FreedmanLarsenWang2000]. -/
theorem theorem4_1_eigenvalue_ratio_not_pm_one {q : ℂ} (hq5 : q ^ 5 = 1)
    (hq1 : q ≠ 1) :
    q / (-1) ≠ 1 ∧ q / (-1) ≠ -1 :=
  fiveRoot_ratio_ne_pm_one hq5 hq1

/-- Closure of the set `{-1, q}` under negation forces `q = 1`; see [FreedmanLarsenWang2000]. -/
theorem theorem4_1_negation_twist_forces_one {q : ℂ}
    (h : ∀ μ ∈ ({(-1 : ℂ), q} : Set ℂ), -μ ∈ ({(-1 : ℂ), q} : Set ℂ)) :
    q = 1 :=
  negation_closed_two_element_forces_one h

/-- Multiplication by a nontrivial fifth root of unity cannot preserve the set `{-1, q}`; see
[FreedmanLarsenWang2000]. -/
theorem theorem4_1_no_fifth_root_multiplicative_closure {q : ℂ} (ω : ℂ)
    (hω5 : ω ^ 5 = 1) (hω1 : ω ≠ 1) :
    ¬ ∀ μ ∈ ({(-1 : ℂ), q} : Set ℂ), ω * μ ∈ ({(-1 : ℂ), q} : Set ℂ) :=
  not_mul_closed_two_element_fifth_root ω hω5 hω1

end Qatlib.Papers.ModularFunct00.MainResults.Density
