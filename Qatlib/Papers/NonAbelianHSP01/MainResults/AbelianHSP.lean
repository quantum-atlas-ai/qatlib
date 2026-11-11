/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

/-!
# Hidden subgroups and stabilizers

Characterizes a hidden subgroup as the right stabilizer of its hiding function and proves
uniqueness from pointwise equality of hiding values. In a commutative ambient group,
`hidden_subgroup_normal_of_commutative` supplies normality. See [IvanyosMagniezSantha2003] for
the surrounding analysis.

## Main statements

* `hidden_subgroup_eq_right_stabilizer`: A hidden subgroup is exactly the set of elements whose
  right multiplication preserves every value of its hiding function.
* `hidden_subgroup_determined_by_hiding_values`: Two hidden-subgroup instances with pointwise
  equal hiding functions have equal hidden subgroups.
* `hidden_subgroup_normal_of_commutative`: A hidden subgroup in a commutative group is normal.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults

section AbelianHSP

variable {G : Type*} [Group G] {X : Type*}

/-- A hidden subgroup is exactly the set of elements whose right multiplication preserves every
value of its hiding function [IvanyosMagniezSantha2003]. -/
theorem hidden_subgroup_eq_right_stabilizer (I : HiddenSubgroupInstance G X) :
    I.H = {a : G | ∀ x : G, I.f (x * a) = I.f x} := by
  ext a
  constructor
  · intro ha x
    have hmem : (x * a)⁻¹ * x ∈ I.H := by
      have hcomp : (x * a)⁻¹ * x = a⁻¹ := by group
      rw [hcomp]
      exact Subgroup.inv_mem I.H ha
    exact (I.hides (x * a) x).2 hmem
  · intro ha
    have h1 : I.f a = I.f 1 := by simpa using ha 1
    exact (I.mem_iff_f_eq_one a).2 h1

/-- Two hidden-subgroup instances with pointwise equal hiding functions have equal hidden
subgroups [IvanyosMagniezSantha2003]. -/
theorem hidden_subgroup_determined_by_hiding_values
    (I I' : HiddenSubgroupInstance G X) (h : ∀ a : G, I'.f a = I.f a) :
    I'.H = I.H := by
  have h1 : ∀ a : G, I'.f a = I'.f 1 ↔ I.f a = I.f 1 := by
    intro a
    rw [h a, h 1]
  ext a
  rw [I'.mem_iff_f_eq_one a, I.mem_iff_f_eq_one a]
  exact h1 a

/-- A hidden subgroup in a commutative group is normal [IvanyosMagniezSantha2003]. -/
theorem hidden_subgroup_normal_of_commutative [IsMulCommutative G]
    (I : HiddenSubgroupInstance G X) : I.H.Normal :=
  Subgroup.normal_of_isMulCommutative I.H

end AbelianHSP

end Qatlib.Papers.NonAbelianHSP01.MainResults
