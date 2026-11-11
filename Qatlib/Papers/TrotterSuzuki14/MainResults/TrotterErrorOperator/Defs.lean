/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.NestedComm

/-!
# Nested commutators for second-order Trotter error

This module defines the weighted nested-commutator expression `leadingSecondOrderError` on a
specified finite set of operator triples. It proves elementary weight and factor-norm estimates
used to distinguish the `Z⁶` and `Z³` contributions. See [BabbushEtAl2015].

## Main statements

* `leadingSecondOrderError`: Weighted nested-commutator error expression.
* `tripleProduct_norm_le_of_oneBody`: A `4 c³ Z⁶` nested-commutator bound.
* `tripleProduct_norm_le_of_twoBody`: A `4 c³ Z³` nested-commutator bound.

## References

* [Babbush et al., 2015][BabbushEtAl2015]
-/

set_option autoImplicit false
namespace Qatlib.Papers.TrotterSuzuki14.MainResults
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra
variable {ι A : Type*}

/-- An ordered triple of indices from `ι`. -/
abbrev Triple (ι : Type*) := ι × ι × ι

/-- The commutator `X * Y - Y * X`. -/
def commutator [Mul A] [Sub A] (X Y : A) : A := X * Y - Y * X

/-- The Suzuki weight, equal to one half when the two indices coincide and one otherwise. -/
noncomputable def suzukiWeight [DecidableEq ι] (α β : ι) : ℝ := if α = β then 1 / 2 else 1

/-- The nested commutator of the first operator with the commutator of the second and third
operators. -/
def tripleProduct [Mul A] [Sub A] (op : ι → A) (t : Triple ι) : A :=
  commutator (op t.1) (commutator (op t.2.1) (op t.2.2))

/-- The finite Suzuki-weighted sum of nested commutators, multiplied by `-(dt² / 12)`. -/
noncomputable def leadingSecondOrderError [AddCommMonoid A] [Mul A] [Sub A] [SMul ℝ A]
    [Neg A] [DecidableEq ι] (op : ι → A) (triples : Finset (Triple ι)) (dt : ℝ) : A :=
  (-(dt ^ 2 / 12)) • ∑ t ∈ triples, suzukiWeight t.1 t.2.1 • tripleProduct op t

/-- Every Suzuki weight has absolute value at most one. -/
theorem abs_suzukiWeight_le_one [DecidableEq ι] (α β : ι) : |suzukiWeight α β| ≤ 1 := by
  unfold suzukiWeight
  split_ifs <;> norm_num

section
variable [NormedRing A]

/-- If each factor has norm at most `c Z²` and `c ≥ 0`, the nested commutator has norm at most
`4 c³ Z⁶`. -/
theorem tripleProduct_norm_le_of_oneBody (op : ι → A) (t : Triple ι) {c Z : ℝ}
    (hα : ‖op t.1‖ ≤ c * Z ^ 2) (hβ : ‖op t.2.1‖ ≤ c * Z ^ 2)
    (hγ : ‖op t.2.2‖ ≤ c * Z ^ 2) (hc : 0 ≤ c) :
    ‖tripleProduct op t‖ ≤ 4 * c ^ 3 * Z ^ 6 := by
  calc ‖tripleProduct op t‖ ≤ 4 * ‖op t.1‖ * ‖op t.2.1‖ * ‖op t.2.2‖ :=
         NestedComm.nested_norm_le _ _ _
       _ ≤ 4 * (c * Z ^ 2) * (c * Z ^ 2) * (c * Z ^ 2) := by gcongr
       _ = 4 * c ^ 3 * Z ^ 6 := by ring

/-- If each factor has norm at most `c Z` and both `c` and `Z` are nonnegative, the nested
commutator has norm at most `4 c³ Z³`. -/
theorem tripleProduct_norm_le_of_twoBody (op : ι → A) (t : Triple ι) {c Z : ℝ}
    (hα : ‖op t.1‖ ≤ c * Z) (hβ : ‖op t.2.1‖ ≤ c * Z)
    (hγ : ‖op t.2.2‖ ≤ c * Z) (hc : 0 ≤ c) (hZ : 0 ≤ Z) :
    ‖tripleProduct op t‖ ≤ 4 * c ^ 3 * Z ^ 3 := by
  calc ‖tripleProduct op t‖ ≤ 4 * ‖op t.1‖ * ‖op t.2.1‖ * ‖op t.2.2‖ :=
         NestedComm.nested_norm_le _ _ _
       _ ≤ 4 * (c * Z) * (c * Z) * (c * Z) := by gcongr
       _ = 4 * c ^ 3 * Z ^ 3 := by ring
end
end Qatlib.Papers.TrotterSuzuki14.MainResults
