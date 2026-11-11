/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Coset density and group twirling

This module defines the finite-group matrices `sourceCosetDensity` and `sourceFixedProjector`,
together with `sourceRightTwirl`. The first uses subgroup membership of `q * p⁻¹`, the second
averages left translations over a subgroup, and the third averages right-translation
conjugations over the group.

These constructions provide the coset-state and symmetry-averaging objects used in hidden
subgroup analysis; see [Lomont2004].

## Main statements

* `sourceCosetDensity`: specifies the subgroup coset density entries.
* `sourceFixedProjector`: averages subgroup translation matrices.
* `sourceRightTwirl`: averages conjugation by right translations.

## References

* [Lomont, 2004][Lomont2004]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib

/-- The matrix with entry `1 / Fintype.card G` when `q * p⁻¹ ∈ H` and zero otherwise. -/
noncomputable def sourceCosetDensity (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) : Matrix G G ℂ := by
  classical
  exact fun p q => if q * p⁻¹ ∈ H then (Fintype.card G : ℂ)⁻¹ else 0

/-- The average over `H` of the permutation matrices for left multiplication by subgroup
elements. -/
noncomputable def sourceFixedProjector (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) : Matrix G G ℂ := by
  classical
  exact (Fintype.card H : ℂ)⁻¹ • ∑ h : H, permMatrix (fun g : G => h.val * g)

/-- The uniform average of conjugates of `rho` by the permutation matrices for right
multiplication in `G`. -/
noncomputable def sourceRightTwirl (G : Type*) [Group G] [Fintype G]
    (rho : Matrix G G ℂ) : Matrix G G ℂ := by
  classical
  exact (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
    let R := permMatrix (fun a : G => a * g)
    R * rho * R.conjTranspose

end Qatlib.Concepts.HspRecovery.ReductionCore
