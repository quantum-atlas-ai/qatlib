/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasisSubgoalQuan

/-!
# The character-table Fourier transform

`characterQFT` is the matrix whose columns are normalized character vectors of a finite Abelian
group, indexed through a chosen equivalence with its character group. The module proves
unitarity, existence of such a labeling, and the normalized character formula for matrix
entries. The development follows [Kitaev1995].

## Main statements

* `characterQFT_unitary`: proves the character Fourier matrix is unitary.
* `characterLabelsExist`: provides a labeling by group elements.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open scoped BigOperators
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm

/-- The Fourier matrix whose column indexed by `j` is the normalized character vector associated
to `labels j`. -/
def characterQFT (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) : Matrix E E ℂ := fun x j => orbitFourierVec E (labels j) x

/-- For any equivalence labeling the characters of a finite Abelian group, `characterQFT` is
unitary, as used in [Kitaev1995]. -/
theorem characterQFT_unitary (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) : characterQFT E labels ∈ Matrix.unitaryGroup E ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h := (orbitFourierBasisSubgoal E).1 (labels i) (labels j)
  simpa [characterQFT, inner_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply, labels.injective.eq_iff] using h

/-- A finite Abelian group possesses an equivalence with its complex-valued additive character
group, as used in [Kitaev1995]. -/
theorem characterLabelsExist (E : Type) [AddCommGroup E] [Fintype E] :
    Nonempty (E ≃ AddChar E ℂ) := Fintype.card_eq.mp AddChar.card_eq.symm

/-- Each character Fourier entry is the character value multiplied by the inverse square root of
the group cardinality, as used in [Kitaev1995]. -/
theorem characterQFT_entry (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) (x j : E) :
    characterQFT E labels x j = (Real.sqrt (Fintype.card E : ℝ))⁻¹ * labels j x := rfl

end Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm
