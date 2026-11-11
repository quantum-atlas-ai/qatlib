/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.BinaryPVM

/-!
# Binary projectors of Hermitian involutions

This module defines the binary matrices `involutionProjector A b = (1 + binarySign b • A) / 2`.
The two branches sum to the identity and their difference recovers `A`.

For Hermitian involutions, the branches are positive semidefinite idempotents. Commutation of
observables passes to their branches, providing the projectors used for joint context
measurements in [XuEtAl2026].

## Main statements

* `involutionProjector`: The Hermitian matrix `(1 + binarySign b • A) / 2`, giving a spectral
  projector when `A` is an involution.
* `involutionProjector_idempotent`: For a Hermitian involution, each binary branch is
  idempotent.
* `involutionProjector_commute`: Binary branches of commuting Hermitian matrices commute.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators ComplexOrder
open Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Hermitian matrix `(1 + binarySign b • A) / 2`, giving a spectral projector when `A` is
an involution. -/
def involutionProjector (A : HermitianMat d ℂ) (b : Bool) : HermitianMat d ℂ :=
  (1/2:ℝ) • (1+binarySign b • A)

omit [Fintype d] in

/-- The two binary branches of `A` sum to the identity. -/
theorem involutionProjector_sum (A : HermitianMat d ℂ) :
    involutionProjector A false+involutionProjector A true=1 := by
  norm_num [involutionProjector,binarySign]
  module

omit [Fintype d] in

/-- The difference of the false and true branches equals `A`. -/
theorem involutionProjector_difference (A : HermitianMat d ℂ) :
    involutionProjector A false-involutionProjector A true=A := by
  norm_num [involutionProjector,binarySign]
  module

/-- For a Hermitian involution, each binary branch is idempotent. -/
theorem involutionProjector_idempotent (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (b : Bool) :
    (involutionProjector A b).mat*(involutionProjector A b).mat=(involutionProjector A b).mat := by
  let B : Matrix d d ℂ := binarySign b • A.mat
  have hB : B*B=1 := by
    dsimp [B]
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,← pow_two,binarySign_sq,hA,one_smul]
  have hD : (1+B)*(1+B)=(2:ℝ) • (1+B) := by
    simp only [add_mul,mul_add,one_mul,mul_one,hB]
    module
  change ((1/2:ℝ) • (1+B))*((1/2:ℝ) • (1+B))=(1/2:ℝ) • (1+B)
  rw [smul_mul_assoc,mul_smul_comm,smul_smul,hD,smul_smul]
  norm_num

/-- For a Hermitian involution, each binary branch is positive semidefinite. -/
theorem involutionProjector_nonneg (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (b : Bool) :
    0 ≤ involutionProjector A b := by
  apply HermitianMat.zero_le_iff.mpr
  have hg := Matrix.posSemidef_conjTranspose_mul_self (involutionProjector A b).mat
  rw [(involutionProjector A b).H,involutionProjector_idempotent A hA b] at hg
  exact hg

/-- Binary branches of commuting Hermitian matrices commute. -/
theorem involutionProjector_commute (A B : HermitianMat d ℂ) (h : Commute A.mat B.mat) (a b : Bool) :
    Commute (involutionProjector A a).mat (involutionProjector B b).mat := by
  change ((1/2:ℝ) • (1+binarySign a • A.mat))*((1/2:ℝ) • (1+binarySign b • B.mat))=
    ((1/2:ℝ) • (1+binarySign b • B.mat))*((1/2:ℝ) • (1+binarySign a • A.mat))
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,add_mul,mul_add,one_mul,mul_one]
  rw [h.eq]
  module

end Qatlib.Foundations.FiniteStats.BornEstimator
