/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.ActualDiagonalization

/-!
# Dissipative shifts of arbitrary generators

For a finite complex generator `A`, `generatorShiftSize` takes the Euclidean operator norm of
its Hermitian part, and `generatorShift` subtracts that scalar multiple of the identity. The
resulting Hermitian part is nonpositive, making the shifted generator eligible for the
diagonalized LCHS formula.

The identity `generator_shift_exponential` restores the original evolution by a scalar
exponential factor. Combined with the spectral representation,
`arbitrary_generator_diagonalized` realizes the shift-and-restoration construction discussed in
[ZhangEtAl2026].

## Main statements

- `generatorL_le_shift` bounds the Hermitian part by the chosen scalar shift.
- `generatorShift_negative_psd` proves dissipativity of the shifted generator.
* `generator_shift_exponential` factors the original exponential into scalar restoration and
  shifted evolution.
* `actual_generator_diagonalized` and `arbitrary_generator_diagonalized` provide diagonalized
  Cauchy formulas for dissipative and arbitrary generators.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Papers.KoopmanSim26.SpectralRep

namespace Qatlib.Papers.KoopmanSim26.SpectralRep
variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable local instance matrixCStar : CStarAlgebra (Matrix I I ℂ) where
noncomputable local instance matrixRatAlgebra : NormedAlgebra ℚ (Matrix I I ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
noncomputable local instance matrixRealAlgebra : NormedAlgebra ℝ (Matrix I I ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

/-- The quantity `generatorShiftSize A` is the Euclidean operator norm of the Hermitian part
`generatorL A`, used as a scalar dissipative shift. -/
def generatorShiftSize (A : Matrix I I ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)) (generatorL A)‖

/-- The matrix `generatorShift A` is obtained by subtracting `generatorShiftSize A` times the
identity from `A`. -/
def generatorShift (A : Matrix I I ℂ) : Matrix I I ℂ := A-generatorShiftSize A • 1

/-- For matrices indexed by `Fin d`, `generatorL` agrees with the public Koopman-flow definition
`hermitianPart`. -/
theorem generatorL_eq_public {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    generatorL A=Qatlib.Concepts.KoopmanFlow.FlowAction.hermitianPart A := rfl

/-- For matrices indexed by `Fin d`, `generatorShiftSize` agrees with the public Koopman-flow
definition `shiftSize`. -/
theorem generatorShiftSize_eq_public {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    generatorShiftSize A=Qatlib.Concepts.KoopmanFlow.FlowAction.shiftSize A := rfl

/-- For matrices indexed by `Fin d`, `generatorShift` agrees with the public Koopman-flow
definition `shifted`. -/
theorem generatorShift_eq_public {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    generatorShift A=Qatlib.Concepts.KoopmanFlow.FlowAction.shifted A := rfl

omit [Fintype I] in

/-- Subtracting a real scalar multiple of the identity from a matrix subtracts the same multiple
from its Hermitian part. -/
theorem generatorL_real_shift (A : Matrix I I ℂ) (a : ℝ) :
    generatorL (A-a • 1)=generatorL A-a • 1 := by
  simp only [generatorL, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_one]
  module

/-- The Hermitian part of `A` is bounded above in matrix order by `generatorShiftSize A` times
the identity. -/
theorem generatorL_le_shift (A : Matrix I I ℂ) :
    generatorL A ≤ generatorShiftSize A • (1 : Matrix I I ℂ) := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (generatorL A) (generatorL_hermitian A)
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.cstar_norm_def, generatorShiftSize] using h

/-- The negative Hermitian part of `generatorShift A` is positive semidefinite. -/
theorem generatorShift_negative_psd (A : Matrix I I ℂ) :
    (-(generatorL (generatorShift A))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply neg_nonneg.mpr
  rw [generatorShift, generatorL_real_shift]
  exact sub_nonpos.mpr (generatorL_le_shift A)

set_option backward.isDefEq.respectTransparency false in

/-- For every real time, `exp(t A)` equals `exp(t generatorShiftSize A)` times the exponential
of the shifted generator. -/
theorem generator_shift_exponential (A : Matrix I I ℂ) (t : ℝ) :
    NormedSpace.exp (t • A)=Real.exp (t*generatorShiftSize A) •
      NormedSpace.exp (t • generatorShift A) := by
  have he : t • A=algebraMap ℝ (Matrix I I ℂ) (t*generatorShiftSize A)+t • generatorShift A := by
    rw [Algebra.algebraMap_eq_smul_one, generatorShift, smul_sub, smul_smul]
    module
  have hc : Commute (algebraMap ℝ (Matrix I I ℂ) (t*generatorShiftSize A))
      (t • generatorShift A) := Algebra.commute_algebraMap_left _ _
  rw [he, NormedSpace.exp_add_of_commute hc,
    ← NormedSpace.algebraMap_exp_comm (𝕂:=ℝ), ← Real.exp_eq_exp_ℝ,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

set_option backward.isDefEq.respectTransparency false in

/-- For a dissipative generator and nonnegative time, the Cauchy-weighted diagonalized frequency
matrices are integrable as matrices and entrywise, and their integral equals `exp(t A)`. -/
theorem actual_generator_diagonalized (A : Matrix I I ℂ) (t : ℝ)
    (hA : (-(generatorL A)).PosSemidef) (ht : 0 ≤ t) :
    Integrable (fun k : ℝ => (1/(Real.pi*(1+k^2))) • diagonalizedUnitary
      (generatorL A) (generatorH A) (generatorL_hermitian A) (generatorH_hermitian A) t k) ∧
    (∀ i j : I, Integrable (fun k : ℝ => ((1/(Real.pi*(1+k^2)) : ℝ) : ℂ) *
      diagonalizedUnitary (generatorL A) (generatorH A)
        (generatorL_hermitian A) (generatorH_hermitian A) t k i j)) ∧
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • diagonalizedUnitary
      (generatorL A) (generatorH A) (generatorL_hermitian A) (generatorH_hermitian A) t k) =
      NormedSpace.exp (t • A) := by
  simpa only [propagator, generator_reconstruction] using
    actual_diagonalized_lchs (generatorL A) (generatorH A) t hA (generatorH_hermitian A) ht

/-- For an arbitrary finite complex generator at nonnegative time, `exp(t A)` is the
diagonalized Cauchy integral for its dissipative shift multiplied by the scalar restoration
factor `exp(t generatorShiftSize A)`. This implements the scalar shift and restoration
construction in [ZhangEtAl2026]. -/
theorem arbitrary_generator_diagonalized (A : Matrix I I ℂ) (t : ℝ) (ht : 0 ≤ t) :
    NormedSpace.exp (t • A) = Real.exp (t*generatorShiftSize A) •
      (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • diagonalizedUnitary
        (generatorL (generatorShift A)) (generatorH (generatorShift A))
        (generatorL_hermitian (generatorShift A)) (generatorH_hermitian (generatorShift A)) t k) := by
  rw [generator_shift_exponential]
  congr 1
  exact (actual_generator_diagonalized (generatorShift A) t (generatorShift_negative_psd A) ht).2.2.symm

end Qatlib.Papers.KoopmanSim26.SpectralRep
