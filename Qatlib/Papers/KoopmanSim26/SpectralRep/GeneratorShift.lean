/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.ActualDiagonalization
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

def generatorShiftSize (A : Matrix I I ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)) (generatorL A)‖

def generatorShift (A : Matrix I I ℂ) : Matrix I I ℂ := A-generatorShiftSize A • 1

theorem generatorL_eq_public {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    generatorL A=Qatlib.Concepts.KoopmanFlow.FlowAction.hermitianPart A := rfl

theorem generatorShiftSize_eq_public {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    generatorShiftSize A=Qatlib.Concepts.KoopmanFlow.FlowAction.shiftSize A := rfl

theorem generatorShift_eq_public {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    generatorShift A=Qatlib.Concepts.KoopmanFlow.FlowAction.shifted A := rfl

omit [Fintype I] in

theorem generatorL_real_shift (A : Matrix I I ℂ) (a : ℝ) :
    generatorL (A-a • 1)=generatorL A-a • 1 := by
  simp only [generatorL, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_one]
  module

theorem generatorL_le_shift (A : Matrix I I ℂ) :
    generatorL A ≤ generatorShiftSize A • (1 : Matrix I I ℂ) := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (generatorL A) (generatorL_hermitian A)
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.cstar_norm_def, generatorShiftSize] using h

theorem generatorShift_negative_psd (A : Matrix I I ℂ) :
    (-(generatorL (generatorShift A))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply neg_nonneg.mpr
  rw [generatorShift, generatorL_real_shift]
  exact sub_nonpos.mpr (generatorL_le_shift A)

set_option backward.isDefEq.respectTransparency false in

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

theorem arbitrary_generator_diagonalized (A : Matrix I I ℂ) (t : ℝ) (ht : 0 ≤ t) :
    NormedSpace.exp (t • A) = Real.exp (t*generatorShiftSize A) •
      (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • diagonalizedUnitary
        (generatorL (generatorShift A)) (generatorH (generatorShift A))
        (generatorL_hermitian (generatorShift A)) (generatorH_hermitian (generatorShift A)) t k) := by
  rw [generator_shift_exponential]
  congr 1
  exact (actual_generator_diagonalized (generatorShift A) t (generatorShift_negative_psd A) ht).2.2.symm

end Qatlib.Papers.KoopmanSim26.SpectralRep
