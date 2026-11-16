/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullUnitaryTransport

@[expose] public section


/-! Complete unitary energy coordinates and the same original Gibbs density.
Both coordinate inverses are proved, and the normalized state is positive definite. -/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SourceForms

variable {D : ℕ}

noncomputable def hermEnergyCoordinates (H : Operator D) (hH : H.IsHermitian)
    (X : Operator D) : Operator D :=
  (hermUnitary H hH)ᴴ * X * hermUnitary H hH

/-- The inverse change of coordinates, on the complete operator space. -/

noncomputable def hermPhysicalCoordinates (H : Operator D) (hH : H.IsHermitian)
    (X : Operator D) : Operator D :=
  hermUnitary H hH * X * (hermUnitary H hH)ᴴ

/-- Herm Physical energy inverse for the stated finite source data. -/
theorem hermPhysical_energy_inverse (H : Operator D) (hH : H.IsHermitian)
    (X : Operator D) :
    hermPhysicalCoordinates H hH (hermEnergyCoordinates H hH X) = X := by
  have hU := hermUnitary_star_mul H hH
  have hUU : hermUnitary H hH * (hermUnitary H hH)ᴴ = 1 :=
    mul_eq_one_comm.mp hU
  unfold hermPhysicalCoordinates hermEnergyCoordinates
  have heq : hermUnitary H hH * ((hermUnitary H hH)ᴴ * X * hermUnitary H hH) *
      (hermUnitary H hH)ᴴ =
      (hermUnitary H hH * (hermUnitary H hH)ᴴ) * X *
        (hermUnitary H hH * (hermUnitary H hH)ᴴ) := by
    repeat' rw [← Matrix.mul_assoc]
  rw [heq, hUU, Matrix.one_mul, Matrix.mul_one]

/-- Herm Energy physical inverse for the stated finite source data. -/
theorem hermEnergy_physical_inverse (H : Operator D) (hH : H.IsHermitian)
    (X : Operator D) :
    hermEnergyCoordinates H hH (hermPhysicalCoordinates H hH X) = X := by
  have hU := hermUnitary_star_mul H hH
  unfold hermPhysicalCoordinates hermEnergyCoordinates
  have heq : (hermUnitary H hH)ᴴ * (hermUnitary H hH * X * (hermUnitary H hH)ᴴ) *
      hermUnitary H hH =
      ((hermUnitary H hH)ᴴ * hermUnitary H hH) * X *
        ((hermUnitary H hH)ᴴ * hermUnitary H hH) := by
    repeat' rw [← Matrix.mul_assoc]
  rw [heq, hU, Matrix.one_mul, Matrix.mul_one]

/-- Herm Energy Coordinates surjective for the stated finite source data. -/
theorem hermEnergyCoordinates_surjective (H : Operator D) (hH : H.IsHermitian) :
    Function.Surjective (hermEnergyCoordinates H hH) := by
  intro X
  exact ⟨hermPhysicalCoordinates H hH X, hermEnergy_physical_inverse H hH X⟩

/-- All `D²` entries of a proposal, with no spectral truncation. -/

theorem hermEnergyCoordinates_mul (H : Operator D) (hH : H.IsHermitian)
    (A B : Operator D) :
    hermEnergyCoordinates H hH (A * B) =
      hermEnergyCoordinates H hH A * hermEnergyCoordinates H hH B := by
  have hU := hermUnitary_star_mul H hH
  have hUU : hermUnitary H hH * (hermUnitary H hH)ᴴ = 1 :=
    mul_eq_one_comm.mp hU
  symm
  have h := conj_mul_conj (hermUnitary H hH)ᴴ A B
  simpa only [Matrix.conjTranspose_conjTranspose, hUU, Matrix.mul_one,
    hermEnergyCoordinates] using h

/-- Every normalized finite diagonal Gibbs matrix is positive definite, including the empty space. -/
theorem gibbsDiag_posDef (lam : Fin D → ℝ) (β : ℝ) :
    (gibbsDiag lam β).PosDef := by
  unfold gibbsDiag
  apply Matrix.PosDef.diagonal
  intro i
  apply Complex.zero_lt_real.mpr
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩

/-- Herm Gibbs pos Def for the stated finite source data. -/
theorem hermGibbs_posDef (H : Operator D) (hH : H.IsHermitian) (β : ℝ) :
    (hermGibbs H hH β).PosDef := by
  let U := hermUnitary H hH
  have hU : Uᴴ * U = 1 := hermUnitary_star_mul H hH
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hinj : Function.Injective (Matrix.mulVec Uᴴ) := by
    intro x y h
    have h' := congrArg (fun v => U *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] using h'
  have h := (gibbsDiag_posDef hH.eigenvalues β).conjTranspose_mul_mul_same
    (B := Uᴴ) hinj
  simpa only [Matrix.conjTranspose_conjTranspose, hermGibbs, U] using h

/-- Trace gibbs Diag one for the stated finite source data. -/
theorem trace_gibbsDiag_one [NeZero D] (lam : Fin D → ℝ) (β : ℝ) :
    Matrix.trace (gibbsDiag lam β) = 1 := by
  have hZ : 0 < ∑ i : Fin D, Real.exp (-(β * lam i)) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [gibbsDiag, Matrix.trace_diagonal, ← Complex.ofReal_sum,
    ← Finset.sum_div, div_self (ne_of_gt hZ), Complex.ofReal_one]

/-- Herm Gibbs is Density Operator for the stated finite source data. -/
theorem hermGibbs_isDensityOperator [NeZero D]
    (H : Operator D) (hH : H.IsHermitian) (β : ℝ) :
    IsDensityOperator (hermGibbs H hH β) := by
  refine ⟨(hermGibbs_posDef H hH β).posSemidef, ?_⟩
  rw [hermGibbs, Matrix.trace_mul_cycle, hermUnitary_star_mul,
    Matrix.one_mul, trace_gibbsDiag_one]

end Qatlib.Concepts.GibbsSource.SourceForms
