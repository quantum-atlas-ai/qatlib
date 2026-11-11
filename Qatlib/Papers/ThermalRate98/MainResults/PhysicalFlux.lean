/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.FluxCorrelation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Flux operators in an energy frame

This module defines the flux matrix `physicalFlux` as `i / ħ` times the commutator of a
Hamiltonian and a surface matrix. It proves its transformation under a unitary energy frame and
identifies entries for a surface matrix diagonal in position coordinates, following the flux
formulas of [LidarWang1999].

## Main statements

* `physical_flux_frame`: expresses the flux as a commutator with the diagonal energy matrix.
* `physical_flux_entry`: identifies energy frame flux entries with `sourceFluxMatrixElement`.
* `physical_flux_hermitian`: proves Hermiticity when the Hamiltonian and surface matrix are
  Hermitian.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The flux matrix `(i / ħ) • (H * P - P * H)` associated with the Hamiltonian `H` and surface
matrix `P`. -/
def physicalFlux (ħ : ℝ) (H P : Matrix I I ℂ) : Matrix I I ℂ :=
  (Complex.I/(ħ : ℂ)) • (H*P-P*H)

/-- Conjugation by a unitary frame preserves matrix multiplication. -/
theorem physical_frame_mul (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (A B : Matrix I I ℂ) :
    Vᴴ*(A*B)*V = (Vᴴ*A*V)*(Vᴴ*B*V) := by
  have hVV : V*Vᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose] using hV
  symm
  calc
    _ = Vᴴ*A*(V*Vᴴ)*B*V := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hVV]; simp only [Matrix.mul_one,Matrix.mul_assoc]

/-- A unitary spectral representation of `H` gives the specified diagonal energy matrix after
conjugation into that frame. -/
theorem physical_hamiltonian_frame (H V : Matrix I I ℂ) (E : I → ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) :
    Vᴴ*H*V = Matrix.diagonal (fun n => (E n : ℂ)) := by
  have hVV : Vᴴ*V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] using hV
  rw [hH]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc Vᴴ V,hVV,Matrix.one_mul,Matrix.mul_one]

/-- In a unitary frame diagonalizing `H`, the flux is `i / ħ` times the commutator of the
diagonal energy matrix with the transformed surface matrix. -/
theorem physical_flux_frame (ħ : ℝ) (H V P : Matrix I I ℂ) (E : I → ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) :
    Vᴴ*physicalFlux ħ H P*V = (Complex.I/(ħ : ℂ)) •
      (Matrix.diagonal (fun n => (E n : ℂ))*(Vᴴ*P*V) -
        (Vᴴ*P*V)*Matrix.diagonal (fun n => (E n : ℂ))) := by
  unfold physicalFlux
  rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sub,Matrix.sub_mul,
    physical_frame_mul V hV H P,physical_frame_mul V hV P H,
    physical_hamiltonian_frame H V E hV hH]

/-- The entries of a position-diagonal surface matrix in frame `V` are sums of conjugated and
unconjugated frame entries weighted by the surface values. -/
theorem physical_surface_entry (V : Matrix I I ℂ) (h : I → ℂ) (n m : I) :
    (Vᴴ*Matrix.diagonal h*V) n m = ∑ j, star (V j n)*V j m*h j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For a unitary spectral frame and a position-diagonal surface matrix, each transformed
physical flux entry equals `sourceFluxMatrixElement`. See [LidarWang1999]. -/
theorem physical_flux_entry (ħ : ℝ) (H V : Matrix I I ℂ) (E : I → ℝ) (h : I → ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) (n m : I) :
    (Vᴴ*physicalFlux ħ H (Matrix.diagonal h)*V) n m =
      sourceFluxMatrixElement ħ E h V n m := by
  rw [physical_flux_frame ħ H V (Matrix.diagonal h) E hV hH]
  simp only [Matrix.smul_apply,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    physical_surface_entry,sourceFluxMatrixElement]
  push_cast
  ring

section
omit [DecidableEq I]

/-- The physical flux matrix is Hermitian whenever the Hamiltonian and surface matrix are
Hermitian. See [LidarWang1999]. -/
theorem physical_flux_hermitian (ħ : ℝ) (H P : Matrix I I ℂ)
    (hH : H.IsHermitian) (hP : P.IsHermitian) : (physicalFlux ħ H P).IsHermitian := by
  change Hᴴ = H at hH
  change Pᴴ = P at hP
  change (physicalFlux ħ H P)ᴴ = physicalFlux ħ H P
  unfold physicalFlux
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,
    hH,hP,Complex.star_def,map_div₀,Complex.conj_I,Complex.conj_ofReal]
  ext i j
  simp only [Matrix.smul_apply,Matrix.sub_apply]
  ring

end

end Qatlib.Papers.ThermalRate98.MainResults
