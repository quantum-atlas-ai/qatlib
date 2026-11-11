/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.ThermalTrace

/-!
# Spectral formulas for physical flux correlations

This module connects the matrix trace definition of `physicalFluxCorrelation` to finite spectral
formulas for the thermal rate analysis of [LidarWang1999]. A unitary spectral representation
yields `sourceFluxCorrelation`, and a real position-diagonal surface gives the explicit thermal
double sum with the inverse-square `ħ` prefactor.

Diagonal terms vanish, and `physical_flux_representation_exists` combines the finite Hermitian
spectral theorem with the off-diagonal correlation formula.

## Main statements

* `physical_hamiltonian_spectral_exists`: provides a unitary frame and real energies for a
  Hermitian Hamiltonian.
* `physical_flux_correlation_eq16`: expands the physical correlation as a weighted double sum.
* `physical_flux_representation_exists`: provides a spectral frame satisfying the off-diagonal
  formula.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Every finite Hermitian complex matrix possesses a unitary spectral representation with real
energies. See [LidarWang1999]. -/
theorem physical_hamiltonian_spectral_exists (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    ∃ (V : Matrix I I ℂ) (E : I → ℝ), V ∈ Matrix.unitaryGroup I ℂ ∧
      H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ := by
  refine ⟨hH.eigenvectorUnitary,hH.eigenvalues,hH.eigenvectorUnitary.property,?_⟩
  simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Function.comp_apply]
    using! hH.spectral_theorem

/-- For a unitary spectral representation of `H` and a position-diagonal surface, the physical
flux correlation equals the source spectral correlation of the corresponding flux entries.
See [LidarWang1999]. -/
theorem physical_flux_correlation_spectral (β t ħ : ℝ) (H V : Matrix I I ℂ)
    (E : I → ℝ) (h : I → ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) :
    physicalFluxCorrelation β t ħ H (Matrix.diagonal h) =
      sourceFluxCorrelation β t ħ E (sourceFluxMatrixElement ħ E h V) := by
  let B := physicalBoltzmannHalf β H
  let U := physicalPropagation t ħ H
  let F := physicalFlux ħ H (Matrix.diagonal h)
  let b := fun n => Complex.exp (-((β : ℂ)/2)*(E n : ℂ))
  let u := fun n => Complex.exp (-Complex.I*((t/ħ : ℝ) : ℂ)*(E n : ℂ))
  have hB : Vᴴ*B*V = Matrix.diagonal b := by
    dsimp [B,physicalBoltzmannHalf]
    rw [physical_scaled_exp _ H V E hV hH,physical_diagonal_frame V hV]
  have hU : Vᴴ*U*V = Matrix.diagonal u := by
    dsimp [U,physicalPropagation]
    rw [physical_scaled_exp _ H V E hV hH,physical_diagonal_frame V hV]
  have hUstar : Vᴴ*Uᴴ*V = (Matrix.diagonal u)ᴴ := by
    rw [physical_frame_adjoint,hU]
  have hF : Vᴴ*F*V = (fun n m => sourceFluxMatrixElement ħ E h V n m) := by
    ext n m
    exact physical_flux_entry ħ H V E h hV hH n m
  change Matrix.trace (B*F*B*Uᴴ*F*U) = _
  rw [← physical_trace_frame V hV (B*F*B*Uᴴ*F*U)]
  simp_rw [physical_frame_mul V hV]
  rw [hB,hUstar,hF,hU,physical_diagonal_trace]
  unfold sourceFluxCorrelation
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  dsimp [b,u]
  exact congrArg (fun z : ℂ => z*sourceFluxMatrixElement ħ E h V n m*
    sourceFluxMatrixElement ħ E h V m n) (physical_thermal_phase β t ħ (E n) (E m))

/-- For a real position-diagonal surface and a unitary spectral representation, the physical
flux correlation is the thermal double sum of squared energy gaps and squared surface
overlaps, with prefactor `ħ⁻²` (see [LidarWang1999]). -/
theorem physical_flux_correlation_eq16 (β t ħ : ℝ) (H V : Matrix I I ℂ)
    (E : I → ℝ) (h : I → ℂ) (hh : ∀ j, (h j).im = 0)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) :
    physicalFluxCorrelation β t ħ H (Matrix.diagonal h) =
      ((ħ⁻¹)^2 : ℂ)*∑ n, ∑ m, Complex.exp (-(β*(E n+E m))/2)*
        Complex.exp (Complex.I*((E m-E n)*t/ħ))*(((E n-E m : ℝ) : ℂ)^2)*
        (Complex.normSq (∑ j, star (V j n)*V j m*h j) : ℂ) := by
  rw [physical_flux_correlation_spectral β t ħ H V E h hV hH]
  exact source_flux_correlation_eq16 β t ħ E V h hh

/-- For a real position-diagonal surface and a unitary spectral representation, the physical
flux correlation has the explicit thermal sum over distinct indices, with prefactor `ħ⁻²`. -/
theorem physical_flux_correlation_offdiagonal (β t ħ : ℝ) (H V : Matrix I I ℂ)
    (E : I → ℝ) (h : I → ℂ) (hh : ∀ j, (h j).im = 0)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) :
    physicalFluxCorrelation β t ħ H (Matrix.diagonal h) =
      ((ħ⁻¹)^2 : ℂ)*∑ n, ∑ m ∈ Finset.univ.erase n, Complex.exp (-(β*(E n+E m))/2)*
        Complex.exp (Complex.I*((E m-E n)*t/ħ))*(((E n-E m : ℝ) : ℂ)^2)*
        (Complex.normSq (∑ j, star (V j n)*V j m*h j) : ℂ) := by
  rw [physical_flux_correlation_eq16 β t ħ H V E h hh hV hH]
  congr 1
  exact (source_flux_offdiagonal β t ħ E (fun n m => ∑ j, star (V j n)*V j m*h j)).symm

/-- For a Hermitian Hamiltonian and a real position-diagonal surface, there exist real energies
and a unitary spectral frame realizing the off-diagonal thermal double sum for the physical
flux correlation. See [LidarWang1999]. -/
theorem physical_flux_representation_exists (β t ħ : ℝ) (H : Matrix I I ℂ)
    (hH : H.IsHermitian) (h : I → ℂ) (hh : ∀ j, (h j).im = 0) :
    ∃ (V : Matrix I I ℂ) (E : I → ℝ), V ∈ Matrix.unitaryGroup I ℂ ∧
      H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ ∧
      physicalFluxCorrelation β t ħ H (Matrix.diagonal h) =
        ((ħ⁻¹)^2 : ℂ)*∑ n, ∑ m ∈ Finset.univ.erase n, Complex.exp (-(β*(E n+E m))/2)*
          Complex.exp (Complex.I*((E m-E n)*t/ħ))*(((E n-E m : ℝ) : ℂ)^2)*
          (Complex.normSq (∑ j, star (V j n)*V j m*h j) : ℂ) := by
  obtain ⟨V,E,hV,hdiag⟩ := physical_hamiltonian_spectral_exists H hH
  exact ⟨V,E,hV,hdiag,physical_flux_correlation_offdiagonal β t ħ H V E h hh hV hdiag⟩

end Qatlib.Papers.ThermalRate98.MainResults
