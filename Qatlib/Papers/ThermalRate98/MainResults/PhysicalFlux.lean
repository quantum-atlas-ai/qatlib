/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.FluxCorrelation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

def physicalFlux (ħ : ℝ) (H P : Matrix I I ℂ) : Matrix I I ℂ :=
  (Complex.I/(ħ : ℂ)) • (H*P-P*H)

theorem physical_frame_mul (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (A B : Matrix I I ℂ) :
    Vᴴ*(A*B)*V = (Vᴴ*A*V)*(Vᴴ*B*V) := by
  have hVV : V*Vᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose] using hV
  symm
  calc
    _ = Vᴴ*A*(V*Vᴴ)*B*V := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hVV]; simp only [Matrix.mul_one,Matrix.mul_assoc]

theorem physical_hamiltonian_frame (H V : Matrix I I ℂ) (E : I → ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun n => (E n : ℂ))*Vᴴ) :
    Vᴴ*H*V = Matrix.diagonal (fun n => (E n : ℂ)) := by
  have hVV : Vᴴ*V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] using hV
  rw [hH]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc Vᴴ V,hVV,Matrix.one_mul,Matrix.mul_one]

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

theorem physical_surface_entry (V : Matrix I I ℂ) (h : I → ℂ) (n m : I) :
    (Vᴴ*Matrix.diagonal h*V) n m = ∑ j, star (V j n)*V j m*h j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

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
