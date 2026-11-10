/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.PhysicalFlux
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

def physicalBoltzmannHalf (β : ℝ) (H : Matrix I I ℂ) : Matrix I I ℂ :=
  NormedSpace.exp ((-((β : ℂ)/2)) • H)

def physicalPropagation (t ħ : ℝ) (H : Matrix I I ℂ) : Matrix I I ℂ :=
  NormedSpace.exp ((-Complex.I*((t/ħ : ℝ) : ℂ)) • H)

def physicalFluxCorrelation (β t ħ : ℝ) (H P : Matrix I I ℂ) : ℂ :=
  let B := physicalBoltzmannHalf β H
  let U := physicalPropagation t ħ H
  let F := physicalFlux ħ H P
  Matrix.trace (B*F*B*Uᴴ*F*U)

theorem physical_scaled_exp (z : ℂ) (H V : Matrix I I ℂ) (E : I → ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hH : H = V*Matrix.diagonal (fun i => (E i : ℂ))*Vᴴ) :
    NormedSpace.exp (z • H) =
      V*Matrix.diagonal (fun i => Complex.exp (z*(E i : ℂ)))*Vᴴ := by
  let W : unitary (Matrix I I ℂ) := ⟨V,hV⟩
  let f := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) W
  let B := Matrix.diagonal (fun i => z*(E i : ℂ))
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hm := NormedSpace.map_exp f f.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional B
  have he : f B = z • H := by
    rw [hH]
    change V*Matrix.diagonal (fun i => z*(E i : ℂ))*Vᴴ = _
    rw [← Matrix.smul_mul,← Matrix.mul_smul,← Matrix.diagonal_smul]
    rfl
  rw [he] at hm
  refine hm.symm.trans ?_
  change V*NormedSpace.exp B*Vᴴ = _
  rw [Matrix.exp_diagonal]
  apply congrArg (fun M : Matrix I I ℂ => V*M*Vᴴ)
  apply congrArg (Matrix.diagonal : (I → ℂ) → Matrix I I ℂ)
  funext i
  rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]

theorem physical_trace_frame (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (A : Matrix I I ℂ) : Matrix.trace (Vᴴ*A*V) = Matrix.trace A := by
  have hVV : V*Vᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose] using hV
  rw [Matrix.trace_mul_cycle,hVV,Matrix.one_mul]

theorem physical_diagonal_frame (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (d : I → ℂ) : Vᴴ*(V*Matrix.diagonal d*Vᴴ)*V = Matrix.diagonal d := by
  have hVV : Vᴴ*V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] using hV
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc Vᴴ V,hVV,Matrix.one_mul,Matrix.mul_one]

section
omit [DecidableEq I]

theorem physical_frame_adjoint (V A : Matrix I I ℂ) : Vᴴ*Aᴴ*V = (Vᴴ*A*V)ᴴ := by
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

end

theorem physical_diagonal_trace (b u : I → ℂ) (F : Matrix I I ℂ) :
    Matrix.trace (Matrix.diagonal b*F*Matrix.diagonal b*
      (Matrix.diagonal u)ᴴ*F*Matrix.diagonal u) =
      ∑ n, ∑ m, b n*b m*star (u m)*u n*F n m*F m n := by
  rw [Matrix.diagonal_conjTranspose]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro n _
  rw [Matrix.mul_diagonal,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Pi.star_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem physical_thermal_phase (β t ħ en em : ℝ) :
    Complex.exp (-((β : ℂ)/2)*(en : ℂ))*Complex.exp (-((β : ℂ)/2)*(em : ℂ))*
      star (Complex.exp (-Complex.I*((t/ħ : ℝ) : ℂ)*(em : ℂ)))*
      Complex.exp (-Complex.I*((t/ħ : ℝ) : ℂ)*(en : ℂ)) =
    Complex.exp (-(β*(en+em))/2)*Complex.exp (Complex.I*((em-en)*t/ħ)) := by
  have hs : star (Complex.exp (-Complex.I*((t/ħ : ℝ) : ℂ)*(em : ℂ))) =
      Complex.exp (Complex.I*((t/ħ : ℝ) : ℂ)*(em : ℂ)) := by
    rw [Complex.star_def,← Complex.exp_conj]
    congr 1
    simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg]
  rw [hs,← Complex.exp_add,← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

end Qatlib.Papers.ThermalRate98.MainResults
