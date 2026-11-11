/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.PolygonResolventPrincipal
import Mathlib.Topology.Algebra.Module.Star
import Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayerKernel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! The actual velocity kernel has total mass I when the underlying contour
has the certified 2*pi*i principal term. Adjoint integration and every scalar
factor are explicit; mere panel closure is not a normalization premise. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `adjoint_intervalIntegral` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem adjoint_intervalIntegral (f : ℝ → Matrix I I ℂ) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b,star (f t))=star (∫ t in a..b,f t) := by
  exact (starL' ℝ : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ).toContinuousLinearMap.intervalIntegral_comp_comm hf

/-- The identity or estimate `adjoint_integrable` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem adjoint_integrable (f : ℝ → Matrix I I ℂ) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b) : IntervalIntegrable (fun t => star (f t)) volume a b := by
  let L := (starL' ℝ : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ).toContinuousLinearMap
  exact ⟨L.integrable_comp hf.1,L.integrable_comp hf.2⟩

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- Construction for velocity Term in the double layer mass model. -/
def velocityTerm (R : Matrix I I ℂ) (u : ℂ) : Matrix I I ℂ := (-Complex.I*u) • R
/-- Construction for matrix Panel Density in the double layer mass model. -/
def matrixPanelDensity (R : Matrix I I ℂ) (u : ℂ) : Matrix I I ℂ :=
  (((4*Real.pi)⁻¹ : ℝ) : ℂ) • (velocityTerm R u+star (velocityTerm R u))

/-- The identity or estimate `velocity_mass` holds with the displayed separation, geometry and norm hypotheses. -/
theorem velocity_mass (R : J → ℝ → Matrix I I ℂ) (u : J → ℂ) (a b : J → ℝ)
    (hprincipal : (∑ j,∫ t in (a j)..(b j),u j • R j t)=(2*(Real.pi : ℂ)*Complex.I) • (1 : Matrix I I ℂ)) :
    (∑ j,∫ t in (a j)..(b j),velocityTerm (R j t) (u j))=
      (2*(Real.pi : ℂ)) • (1 : Matrix I I ℂ) := by
  have heq : (∑ j,∫ t in (a j)..(b j),velocityTerm (R j t) (u j))=
      (-Complex.I) • (∑ j,∫ t in (a j)..(b j),u j • R j t) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← intervalIntegral.integral_smul]
    simp only [velocityTerm,smul_smul]
  rw [heq,hprincipal,smul_smul]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

/-- The identity or estimate `matrixPanelDensity_mass_of_principal` holds with the displayed separation, geometry and norm hypotheses. -/
theorem matrixPanelDensity_mass_of_principal (R : J → ℝ → Matrix I I ℂ) (u : J → ℂ) (a b : J → ℝ)
    (hR : ∀ j,IntervalIntegrable (R j) volume (a j) (b j))
    (hprincipal : (∑ j,∫ t in (a j)..(b j),u j • R j t)=(2*(Real.pi : ℂ)*Complex.I) • (1 : Matrix I I ℂ)) :
    (∑ j,∫ t in (a j)..(b j),matrixPanelDensity (R j t) (u j))=1 := by
  let G := fun j t => velocityTerm (R j t) (u j)
  have hg (j : J) : IntervalIntegrable (G j) volume (a j) (b j) := (hR j).smul (-Complex.I*u j)
  have hs := velocity_mass R u a b hprincipal
  have hstar : star ((2*(Real.pi : ℂ)) • (1 : Matrix I I ℂ))=(2*(Real.pi : ℂ)) • 1 := by
    simp only [star_smul,star_one,map_mul,Complex.star_def,Complex.conj_ofReal,map_ofNat]
  have hkernel : (∑ j,∫ t in (a j)..(b j),G j t+star (G j t))=
      (4*(Real.pi : ℂ)) • (1 : Matrix I I ℂ) := by
    calc
      _ = ∑ j,((∫ t in (a j)..(b j),G j t)+star (∫ t in (a j)..(b j),G j t)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [intervalIntegral.integral_add (hg j) (adjoint_integrable (G j) (a j) (b j) (hg j)),
          adjoint_intervalIntegral (G j) (a j) (b j) (hg j)]
      _ = (∑ j,∫ t in (a j)..(b j),G j t)+star (∑ j,∫ t in (a j)..(b j),G j t) := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact (map_sum (starAddEquiv : Matrix I I ℂ ≃+ Matrix I I ℂ) _ _).symm
      _ = _ := by rw [hs,hstar]; module
  have hfactor : (∑ j,∫ t in (a j)..(b j),matrixPanelDensity (R j t) (u j))=
      (((4*Real.pi)⁻¹ : ℝ) : ℂ) • (∑ j,∫ t in (a j)..(b j),G j t+star (G j t)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact intervalIntegral.integral_smul _ _
  rw [hfactor,hkernel,smul_smul]
  have hc : (((4*Real.pi)⁻¹ : ℝ) : ℂ)*(4*(Real.pi : ℂ))=1 := by
    norm_cast
    field_simp [Real.pi_ne_zero]
  rw [hc,one_smul]

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The matrix density integrated in the mass theorem is exactly the operator
whose positivity was proved from the actual numerical range. -/
theorem matrixPanelDensity_toEuclideanCLM (R : Matrix I I ℂ) (u : ℂ) :
    Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (matrixPanelDensity R u)=
      panelDensity (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) R) u := by
  simp only [matrixPanelDensity,velocityTerm,panelDensity,kernelOp,map_smul,map_add,map_star,star_smul,ContinuousLinearMap.star_eq_adjoint]

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
