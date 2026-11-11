/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.LocalResolventApproximation
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! Positive double-layer kernels from the actual numerical-range support
inequality and the actual right inverse. The velocity normal -i*u includes
its arclength weight; no division by the panel speed is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open ContinuousLinearMap
open scoped InnerProduct
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The identity or estimate `positive_of_unit` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem positive_of_unit (S : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (hunit : ∀ x,‖x‖=1 → 0≤(inner ℂ x (S x)).re) : S.IsPositive := by
  apply isPositive_def'.mpr
  refine ⟨hS,?_⟩
  intro x
  change 0≤(inner ℂ (S x) x).re
  have hre : (inner ℂ (S x) x).re=(inner ℂ x (S x)).re := inner_re_symm (𝕜 := ℂ) (S x) x
  rw [hre]
  by_cases hx : x=0
  · simp [hx]
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  let u := ((‖x‖ : ℂ)⁻¹) • x
  have hu : ‖u‖=1 := by
    simp [u,norm_smul,norm_inv,Complex.norm_real,inv_mul_cancel₀ hn.ne']
  have hxu : x=(‖x‖ : ℂ) • u := by
    simp [u,smul_smul,hn.ne']
  have hh := hunit u hu
  rw [hxu]
  simp only [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg hn.le (mul_nonneg hn.le hh)

/-- Construction for support Op in the double layer kernel model. -/
def supportOp (A : E →L[ℂ] E) (z n : ℂ) : E →L[ℂ] E :=
  star n • shiftedOperator A z+n • (shiftedOperator A z)†
/-- Construction for kernel Op in the double layer kernel model. -/
def kernelOp (R : E →L[ℂ] E) (n : ℂ) : E →L[ℂ] E := n • R+star n • R†

/-- The identity or estimate `supportOp_selfadjoint` holds with the displayed separation, geometry and norm hypotheses. -/
theorem supportOp_selfadjoint (A : E →L[ℂ] E) (z n : ℂ) : IsSelfAdjoint (supportOp A z n) := by
  change star (supportOp A z n)=supportOp A z n
  simp only [supportOp,← star_eq_adjoint,star_add,star_smul,star_star]
  abel

/-- The identity or estimate `supportOp_unit` holds with the displayed separation, geometry and norm hypotheses. -/
theorem supportOp_unit (A : E →L[ℂ] E) (z n : ℂ) (x : E) (hx : ‖x‖=1) :
    (inner ℂ x (supportOp A z n x)).re=2*(star n*(z-inner ℂ x (A x))).re := by
  have hz : inner ℂ x (shiftedOperator A z x)=z-inner ℂ x (A x) := by
    simp [shiftedOperator,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hx]
  simp only [supportOp,add_apply,smul_apply,inner_add_right,inner_smul_right,adjoint_inner_right]
  rw [← inner_conj_symm (𝕜 := ℂ) (x := shiftedOperator A z x) (y := x),hz]
  simp only [Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

/-- The identity or estimate `supportOp_positive` holds with the displayed separation, geometry and norm hypotheses. -/
theorem supportOp_positive (A : E →L[ℂ] E) (z n : ℂ)
    (hs : ∀ w∈numericalRange A,0≤(star n*(z-w)).re) : (supportOp A z n).IsPositive := by
  apply positive_of_unit _ (supportOp_selfadjoint A z n)
  intro x hx
  rw [supportOp_unit A z n x hx]
  exact mul_nonneg (by norm_num) (hs _ ⟨x,hx,rfl⟩)

/-- Only the actual inverse identity is used in the kernel congruence. -/
theorem kernel_congruence (A R : E →L[ℂ] E) (z n : ℂ)
    (hZR : shiftedOperator A z*R=1) :
    kernelOp R n=R† ∘L supportOp A z n ∘L R := by
  have hadj : R†*(shiftedOperator A z)†=1 := by
    have hh := congrArg star hZR
    simpa only [star_mul,star_one,star_eq_adjoint] using hh
  change _=R†*(supportOp A z n*R)
  simp only [supportOp,kernelOp,add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  rw [hZR,mul_one,← mul_assoc,hadj,one_mul]
  abel

/-- The identity or estimate `kernel_positive` holds with the displayed separation, geometry and norm hypotheses. -/
theorem kernel_positive (A R : E →L[ℂ] E) (z n : ℂ)
    (hs : ∀ w∈numericalRange A,0≤(star n*(z-w)).re)
    (hZR : shiftedOperator A z*R=1) : (kernelOp R n).IsPositive := by
  rw [kernel_congruence A R z n hZR]
  exact (supportOp_positive A z n hs).adjoint_conj R

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open ContinuousLinearMap
open scoped InnerProduct ComplexOrder
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Density with respect to the panel parameter, including its actual velocity.
The factor 4*pi is chosen for total mass I, not 2I. -/
def panelDensity (R : E →L[ℂ] E) (u : ℂ) : E →L[ℂ] E :=
  (((4*Real.pi)⁻¹ : ℝ) : ℂ) • kernelOp R (-Complex.I*u)

/-- The identity or estimate `panelDensity_positive` holds with the displayed separation, geometry and norm hypotheses. -/
theorem panelDensity_positive (A R : E →L[ℂ] E) (z u : ℂ)
    (hs : ∀ w∈numericalRange A,0≤(star (-Complex.I*u)*(z-w)).re)
    (hZR : shiftedOperator A z*R=1) : (panelDensity R u).IsPositive := by
  have hc : 0≤(((4*Real.pi)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast (inv_nonneg.mpr (by positivity : (0 : ℝ)≤4*Real.pi))
  exact (kernel_positive A R z (-Complex.I*u) hs hZR).smul_of_nonneg hc

/-- The identity or estimate `panelDensity_zero_velocity` holds with the displayed separation, geometry and norm hypotheses. -/
theorem panelDensity_zero_velocity (R : E →L[ℂ] E) : panelDensity R 0=0 := by
  simp only [panelDensity,mul_zero,kernelOp,star_zero,zero_smul,add_zero,smul_zero]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The positive kernel uses the actual resolvent selected from A and z;
its inverse law follows from the actual numerical-range separation. -/
theorem actual_matrix_panelDensity_positive (A : Matrix I I ℂ) (z u : ℂ) (r : ℝ)
    (hr : 0<r) (hsep : ∀ w∈matrixNumericalRange A,r≤‖z-w‖)
    (hs : ∀ w∈matrixNumericalRange A,0≤(star (-Complex.I*u)*(z-w)).re) :
    (panelDensity (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (matrixResolvent A z)) u).IsPositive := by
  let e := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  have hZ : e (matrixShift A z)=shiftedOperator (e A) z := by
    change e (z • (1 : Matrix I I ℂ)-A)=z • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I)-e A
    rw [map_sub,map_smul,map_one]
    rfl
  have hm := (matrixResolvent_inverse_norm_of_separation A z r hr hsep).1
  have he := congrArg e hm
  simp only [map_mul,map_one] at he
  apply panelDensity_positive (e A) (e (matrixResolvent A z)) z u hs
  simpa only [hZ] using he

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open ContinuousLinearMap
open scoped InnerProduct
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The identity or estimate `support_closed` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem support_closed (A : E →L[ℂ] E) (z n : ℂ) :
    supportOp A z n=(star n*z+n*star z) • (1 : E →L[ℂ] E)-star n • A-n • A† := by
  simp only [supportOp,shiftedOperator,← one_def,← star_eq_adjoint,star_sub,star_smul,star_one]
  module

/-- The identity or estimate `support_constant` holds with the displayed separation, geometry and norm hypotheses. -/
theorem support_constant (A : E →L[ℂ] E) (z u : ℂ) (t : ℝ) :
    supportOp A (z+(t : ℂ)*u) (-Complex.I*u)=supportOp A z (-Complex.I*u) := by
  have hc : star (-Complex.I*u)*(z+(t : ℂ)*u)+(-Complex.I*u)*star (z+(t : ℂ)*u)=
      star (-Complex.I*u)*z+(-Complex.I*u)*star z := by
    simp only [Complex.star_def,map_add,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal]
    ring
  rw [support_closed,support_closed,hc]

/-- The identity or estimate `support_panel_constant` holds with the displayed separation, geometry and norm hypotheses. -/
theorem support_panel_constant (A : E →L[ℂ] E) (z u : ℂ) (a h t : ℝ) :
    supportOp A (contourPanel z u a h t) (-Complex.I*u)=supportOp A z (-Complex.I*u) :=
  support_constant A z u (t-(a+h/2))

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open ContinuousLinearMap
open scoped BigOperators
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A single finite Gram family works on the whole straight panel. The vectors
are derived mathematical witnesses, not classical inputs to the query algorithm. -/
theorem exists_fixed_panel_gram [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (z u : ℂ)
    (hs : ∀ w∈numericalRange A,0≤(star (-Complex.I*u)*(z-w)).re) :
    ∃ (m : ℕ) (v : Fin m → E),∀ a h t : ℝ,
      supportOp A (contourPanel z u a h t) (-Complex.I*u)=
        ∑ i,InnerProductSpace.rankOne ℂ (v i) (v i) := by
  obtain ⟨m,v,hv⟩ := isPositive_iff_eq_sum_rankOne.mp (supportOp_positive A z (-Complex.I*u) hs)
  refine ⟨m,v,?_⟩
  intro a h t
  rw [support_panel_constant,hv]

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
