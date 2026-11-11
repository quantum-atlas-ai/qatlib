/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayerFlatGram
import Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayerMass
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2


/-! Actual finite-matrix resolvents generate one continuous scalar L2 frame
and one contraction with all adjoint moments. The density mass is a certified
contour input; the strict consumer derives it from finite support/crossings.
No isometry, final norm bound or free inverse is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2
open Matrix MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped Matrix.Norms.L2Operator BigOperators InnerProduct Classical
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "H" => EuclideanSpace ℂ I
local notation "Op" => (H →L[ℂ] H)
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- Construction for operator Iso in the double layer polygon l2 model. -/
def operatorIso : Matrix I I ℂ ≃L[ℂ] Op :=
  (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

/-- The identity or estimate `operatorIso_interval` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem operatorIso_interval (f : ℝ → Matrix I I ℂ) (a b : ℝ) :
    (∫ t in a..b,operatorIso (f t))=operatorIso (∫ t in a..b,f t) := by
  have ha : (∫ t in Set.Ioc a b,operatorIso (f t))=operatorIso (∫ t in Set.Ioc a b,f t) :=
    (operatorIso (I := I)).integral_comp_comm (μ := volume.restrict (Set.Ioc a b)) f
  have hb : (∫ t in Set.Ioc b a,operatorIso (f t))=operatorIso (∫ t in Set.Ioc b a,f t) :=
    (operatorIso (I := I)).integral_comp_comm (μ := volume.restrict (Set.Ioc b a)) f
  simp only [intervalIntegral,map_sub]
  rw [ha,hb]

variable {J : Type}

/-- Construction for canonical R in the double layer polygon l2 model. -/
def canonicalR (A : Matrix I I ℂ) (z v : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (v j) (-1) 2 (t : ℝ)-w‖) : J → C(PanelTime,Op) := fun j =>
  ⟨fun t => operatorIso (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 (t : ℝ))),by
    have hR : ContinuousOn
        (fun t : ℝ => matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (Set.Icc (-1 : ℝ) 1) :=
      (matrixResolvent_continuousOn_of_separation A r hr).comp
        (contourPanel_continuous (z j) (v j) (-1) 2).continuousOn (fun t ht => hsep j ⟨t,ht⟩)
    exact operatorIso.continuous.comp (continuousOn_iff_continuous_restrict.mp hR)⟩

/-- The identity or estimate `canonical_inverse` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem canonical_inverse (A : Matrix I I ℂ) (z : ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ w∈matrixNumericalRange A,r≤‖z-w‖) :
    shiftedOperator (operatorIso A) z*operatorIso (matrixResolvent A z)=1 := by
  let e := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  have hZ : e (matrixShift A z)=shiftedOperator (e A) z := by
    change e (z • (1 : Matrix I I ℂ)-A)=z • ContinuousLinearMap.id ℂ H-e A
    rw [map_sub,map_smul,map_one]
    rfl
  have he := congrArg e (matrixResolvent_inverse_norm_of_separation A z r hr hsep).1
  simp only [map_mul,map_one] at he
  simpa [hZ,e,operatorIso] using he

variable [Fintype J]

/-- The identity or estimate `operator_density_mass` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem operator_density_mass (A : Matrix I I ℂ) (z v : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (v j) (-1) 2 (t : ℝ)-w‖)
    (hMass : (∑ j,∫ t in (-1 : ℝ)..1,
      matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (v j))=1) :
    (∑ j,∫ t : PanelTime,panelDensity (canonicalR A z v r hr hsep j t) (v j))=1 := by
  calc
    _ = ∑ j,operatorIso (∫ t in (-1 : ℝ)..1,
        matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (v j)) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∫ t : PanelTime,operatorIso
            (matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 (t : ℝ))) (v j)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t => (matrixPanelDensity_toEuclideanCLM _ _).symm)
        _ = ∫ t in (-1 : ℝ)..1,operatorIso
            (matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (v j)) :=
          panelTime_integral (B := Op) (fun t : ℝ => operatorIso
            (matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (v j)))
        _ = _ := operatorIso_interval _ _ _
    _ = operatorIso (∑ j,∫ t in (-1 : ℝ)..1,
        matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (v j)) := (map_sum operatorIso _ _).symm
    _ = 1 := by
      rw [hMass]
      exact (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).map_one

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2
open Matrix MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped Matrix.Norms.L2Operator BigOperators InnerProduct Classical
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
local notation "H" => EuclideanSpace ℂ I
local notation "Op" => (H →L[ℂ] H)
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

omit [Fintype J] in
/-- The identity or estimate `canonical_kernel` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem canonical_kernel (A : Matrix I I ℂ) (z v : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (v j) (-1) 2 (t : ℝ)-w‖)
    (m : J → ℕ) (a : ∀ j,Fin (m j) → H)
    (hGram : ∀ j,supportOp (operatorIso A) (z j) (-Complex.I*v j)=∑ i,rankOne ℂ (a j i) (a j i))
    (j : J) (t : PanelTime) :
    (canonicalR A z v r hr hsep j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L canonicalR A z v r hr hsep j t=
      kernelOp (canonicalR A z v r hr hsep j t) (-Complex.I*v j) := by
  rw [← hGram j,← support_panel_constant (operatorIso A) (z j) (v j) (-1) 2 (t : ℝ)]
  exact (kernel_congruence (operatorIso A) (canonicalR A z v r hr hsep j t)
    (contourPanel (z j) (v j) (-1) 2 (t : ℝ)) (-Complex.I*v j)
    (canonical_inverse A _ r hr (hsep j t))).symm

/-- The identity or estimate `normalized_kernel_moment` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem normalized_kernel_moment (A : Matrix I I ℂ) (z v : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (v j) (-1) 2 (t : ℝ)-w‖)
    (m : J → ℕ) (a : ∀ j,Fin (m j) → H)
    (hGram : ∀ j,supportOp (operatorIso A) (z j) (-Complex.I*v j)=∑ i,rankOne ℂ (a j i) (a j i))
    (f : J → C(PanelTime,ℂ)) (n : ℕ) :
    (4*Real.pi)⁻¹ • (∑ j,∫ t : PanelTime,(f j t)^n •
      ((canonicalR A z v r hr hsep j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L canonicalR A z v r hr hsep j t))=
      ∑ j,∫ t : PanelTime,(f j t)^n • panelDensity (canonicalR A z v r hr hsep j t) (v j) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  change (4*Real.pi)⁻¹ • ((f j t)^n •
    ((canonicalR A z v r hr hsep j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L canonicalR A z v r hr hsep j t))=
    (f j t)^n • panelDensity (canonicalR A z v r hr hsep j t) (v j)
  rw [canonical_kernel A z v r hr hsep m a hGram j t]
  simp only [panelDensity]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

/-- All mathematical dilation data are constructed from the same actual A,
canonical resolvents, true support, scalar weights and certified density mass. -/
theorem actual_polygon_dilation (A : Matrix I I ℂ) (z v : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (v j) (-1) 2 (t : ℝ)-w‖)
    (hsupport : ∀ j w,w∈matrixNumericalRange A → 0≤(star (-Complex.I*v j)*(z j-w)).re)
    (hMass : (∑ j,∫ t in (-1 : ℝ)..1,
      matrixPanelDensity (matrixResolvent A (contourPanel (z j) (v j) (-1) 2 t)) (v j))=1)
    (f : J → C(PanelTime,ℂ)) (hf : ∀ j t,‖f j t‖≤1) :
    ∃ (N : ℕ) (w : C(Fin N × PanelTime,H)) (g : C(Fin N × PanelTime,ℂ)),
      (∀ x,‖analysis (dilationMeasure N) w x‖=‖x‖) ∧
      ‖dilationContraction (dilationMeasure N) g‖≤1 ∧
      ∀ n : ℕ,(analysis (dilationMeasure N) w)† ∘L
        (((dilationContraction (dilationMeasure N) g)†)^n) ∘L analysis (dilationMeasure N) w=
        ∑ j,∫ t : PanelTime,(f j t)^n • panelDensity (canonicalR A z v r hr hsep j t) (v j) := by
  have hg (j : J) : ∃ (m : ℕ) (a : Fin m → H),
      supportOp (operatorIso A) (z j) (-Complex.I*v j)=∑ i,rankOne ℂ (a i) (a i) :=
    isPositive_iff_eq_sum_rankOne.mp (supportOp_positive (operatorIso A) (z j) (-Complex.I*v j) (hsupport j))
  choose m a hGram using hg
  let R := canonicalR A z v r hr hsep
  have hKernelMass : (4*Real.pi)⁻¹ • (∑ j,∫ t : PanelTime,
      (R j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L R j t)=1 := by
    have h0 := normalized_kernel_moment A z v r hr hsep m a hGram (fun _ => 1) 0
    simp only [pow_zero,one_smul] at h0
    exact h0.trans (operator_density_mass A z v r hr hsep hMass)
  obtain ⟨hV,hQ,hMom⟩ := flat_dilation m a R f hKernelMass hf
  refine ⟨rowCount m,flatFrame m a R,flatWeight m f,hV,hQ,?_⟩
  intro n
  exact (hMom n).trans (normalized_kernel_moment A z v r hr hsep m a hGram f n)

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2
