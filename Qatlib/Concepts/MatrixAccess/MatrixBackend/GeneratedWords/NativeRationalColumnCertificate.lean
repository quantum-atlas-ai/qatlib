/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeGroupedColumnError
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
/-! Executable coordinate residual from the actual rational PREP column.
The receipt bounds the existing grouped norm certificate; it is not an
assumed final matrix error or a success/precision theorem for a producer. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators

/-- Construction for gaussian Value Add Hom in the native rational column certificate model. -/
def gaussianValueAddHom : GaussianRat →+ ℂ where
  toFun := gaussianRatComplex
  map_zero' := by simp [gaussianRatComplex]
  map_add' := Qatlib.Concepts.NativeNumerics.PhaseSynthesis.complex_gadd

/-- Construction for rational Column Coefficient in the native rational column certificate model. -/
def rationalColumnCoefficient {n : ℕ} (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle))
    (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (a : Option (Fin n)) : GaussianRat :=
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gmul ((tablePreparedColumn rs a)^2,0)
    ((phase a).c,(phase a).s)

/-- Construction for rational Grouped Coefficient in the native rational column certificate model. -/
def rationalGroupedCoefficient {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (j : J) : GaussianRat :=
  ∑ a,if node a=j then rationalColumnCoefficient rs phase a else 0

/-- Construction for rational Desired Coefficient in the native rational column certificate model. -/
def rationalDesiredCoefficient {J : Type} (weights : J → GaussianRat) (L : ℚ) (j : J) : GaussianRat :=
  ((weights j).1/L,(weights j).2/L)

/-- Construction for rational Column Residual in the native rational column certificate model. -/
def rationalColumnResidual {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (L : ℚ) (j : J) : GaussianRat :=
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis.gsub (rationalDesiredCoefficient weights L j)
    (rationalGroupedCoefficient node rs phase j)

/-- Construction for rational Column D in the native rational column certificate model. -/
def rationalColumnD {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (L : ℚ) : ℚ :=
  ∑ j, (|(rationalColumnResidual node rs phase weights L j).1| +
    |(rationalColumnResidual node rs phase weights L j).2|)

/-- Construction for rational Column Check in the native rational column certificate model. -/
def rationalColumnCheck {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (L D : ℚ) : Bool := decide (rationalColumnD node rs phase weights L≤D)

/-- Construction for rational Weight Mass in the native rational column certificate model. -/
def rationalWeightMass {J : Type} [Fintype J] (weights : J → GaussianRat) : ℚ :=
  ∑ j, (|(weights j).1|+|(weights j).2|)

/-- Construction for rational Weight Mass Check in the native rational column certificate model. -/
def rationalWeightMassCheck {J : Type} [Fintype J] (weights : J → GaussianRat) (L : ℚ) : Bool :=
  (L==rationalWeightMass weights) && decide (0 < L)

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `rationalWeightMassCheck_iff` under the displayed hypotheses. -/
theorem rationalWeightMassCheck_iff {J : Type} [Fintype J] (weights : J → GaussianRat) (L : ℚ) :
    rationalWeightMassCheck weights L=true ↔ L=rationalWeightMass weights ∧ 0<L := by
  simp [rationalWeightMassCheck]

noncomputable section
open scoped Classical

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `rationalColumnCoefficient_complex` under the displayed hypotheses. -/
theorem rationalColumnCoefficient_complex {n : ℕ} (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle))
    (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (a : Option (Fin n)) :
    gaussianRatComplex (rationalColumnCoefficient rs phase a) =
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data.columnPhaseCoefficient (tableHouseholder rs) (fun a => phaseScalar (phase a)) none a := by
  rw [rationalColumnCoefficient, Qatlib.Concepts.NativeNumerics.PhaseSynthesis.complex_gmul,
    ← phaseScalar_as_gaussian]
  simp [gaussianRatComplex, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data.columnPhaseCoefficient, tableHouseholder_origin_column, pow_two]

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `rationalGroupedCoefficient_complex` under the displayed hypotheses. -/
theorem rationalGroupedCoefficient_complex {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (j : J) :
    gaussianRatComplex (rationalGroupedCoefficient node rs phase j) =
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data.groupedColumnCoefficient node (tableHouseholder rs) (fun a => phaseScalar (phase a)) none j := by
  change gaussianValueAddHom (∑ a,if node a=j then rationalColumnCoefficient rs phase a else 0)=_
  rw [map_sum]
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data.groupedColumnCoefficient
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : node a=j
  · simpa [ite_eq_left ha,gaussianValueAddHom] using rationalColumnCoefficient_complex rs phase a
  · simp [ha, gaussianValueAddHom, gaussianRatComplex]

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `rationalDesiredCoefficient_complex` under the displayed hypotheses. -/
theorem rationalDesiredCoefficient_complex {J : Type} (weights : J → GaussianRat) (L : ℚ) (j : J) :
    gaussianRatComplex (rationalDesiredCoefficient weights L j)=gaussianRatComplex (weights j)/(L : ℂ) := by
  simp only [rationalDesiredCoefficient, gaussianRatComplex, Rat.cast_div]
  ring

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `rationalColumnResidual_complex` under the displayed hypotheses. -/
theorem rationalColumnResidual_complex {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (L : ℚ) (j : J) :
    gaussianRatComplex (rationalColumnResidual node rs phase weights L j) =
      gaussianRatComplex (weights j)/(L : ℂ)-
        Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data.groupedColumnCoefficient node (tableHouseholder rs) (fun a => phaseScalar (phase a)) none j := by
  rw [rationalColumnResidual, Qatlib.Concepts.NativeNumerics.PhaseSynthesis.complex_gsub,
    rationalDesiredCoefficient_complex, rationalGroupedCoefficient_complex]

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `gaussianRat_norm_le_coordinate` under the displayed hypotheses. -/
theorem gaussianRat_norm_le_coordinate (z : GaussianRat) :
    ‖gaussianRatComplex z‖ ≤ ((|z.1|+|z.2| : ℚ) : ℝ) := by
  simpa [gaussianRatComplex] using Complex.norm_le_abs_re_add_abs_im (gaussianRatComplex z)

/-- The finite construction in `NativeRationalColumnCertificate` satisfies `rationalWeightMass_majorizes` under the displayed hypotheses. -/
theorem rationalWeightMass_majorizes {J : Type} [Fintype J] (weights : J → GaussianRat) :
    (∑ j,‖gaussianRatComplex (weights j)‖) ≤ (rationalWeightMass weights : ℝ) := by
  calc
    _ ≤ ∑ j, ((|(weights j).1|+|(weights j).2| : ℚ) : ℝ) :=
      Finset.sum_le_sum (fun j _ => gaussianRat_norm_le_coordinate (weights j))
    _ = _ := by simp [rationalWeightMass]

/-- Exactly the existing grouped scalar hypothesis, obtained by a finite
rational check over the supplied actual QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle table and phase data. -/
theorem rationalColumnCheck_sound {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (node : Option (Fin n) → J) (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (L D : ℚ) (hc : rationalColumnCheck node rs phase weights L D=true) :
    (∑ j, ‖gaussianRatComplex (weights j)/(L : ℂ)-
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data.groupedColumnCoefficient node (tableHouseholder rs) (fun a => phaseScalar (phase a)) none j‖) ≤ (D : ℝ) := by
  have hb : rationalColumnD node rs phase weights L≤D := by
    simpa only [rationalColumnCheck, decide_eq_true_eq] using hc
  have hr : (rationalColumnD node rs phase weights L : ℝ)≤(D : ℝ) := by exact_mod_cast hb
  calc
    _ = ∑ j, ‖gaussianRatComplex (rationalColumnResidual node rs phase weights L j)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [rationalColumnResidual_complex]
    _ ≤ ∑ j, ((|(rationalColumnResidual node rs phase weights L j).1|+
        |(rationalColumnResidual node rs phase weights L j).2| : ℚ) : ℝ) :=
      Finset.sum_le_sum (fun j _ => gaussianRat_norm_le_coordinate _)
    _ = (rationalColumnD node rs phase weights L : ℝ) := by simp [rationalColumnD]
    _ ≤ _ := hr

end
end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
