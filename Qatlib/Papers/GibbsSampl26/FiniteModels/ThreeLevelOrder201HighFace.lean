/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighSourceTables
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighCoefficientTables
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum

@[expose] public section


/-!
# The actual order201 high collision face

The complete three-term source and both residual Bernstein reconstructions
are checked in the original full complex coordinate metric. All source
columns are attached directly to the actual Pauli operators; no
identity-order population coordinate conversion is assumed.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighFace
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain
open ThreeLevelGramCertificateCorner ThreeLevelCoordinateMetric ThreeLevelCornerForm
open ThreeLevelOrder201
open ThreeLevelHighCollisionFace

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

abbrev literalFaceStack (G q : ℝ) : Matrix (Fin 96) (Fin 15) ℂ :=
  ThreeLevelCollisionFace.polynomialStack ThreeLevelOrder201HighCoefficientTables.faceBase
    ThreeLevelOrder201HighCoefficientTables.faceUp
    ThreeLevelOrder201HighCoefficientTables.faceDown G q

def literalFaceGram (G q : ℝ) : Matrix (Fin 15) (Fin 15) ℂ :=
  (literalFaceStack G q)ᴴ * literalFaceStack G q

/-- Coefficient Weight eq rational for the stated finite source data. -/
theorem coefficientWeight_eq_rational (t : Fin 6) (i : Fin 5) (j : Fin 3) :
    ThreeLevelCollisionFace.coefficientWeight t i j =
      (ThreeLevelOrder201HighCoefficientTables.coefficientWeight t i j : ℝ) := by
  fin_cases t <;>
    simp [ThreeLevelCollisionFace.coefficientWeight, ThreeLevelOrder201HighCoefficientTables.coefficientWeight] <;>
    split_ifs <;> push_cast <;> ring

/-- Gram Pieces eq literal for the stated finite source data. -/
theorem gramPieces_eq_literal :
    ThreeLevelCollisionFace.gramPieces ThreeLevelOrder201HighCoefficientTables.faceBase
      ThreeLevelOrder201HighCoefficientTables.faceUp ThreeLevelOrder201HighCoefficientTables.faceDown =
        ThreeLevelOrder201HighCoefficientTables.gramPiece := by
  funext t
  fin_cases t <;>
    simp [ThreeLevelCollisionFace.gramPieces, ThreeLevelOrder201HighCoefficientTables.gramPiece,
      ThreeLevelOrder201HighCoefficientTables.gramBB_eq,
      ThreeLevelOrder201HighCoefficientTables.gramBU_eq,
      ThreeLevelOrder201HighCoefficientTables.gramBV_eq,
      ThreeLevelOrder201HighCoefficientTables.gramUU_eq,
      ThreeLevelOrder201HighCoefficientTables.gramUV_eq,
      ThreeLevelOrder201HighCoefficientTables.gramVV_eq]

/-- Coefficient Form eq literal for the stated finite source data. -/
theorem coefficientForm_eq_literal (i : Fin 5) (j : Fin 3) :
    ThreeLevelCollisionFace.coefficientForm (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder201HighCoefficientTables.faceBase
      ThreeLevelOrder201HighCoefficientTables.faceUp
      ThreeLevelOrder201HighCoefficientTables.faceDown) i j =
        ThreeLevelOrder201HighCoefficientTables.coefficientGram i j := by
  simp only [ThreeLevelCollisionFace.coefficientForm, gramPieces_eq_literal, coefficientWeight_eq_rational,
    ThreeLevelOrder201HighCoefficientTables.coefficientGram]

/-- Every lower residual coefficient is the previously checked concrete
Gaussian-rational matrix, with the exact six-product incidence discharged. -/
theorem lower_reconstruction (G q : ℝ) :
    ThreeLevelCollisionFace.faceMatrixValue ThreeLevelOrder201HighCertificates.lowerCoefficient G q =
      literalFaceGram G q - cornerMetric := by
  have hC : ThreeLevelOrder201HighCertificates.lowerCoefficient =
      fun i j => ThreeLevelCollisionFace.coefficientForm
        (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder201HighCoefficientTables.faceBase
          ThreeLevelOrder201HighCoefficientTables.faceUp
          ThreeLevelOrder201HighCoefficientTables.faceDown) i j - cornerMetric := by
    funext i j
    rw [ThreeLevelOrder201HighCoefficientTables.lowerCoefficient_eq_gram_sub_metric,
      coefficientForm_eq_literal]
  rw [hC, ThreeLevelCollisionFace.faceMatrixValue_sub, ThreeLevelCollisionFace.faceMatrixValue_gram, ThreeLevelCollisionFace.faceMatrixValue_const]
  rfl

/-- Upper reconstruction for the stated finite source data. -/
theorem upper_reconstruction (G q : ℝ) :
    ThreeLevelCollisionFace.faceMatrixValue ThreeLevelOrder201HighCertificates.upperCoefficient G q =
      (34 : ℝ) • cornerMetric - literalFaceGram G q := by
  have hC : ThreeLevelOrder201HighCertificates.upperCoefficient =
      fun i j => (34 : ℝ) • cornerMetric - ThreeLevelCollisionFace.coefficientForm
        (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder201HighCoefficientTables.faceBase
          ThreeLevelOrder201HighCoefficientTables.faceUp
          ThreeLevelOrder201HighCoefficientTables.faceDown) i j := by
    funext i j
    rw [ThreeLevelOrder201HighCoefficientTables.upperCoefficient_eq_metric_sub_gram,
      coefficientForm_eq_literal]
  rw [hC, ThreeLevelCollisionFace.faceMatrixValue_sub, ThreeLevelCollisionFace.faceMatrixValue_const, ThreeLevelCollisionFace.faceMatrixValue_gram]
  rfl

/-- Literal Face Gram lower pos Semidef for the stated finite source data. -/
theorem literalFaceGram_lower_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (literalFaceGram G q - cornerMetric).PosSemidef := by
  rw [← lower_reconstruction]
  exact ThreeLevelCollisionFace.faceMatrixValue_posSemidef ThreeLevelOrder201HighCertificates.lowerCoefficient hG hq
    ThreeLevelOrder201HighCertificates.lowerCoefficient_posSemidef

/-- Literal Face Gram upper pos Semidef for the stated finite source data. -/
theorem literalFaceGram_upper_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ((34 : ℝ) • cornerMetric - literalFaceGram G q).PosSemidef := by
  rw [← upper_reconstruction]
  exact ThreeLevelCollisionFace.faceMatrixValue_posSemidef ThreeLevelOrder201HighCertificates.upperCoefficient hG hq
    ThreeLevelOrder201HighCertificates.upperCoefficient_posSemidef

/-- Literal Base full Coordinates for the stated finite source data. -/
theorem literalBase_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order201 Y) (a : Fin 96) :
    (ThreeLevelOrder201HighCoefficientTables.faceBase *ᵥ fullCoordinates c d Y) a =
      sourceBase order201 c d Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelOrder201HighSourceTables.faceBase_mulVec c d Y hY a

/-- Literal Up full Coordinates for the stated finite source data. -/
theorem literalUp_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order201 Y) (a : Fin 96) :
    (ThreeLevelOrder201HighCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      sourceUp order201 d Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelOrder201HighSourceTables.faceUp_mulVec c d Y hY a

/-- Literal Down full Coordinates for the stated finite source data. -/
theorem literalDown_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order201 Y) (a : Fin 96) :
    (ThreeLevelOrder201HighCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      sourceDown order201 Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelOrder201HighSourceTables.faceDown_mulVec c d Y hY a

/-- The concrete polynomial stack acts as the exact scaled six-source map on
all15 complex coordinates; the full fast input is reconstructed internally. -/
theorem literalFaceStack_fullCoordinates (G q : ℝ) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order201 Y) (a : Fin 96) :
    (literalFaceStack G q *ᵥ fullCoordinates c d Y) a =
      compactFaceSource order201 G q c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  simp only [literalFaceStack, ThreeLevelCollisionFace.polynomialStack, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, literalBase_fullCoordinates c d Y hY a,
    literalUp_fullCoordinates c d Y hY a, literalDown_fullCoordinates c d Y hY a]
  rw [compactFaceSource_three_terms]
  simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]

/-- Literal Face Stack actual for the stated finite source data. -/
theorem literalFaceStack_actual (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order201 Y) (a : Fin 96) :
    (literalFaceStack (halfWeight S) (compactAmplitude S) *ᵥ fullCoordinates c d Y) a =
      scaledSource order201 S 0 c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  rw [literalFaceStack_fullCoordinates _ _ c d Y hY a, compactFaceSource_actual _ S hs]

/-- Literal Face Gram full Coordinates for the stated finite source data. -/
theorem literalFaceGram_fullCoordinates (S : ℝ) (hs : 0 ≤ S) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast order201 Y) :
    ThreeLevelBernstein.quadratic (literalFaceGram (halfWeight S) (compactAmplitude S))
      (fullCoordinates c d Y) = stackSquare order201 S 0 c d Y := by
  rw [literalFaceGram, quadratic_gram_eq_sum_normSq]
  simp_rw [literalFaceStack_actual S hs c d Y hY]
  exact sum_normSq_flat_source (scaledSource order201 S 0 c d Y)

/-- An unconditional finite-temperature collision-face certificate for order201.
Both residual identities, every PSD coefficient and the actual source/metric
reconstruction have been discharged by ordinary kernel proofs. -/
theorem collision_scaledStackBounds (S : ℝ) (hs : 0 ≤ S) :
    ScaledStackBounds order201 S 0 1 34 := by
  intro c d Y hY
  obtain ⟨hG,hq⟩ := physical_face_parameters S hs
  have hb := ThreeLevelBernstein.quadratic_bounds cornerMetric
    (literalFaceGram (halfWeight S) (compactAmplitude S)) 1 34
    (by simpa only [one_smul] using literalFaceGram_lower_posSemidef hG hq)
    (literalFaceGram_upper_posSemidef hG hq) (fullCoordinates c d Y)
  rw [cornerMetric_fullCoordinates_quadratic order201 c d Y hY,
    literalFaceGram_fullCoordinates S hs c d Y hY] at hb
  exact hb

/-- Collision plain Energy bounds for the stated finite source data. -/
theorem collision_plainEnergy_bounds (S : ℝ) (hs : 0 ≤ S) (X : Operator 4) :
    (1/12 : ℝ) * invariantMass order201 S 0 X ≤
        plainEnergy order201 S 0 X ∧
      plainEnergy order201 S 0 X ≤
        (17/6 : ℝ) * invariantMass order201 S 0 X := by
  convert plainEnergy_bounds order201 S 0 1 34
    (collision_scaledStackBounds S hs) X using 1
  norm_num

/-- Collision clock Energy bounds for the stated finite source data. -/
theorem collision_clockEnergy_bounds (β S : ℝ) (hs : 0 ≤ S)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    (1/12 : ℝ) * invariantMass order201 S 0 X ≤
        clockEnergy order201 β S 0 μ X ∧
      clockEnergy order201 β S 0 μ X ≤
        (17/6 : ℝ) * invariantMass order201 S 0 X := by
  convert clockEnergy_bounds order201 β S 0 1 34
    (collision_scaledStackBounds S hs) μ X using 1
  norm_num

/-- Collision clock Energy comparison for the stated finite source data. -/
theorem collision_clockEnergy_comparison (β S : ℝ) (hs : 0 ≤ S)
    (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy order201 β S 0 ν X ≤
      34 * clockEnergy order201 β S 0 μ X :=
  clockEnergy_comparison_34 order201 β S 0
    (collision_scaledStackBounds S hs) μ ν X

/-- Collision clock Energy kernel for the stated finite source data. -/
theorem collision_clockEnergy_kernel (β S : ℝ) (hs : 0 ≤ S)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy order201 β S 0 μ X = 0 ↔
      ∃ c : ℂ, X = c • gibbsRoot order201 (lowEnergies S 0) :=
  clockEnergy_eq_zero_iff order201 β S 0 1 34
    (by norm_num) (collision_scaledStackBounds S hs) μ X

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighFace
