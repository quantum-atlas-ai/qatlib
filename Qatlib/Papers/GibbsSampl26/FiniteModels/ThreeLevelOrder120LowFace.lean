/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowSourceTables
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowCoefficientTables
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinFirstElevation
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
# The actual order120 low collision face

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

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowFace
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain
open ThreeLevelGramCertificateCorner ThreeLevelCoordinateMetric ThreeLevelCornerForm
open ThreeLevelOrder120
open ThreeLevelCollisionFace

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

abbrev literalFaceStack (G q : ℝ) : Matrix (Fin 96) (Fin 15) ℂ :=
  ThreeLevelCollisionFace.polynomialStack ThreeLevelOrder120LowCoefficientTables.faceBase
    ThreeLevelOrder120LowCoefficientTables.faceUp
    ThreeLevelOrder120LowCoefficientTables.faceDown G q

def literalFaceGram (G q : ℝ) : Matrix (Fin 15) (Fin 15) ℂ :=
  (literalFaceStack G q)ᴴ * literalFaceStack G q

/-- Upper Coefficient Weight eq rational for the stated finite source data. -/
theorem upperCoefficientWeight_eq_rational (t : Fin 6) (i : Fin 5) (j : Fin 3) :
    ThreeLevelCollisionFace.coefficientWeight t i j =
      (ThreeLevelOrder120LowCoefficientTables.upperCoefficientWeight t i j : ℝ) := by
  fin_cases t <;>
    simp [ThreeLevelCollisionFace.coefficientWeight, ThreeLevelOrder120LowCoefficientTables.upperCoefficientWeight] <;>
    split_ifs <;> push_cast <;> ring

/-- Gram Pieces eq literal for the stated finite source data. -/
theorem gramPieces_eq_literal :
    ThreeLevelCollisionFace.gramPieces ThreeLevelOrder120LowCoefficientTables.faceBase
      ThreeLevelOrder120LowCoefficientTables.faceUp ThreeLevelOrder120LowCoefficientTables.faceDown =
        ThreeLevelOrder120LowCoefficientTables.gramPiece := by
  funext t
  fin_cases t <;>
    simp [ThreeLevelCollisionFace.gramPieces, ThreeLevelOrder120LowCoefficientTables.gramPiece,
      ThreeLevelOrder120LowCoefficientTables.gramBB_eq,
      ThreeLevelOrder120LowCoefficientTables.gramBU_eq,
      ThreeLevelOrder120LowCoefficientTables.gramBV_eq,
      ThreeLevelOrder120LowCoefficientTables.gramUU_eq,
      ThreeLevelOrder120LowCoefficientTables.gramUV_eq,
      ThreeLevelOrder120LowCoefficientTables.gramVV_eq]

/-- Upper Coefficient Form eq literal for the stated finite source data. -/
theorem upperCoefficientForm_eq_literal (i : Fin 5) (j : Fin 3) :
    ThreeLevelCollisionFace.coefficientForm (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder120LowCoefficientTables.faceBase
      ThreeLevelOrder120LowCoefficientTables.faceUp
      ThreeLevelOrder120LowCoefficientTables.faceDown) i j =
        ThreeLevelOrder120LowCoefficientTables.upperCoefficientGram i j := by
  simp only [ThreeLevelCollisionFace.coefficientForm, gramPieces_eq_literal, upperCoefficientWeight_eq_rational,
    ThreeLevelOrder120LowCoefficientTables.upperCoefficientGram]

/-- Lower Coefficient Weight eq rational for the stated finite source data. -/
theorem lowerCoefficientWeight_eq_rational (t : Fin 6) (i : Fin 7) (j : Fin 4) :
    ThreeLevelBernsteinFirstElevation.coefficientWeight t i j =
      (ThreeLevelOrder120LowCoefficientTables.lowerCoefficientWeight t i j : ℝ) := by
  fin_cases t <;> fin_cases i <;> fin_cases j <;>
    norm_num [ThreeLevelBernsteinFirstElevation.coefficientWeight,
      ThreeLevelBernsteinFirstElevation.elevationWeight,
      ThreeLevelBernsteinElevation.coefficientWeight,
      ThreeLevelOrder120LowCoefficientTables.lowerCoefficientWeight,
      Fin.sum_univ_succ]


/-- Lower Coefficient Form eq literal for the stated finite source data. -/
theorem lowerCoefficientForm_eq_literal (i : Fin 7) (j : Fin 4) :
    ThreeLevelBernsteinFirstElevation.coefficientForm
      (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder120LowCoefficientTables.faceBase
        ThreeLevelOrder120LowCoefficientTables.faceUp
        ThreeLevelOrder120LowCoefficientTables.faceDown) i j =
      ThreeLevelOrder120LowCoefficientTables.lowerCoefficientGram i j := by
  simp only [ThreeLevelBernsteinFirstElevation.coefficientForm, gramPieces_eq_literal,
    lowerCoefficientWeight_eq_rational,
    ThreeLevelOrder120LowCoefficientTables.lowerCoefficientGram]

/-- The degree-(6,3) lower family reconstructs the exact full complex residual. -/
theorem lower_reconstruction (G q : ℝ) :
    ThreeLevelBernsteinFirstElevation.faceMatrixValue
      ThreeLevelOrder120LowCertificates.lowerCoefficient G q =
      literalFaceGram G q - cornerMetric := by
  have hC : ThreeLevelOrder120LowCertificates.lowerCoefficient =
      fun i j => ThreeLevelBernsteinFirstElevation.coefficientForm
        (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder120LowCoefficientTables.faceBase
          ThreeLevelOrder120LowCoefficientTables.faceUp
          ThreeLevelOrder120LowCoefficientTables.faceDown) i j - cornerMetric := by
    funext i j
    rw [ThreeLevelOrder120LowCoefficientTables.lowerCoefficient_eq_gram_sub_metric,
      lowerCoefficientForm_eq_literal]
  rw [hC, ThreeLevelBernsteinFirstElevation.faceMatrixValue_sub,
    ThreeLevelBernsteinFirstElevation.faceMatrixValue_gram,
    ThreeLevelBernsteinFirstElevation.faceMatrixValue_const]
  rfl

/-- Upper reconstruction for the stated finite source data. -/
theorem upper_reconstruction (G q : ℝ) :
    ThreeLevelCollisionFace.faceMatrixValue ThreeLevelOrder120LowCertificates.upperCoefficient G q =
      (34 : ℝ) • cornerMetric - literalFaceGram G q := by
  have hC : ThreeLevelOrder120LowCertificates.upperCoefficient =
      fun i j => (34 : ℝ) • cornerMetric - ThreeLevelCollisionFace.coefficientForm
        (ThreeLevelCollisionFace.gramPieces ThreeLevelOrder120LowCoefficientTables.faceBase
          ThreeLevelOrder120LowCoefficientTables.faceUp
          ThreeLevelOrder120LowCoefficientTables.faceDown) i j := by
    funext i j
    rw [ThreeLevelOrder120LowCoefficientTables.upperCoefficient_eq_metric_sub_gram,
      upperCoefficientForm_eq_literal]
  rw [hC, ThreeLevelCollisionFace.faceMatrixValue_sub, ThreeLevelCollisionFace.faceMatrixValue_const, ThreeLevelCollisionFace.faceMatrixValue_gram]
  rfl

/-- Literal Face Gram lower pos Semidef for the stated finite source data. -/
theorem literalFaceGram_lower_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (literalFaceGram G q - cornerMetric).PosSemidef := by
  rw [← lower_reconstruction]
  exact ThreeLevelBernsteinFirstElevation.faceMatrixValue_posSemidef
    ThreeLevelOrder120LowCertificates.lowerCoefficient hG hq
    ThreeLevelOrder120LowCertificates.lowerCoefficient_posSemidef

/-- Literal Face Gram upper pos Semidef for the stated finite source data. -/
theorem literalFaceGram_upper_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ((34 : ℝ) • cornerMetric - literalFaceGram G q).PosSemidef := by
  rw [← upper_reconstruction]
  exact ThreeLevelCollisionFace.faceMatrixValue_posSemidef ThreeLevelOrder120LowCertificates.upperCoefficient hG hq
    ThreeLevelOrder120LowCertificates.upperCoefficient_posSemidef

/-- Literal Base full Coordinates for the stated finite source data. -/
theorem literalBase_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (ThreeLevelOrder120LowCoefficientTables.faceBase *ᵥ fullCoordinates c d Y) a =
      sourceBase order120 c d Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelOrder120LowSourceTables.faceBase_mulVec c d Y hY a

/-- Literal Up full Coordinates for the stated finite source data. -/
theorem literalUp_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (ThreeLevelOrder120LowCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      sourceUp order120 Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelOrder120LowSourceTables.faceUp_mulVec c d Y hY a

/-- Literal Down full Coordinates for the stated finite source data. -/
theorem literalDown_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (ThreeLevelOrder120LowCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      sourceDown order120 c Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelOrder120LowSourceTables.faceDown_mulVec c d Y hY a

/-- The concrete polynomial stack acts as the exact scaled six-source map on
all15 complex coordinates; the full fast input is reconstructed internally. -/
theorem literalFaceStack_fullCoordinates (G q : ℝ) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (literalFaceStack G q *ᵥ fullCoordinates c d Y) a =
      compactFaceSource order120 G q c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  simp only [literalFaceStack, ThreeLevelCollisionFace.polynomialStack, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, literalBase_fullCoordinates c d Y hY a,
    literalUp_fullCoordinates c d Y hY a, literalDown_fullCoordinates c d Y hY a]
  rw [compactFaceSource_three_terms]
  simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]

/-- Literal Face Stack actual for the stated finite source data. -/
theorem literalFaceStack_actual (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (literalFaceStack (halfWeight s) (compactAmplitude s) *ᵥ fullCoordinates c d Y) a =
      scaledSource order120 0 s c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  rw [literalFaceStack_fullCoordinates _ _ c d Y hY a, compactFaceSource_actual _ s hs]

/-- Literal Face Gram full Coordinates for the stated finite source data. -/
theorem literalFaceGram_fullCoordinates (s : ℝ) (hs : 0 ≤ s) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast order120 Y) :
    ThreeLevelBernstein.quadratic (literalFaceGram (halfWeight s) (compactAmplitude s))
      (fullCoordinates c d Y) = stackSquare order120 0 s c d Y := by
  rw [literalFaceGram, quadratic_gram_eq_sum_normSq]
  simp_rw [literalFaceStack_actual s hs c d Y hY]
  exact sum_normSq_flat_source (scaledSource order120 0 s c d Y)

/-- An unconditional finite-temperature collision-face certificate for order120.
Both residual identities, every PSD coefficient and the actual source/metric
reconstruction have been discharged by ordinary kernel proofs. -/
theorem collision_scaledStackBounds (s : ℝ) (hs : 0 ≤ s) :
    ScaledStackBounds order120 0 s 1 34 := by
  intro c d Y hY
  obtain ⟨hG,hq⟩ := physical_face_parameters s hs
  have hb := ThreeLevelBernstein.quadratic_bounds cornerMetric
    (literalFaceGram (halfWeight s) (compactAmplitude s)) 1 34
    (by simpa only [one_smul] using literalFaceGram_lower_posSemidef hG hq)
    (literalFaceGram_upper_posSemidef hG hq) (fullCoordinates c d Y)
  rw [cornerMetric_fullCoordinates_quadratic order120 c d Y hY,
    literalFaceGram_fullCoordinates s hs c d Y hY] at hb
  exact hb

/-- Collision plain Energy bounds for the stated finite source data. -/
theorem collision_plainEnergy_bounds (s : ℝ) (hs : 0 ≤ s) (X : Operator 4) :
    (1/12 : ℝ) * invariantMass order120 0 s X ≤
        plainEnergy order120 0 s X ∧
      plainEnergy order120 0 s X ≤
        (17/6 : ℝ) * invariantMass order120 0 s X := by
  convert plainEnergy_bounds order120 0 s 1 34
    (collision_scaledStackBounds s hs) X using 1
  norm_num

/-- Collision clock Energy bounds for the stated finite source data. -/
theorem collision_clockEnergy_bounds (β s : ℝ) (hs : 0 ≤ s)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    (1/12 : ℝ) * invariantMass order120 0 s X ≤
        clockEnergy order120 β 0 s μ X ∧
      clockEnergy order120 β 0 s μ X ≤
        (17/6 : ℝ) * invariantMass order120 0 s X := by
  convert clockEnergy_bounds order120 β 0 s 1 34
    (collision_scaledStackBounds s hs) μ X using 1
  norm_num

/-- Collision clock Energy comparison for the stated finite source data. -/
theorem collision_clockEnergy_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy order120 β 0 s ν X ≤
      34 * clockEnergy order120 β 0 s μ X :=
  clockEnergy_comparison_34 order120 β 0 s
    (collision_scaledStackBounds s hs) μ ν X

/-- Collision clock Energy kernel for the stated finite source data. -/
theorem collision_clockEnergy_kernel (β s : ℝ) (hs : 0 ≤ s)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy order120 β 0 s μ X = 0 ↔
      ∃ c : ℂ, X = c • gibbsRoot order120 (lowEnergies 0 s) :=
  clockEnergy_eq_zero_iff order120 β 0 s 1 34
    (by norm_num) (collision_scaledStackBounds s hs) μ X

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowFace
