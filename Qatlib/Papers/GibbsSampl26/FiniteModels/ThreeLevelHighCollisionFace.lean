/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionSourceTables
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionCoefficientTables
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinElevation
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCornerForm
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinBridge
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
# The actual order012 high-cluster collision face

The s=0 source reduction retains both Gaussian thermal legs, all six original
sources and the full 15-complex-coordinate chart. The lower degree-(4,3) and
upper degree-(4,2) tensor Bernstein identities connect all 35 residual
occurrences to concrete kernel-checked positive coefficients. Actual source
and metric reconstruction discharge the scaled-stack premise and give the
original normalized physical clock bounds. The source formulas hold for all
permutations; the finite positivity result here is only for order012.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionFace
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

def mergedLow (σ : Perm) : Operator 4 :=
  spectralProjectors σ 0

def mergedHigh (σ : Perm) : Operator 4 :=
  spectralProjectors σ 1 + spectralProjectors σ 2

def faceDiagonal (σ : Perm) (A : Operator 4) : Operator 4 :=
  mergedLow σ * A * mergedLow σ + mergedHigh σ * A * mergedHigh σ

def faceBase (σ : Perm) (A X : Operator 4) : Operator 4 :=
  faceDiagonal σ A * X - X * faceDiagonal σ A

def faceUp (σ : Perm) (A X : Operator 4) : Operator 4 :=
  (mergedLow σ * A * mergedHigh σ) * X -
    X * (mergedHigh σ * A * mergedLow σ)

def faceDown (σ : Perm) (A X : Operator 4) : Operator 4 :=
  (mergedHigh σ * A * mergedLow σ) * X -
    X * (mergedLow σ * A * mergedHigh σ)

def faceGradient (σ : Perm) (G e : ℂ) (A X : Operator 4) : Operator 4 :=
  faceBase σ A X + e • faceUp σ A X + (G*e) • faceDown σ A X

def faceQuarter (a : ℂ) : Fin 3 → ℂ := ![1,a,a]
def faceWeights (a e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,e*a,e*a; e*a,1,1; e*a,1,1]
def faceSharpWeights (G e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,e,e; G*e,1,1; G*e,1,1]
def faceFlatWeights (G e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,G*e,G*e; e,1,1; e,1,1]

/-- Face sharp filter for the stated finite source data. -/
theorem face_sharp_filter (σ : Perm) (G e : ℂ) (A : Operator 4) :
    spectralFilter σ (faceSharpWeights G e) A =
      faceDiagonal σ A + e • (mergedLow σ*A*mergedHigh σ) +
        (G*e) • (mergedHigh σ*A*mergedLow σ) := by
  simp [spectralFilter, faceSharpWeights, faceDiagonal, mergedLow, mergedHigh,
    Fin.sum_univ_succ, Matrix.add_mul, Matrix.mul_add, smul_add]
  abel

/-- Face flat filter for the stated finite source data. -/
theorem face_flat_filter (σ : Perm) (G e : ℂ) (A : Operator 4) :
    spectralFilter σ (faceFlatWeights G e) A =
      faceDiagonal σ A + (G*e) • (mergedLow σ*A*mergedHigh σ) +
        e • (mergedHigh σ*A*mergedLow σ) := by
  simp [spectralFilter, faceFlatWeights, faceDiagonal, mergedLow, mergedHigh,
    Fin.sum_univ_succ, Matrix.add_mul, Matrix.mul_add, smul_add]
  abel

/-- Thermal Gradient face for the stated finite source data. -/
theorem thermalGradient_face (σ : Perm) (a e : ℂ) (ha : a ≠ 0)
    (A X : Operator 4) :
    thermalGradient σ (faceQuarter a) (faceWeights a e) A X =
      faceGradient σ (a^2) e A X := by
  have hsharp : (fun i j => faceQuarter a i * faceWeights a e i j *
      (faceQuarter a j)⁻¹) = faceSharpWeights (a^2) e := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [faceQuarter, faceWeights, faceSharpWeights] <;>
      field_simp [ha]
  have hflat : (fun i j => (faceQuarter a i)⁻¹ * faceWeights a e i j *
      faceQuarter a j) = faceFlatWeights (a^2) e := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [faceQuarter, faceWeights, faceFlatWeights] <;>
      field_simp [ha]
  rw [thermalGradient, population_filter_population, population_filter_population,
    hsharp, hflat, face_sharp_filter, face_flat_filter]
  simp only [faceGradient, faceBase, faceUp, faceDown, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

/-- Actual face quarter for the stated finite source data. -/
theorem actual_face_quarter (S : ℝ) :
    (fun i => quarterAmplitude (lowEnergies S 0 i)) =
      faceQuarter (quarterAmplitude S) := by
  funext i
  fin_cases i <;> simp [lowEnergies, faceQuarter, quarterAmplitude_zero]

/-- Actual face weights for the stated finite source data. -/
theorem actual_face_weights (S : ℝ) :
    gaussianWeights (lowEnergies S 0) =
      faceWeights (quarterAmplitude S) (smallAmplitude S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaussianWeights, lowEnergies, faceWeights,
      gaussianAmplitude_zero, gaussianAmplitude_neg, small_mul_quarter]

/-- Exact two-cluster source formula for every complex input, retaining both
thermal legs and every original source channel. -/
theorem actualGradient_collision_face (σ : Perm) (S : ℝ) (k : Fin 6)
    (X : Operator 4) :
    actualGradient σ (lowEnergies S 0) k X =
      faceGradient σ (halfWeight S : ℂ) (gain S : ℂ)
        (ThreeLevelWordDual.source k) X := by
  rw [actualGradient, actual_face_quarter, actual_face_weights,
    thermalGradient_face σ _ _ (quarterAmplitude_ne_zero S),
    quarterAmplitude_sq_eq_halfWeight, smallAmplitude_eq_gain]

def faceSource (σ : Perm) (G e c d : ℂ) (Y : Operator 4)
    (k : Fin 6) : Operator 4 :=
  c • (edge σ (ThreeLevelWordDual.source k) 0 1 +
      edge σ (ThreeLevelWordDual.source k) 0 2) +
  d • (edge σ (ThreeLevelWordDual.source k) 1 2 +
      e • edge σ (ThreeLevelWordDual.source k) 0 2) +
  faceGradient σ G e (ThreeLevelWordDual.source k) Y

/-- Column One collision face for the stated finite source data. -/
theorem columnOne_collision_face (σ : Perm) (S : ℝ) (k : Fin 6) :
    columnOne σ S 0 k =
      edge σ (ThreeLevelWordDual.source k) 0 1 +
        edge σ (ThreeLevelWordDual.source k) 0 2 := by
  rw [columnOne_eq_edges]
  simp [quarterAmplitude_zero, farRatio, cexp]

/-- Column Two collision face for the stated finite source data. -/
theorem columnTwo_collision_face (σ : Perm) (S : ℝ) (k : Fin 6) :
    columnTwo σ S 0 k =
      edge σ (ThreeLevelWordDual.source k) 1 2 +
        (gain S : ℂ) • edge σ (ThreeLevelWordDual.source k) 0 2 := by
  rw [columnTwo_eq_edges, smallAmplitude_eq_gain]
  simp [collisionParameter, cexp]

/-- Scaled Source collision face for the stated finite source data. -/
theorem scaledSource_collision_face (σ : Perm) (S : ℝ) (c d : ℂ)
    (Y : Operator 4) (k : Fin 6) :
    scaledSource σ S 0 c d Y k =
      faceSource σ (halfWeight S : ℂ) (gain S : ℂ) c d Y k := by
  rw [scaledSource, columnOne_collision_face, columnTwo_collision_face,
    actualGradient_collision_face]
  rfl

def compactFaceSource (σ : Perm) (G q : ℝ) (c d : ℂ) (Y : Operator 4)
    (k : Fin 6) : Operator 4 :=
  faceSource σ (G : ℂ) ((q : ℂ)*(3-(G : ℂ))/2) c d Y k

/-- Compact Face Source actual for the stated finite source data. -/
theorem compactFaceSource_actual (σ : Perm) (S : ℝ) (hs : 0 ≤ S)
    (c d : ℂ) (Y : Operator 4) (k : Fin 6) :
    compactFaceSource σ (halfWeight S) (compactAmplitude S) c d Y k =
      scaledSource σ S 0 c d Y k := by
  rw [scaledSource_collision_face, compactFaceSource]
  congr 1
  exact (smallAmplitude_eq_compact hs).symm

/-- Cube Point collision face for the stated finite source data. -/
theorem cubePoint_collision_face (S : ℝ) :
    cubePoint S 0 = ![halfWeight S,1,compactAmplitude S,1,1] := by
  funext i
  fin_cases i <;> norm_num [cubePoint, halfWeight, compactAmplitude, gain, mixedWeight]


def sourceBase (σ : Perm) (c d : ℂ) (Y : Operator 4) (k : Fin 6) : Operator 4 :=
  c • (edge σ (ThreeLevelWordDual.source k) 0 1 +
      edge σ (ThreeLevelWordDual.source k) 0 2) +
    d • edge σ (ThreeLevelWordDual.source k) 1 2 +
    faceBase σ (ThreeLevelWordDual.source k) Y

def sourceUp (σ : Perm) (d : ℂ) (Y : Operator 4) (k : Fin 6) : Operator 4 :=
  d • edge σ (ThreeLevelWordDual.source k) 0 2 +
    faceUp σ (ThreeLevelWordDual.source k) Y

def sourceDown (σ : Perm) (Y : Operator 4) (k : Fin 6) : Operator 4 :=
  faceDown σ (ThreeLevelWordDual.source k) Y

/-- Both actual population columns and all fast source terms are retained. -/
theorem faceSource_three_terms (σ : Perm) (G e c d : ℂ)
    (Y : Operator 4) (k : Fin 6) :
    faceSource σ G e c d Y k =
      sourceBase σ c d Y k + e • sourceUp σ d Y k +
        (G*e) • sourceDown σ Y k := by
  simp only [faceSource, faceGradient, sourceBase, sourceUp, sourceDown,
    smul_add, smul_smul]
  rw [mul_comm d e]
  abel

/-- Compact Face Source three terms for the stated finite source data. -/
theorem compactFaceSource_three_terms (σ : Perm) (G q : ℝ) (c d : ℂ)
    (Y : Operator 4) (k : Fin 6) :
    compactFaceSource σ G q c d Y k =
      sourceBase σ c d Y k +
      ((q : ℂ)*(3-(G : ℂ))/2) • sourceUp σ d Y k +
      ((G : ℂ)*((q : ℂ)*(3-(G : ℂ))/2)) • sourceDown σ Y k :=
  faceSource_three_terms σ _ _ c d Y k

/-- Physical face parameters for the stated finite source data. -/
theorem physical_face_parameters (S : ℝ) (hs : 0 ≤ S) :
    halfWeight S ∈ Set.Icc (0 : ℝ) 1 ∧
      compactAmplitude S ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨⟨(halfWeight_pos S).le, halfWeight_le_one hs⟩,
    ⟨(compactAmplitude_pos hs).le, compactAmplitude_le_one hs⟩⟩

open ThreeLevelCollisionFace
  (polynomialStack gramPieces coefficientWeight coefficientForm faceMatrixValue
   faceMatrixValue_sub faceMatrixValue_const faceMatrixValue_gram faceMatrixValue_posSemidef)

open ThreeLevelGramCertificateCorner ThreeLevelCoordinateMetric ThreeLevelCornerForm

abbrev literalFaceStack (G q : ℝ) : Matrix (Fin 96) (Fin 15) ℂ :=
  polynomialStack ThreeLevelHighCollisionCoefficientTables.faceBase
    ThreeLevelHighCollisionCoefficientTables.faceUp
    ThreeLevelHighCollisionCoefficientTables.faceDown G q

def literalFaceGram (G q : ℝ) : Matrix (Fin 15) (Fin 15) ℂ :=
  (literalFaceStack G q)ᴴ * literalFaceStack G q

/-- Upper Coefficient Weight eq rational for the stated finite source data. -/
theorem upperCoefficientWeight_eq_rational (t : Fin 6) (i : Fin 5) (j : Fin 3) :
    coefficientWeight t i j =
      (ThreeLevelHighCollisionCoefficientTables.upperCoefficientWeight t i j : ℝ) := by
  fin_cases t <;>
    simp [coefficientWeight, ThreeLevelHighCollisionCoefficientTables.upperCoefficientWeight] <;>
    split_ifs <;> push_cast <;> ring

/-- Gram Pieces eq literal for the stated finite source data. -/
theorem gramPieces_eq_literal :
    gramPieces ThreeLevelHighCollisionCoefficientTables.faceBase
      ThreeLevelHighCollisionCoefficientTables.faceUp ThreeLevelHighCollisionCoefficientTables.faceDown =
        ThreeLevelHighCollisionCoefficientTables.gramPiece := by
  funext t
  fin_cases t <;>
    simp [gramPieces, ThreeLevelHighCollisionCoefficientTables.gramPiece,
      ThreeLevelHighCollisionCoefficientTables.gramBB_eq,
      ThreeLevelHighCollisionCoefficientTables.gramBU_eq,
      ThreeLevelHighCollisionCoefficientTables.gramBV_eq,
      ThreeLevelHighCollisionCoefficientTables.gramUU_eq,
      ThreeLevelHighCollisionCoefficientTables.gramUV_eq,
      ThreeLevelHighCollisionCoefficientTables.gramVV_eq]

/-- Upper Coefficient Form eq literal for the stated finite source data. -/
theorem upperCoefficientForm_eq_literal (i : Fin 5) (j : Fin 3) :
    coefficientForm (gramPieces ThreeLevelHighCollisionCoefficientTables.faceBase
      ThreeLevelHighCollisionCoefficientTables.faceUp
      ThreeLevelHighCollisionCoefficientTables.faceDown) i j =
        ThreeLevelHighCollisionCoefficientTables.upperCoefficientGram i j := by
  simp only [coefficientForm, gramPieces_eq_literal, upperCoefficientWeight_eq_rational,
    ThreeLevelHighCollisionCoefficientTables.upperCoefficientGram]

/-- Lower Coefficient Weight eq rational for the stated finite source data. -/
theorem lowerCoefficientWeight_eq_rational (t : Fin 6) (i : Fin 5) (j : Fin 4) :
    ThreeLevelBernsteinElevation.coefficientWeight t i j =
      (ThreeLevelHighCollisionCoefficientTables.lowerCoefficientWeight t i j : ℝ) := by
  fin_cases t <;>
    simp [ThreeLevelBernsteinElevation.coefficientWeight,
      ThreeLevelHighCollisionCoefficientTables.lowerCoefficientWeight] <;> ring

/-- Lower Coefficient Form eq literal for the stated finite source data. -/
theorem lowerCoefficientForm_eq_literal (i : Fin 5) (j : Fin 4) :
    ThreeLevelBernsteinElevation.coefficientForm
      (gramPieces ThreeLevelHighCollisionCoefficientTables.faceBase
        ThreeLevelHighCollisionCoefficientTables.faceUp
        ThreeLevelHighCollisionCoefficientTables.faceDown) i j =
      ThreeLevelHighCollisionCoefficientTables.lowerCoefficientGram i j := by
  simp only [ThreeLevelBernsteinElevation.coefficientForm, gramPieces_eq_literal,
    lowerCoefficientWeight_eq_rational,
    ThreeLevelHighCollisionCoefficientTables.lowerCoefficientGram]

/-- The degree-(4,3) lower family reconstructs the exact full complex residual. -/
theorem lower_reconstruction (G q : ℝ) :
    ThreeLevelBernsteinElevation.faceMatrixValue
      ThreeLevelHighCollisionCertificates.lowerCoefficient G q =
      literalFaceGram G q - cornerMetric := by
  have hC : ThreeLevelHighCollisionCertificates.lowerCoefficient =
      fun i j => ThreeLevelBernsteinElevation.coefficientForm
        (gramPieces ThreeLevelHighCollisionCoefficientTables.faceBase
          ThreeLevelHighCollisionCoefficientTables.faceUp
          ThreeLevelHighCollisionCoefficientTables.faceDown) i j - cornerMetric := by
    funext i j
    rw [ThreeLevelHighCollisionCoefficientTables.lowerCoefficient_eq_gram_sub_metric,
      lowerCoefficientForm_eq_literal]
  rw [hC, ThreeLevelBernsteinElevation.faceMatrixValue_sub,
    ThreeLevelBernsteinElevation.faceMatrixValue_gram,
    ThreeLevelBernsteinElevation.faceMatrixValue_const]
  rfl

/-- Upper reconstruction for the stated finite source data. -/
theorem upper_reconstruction (G q : ℝ) :
    faceMatrixValue ThreeLevelHighCollisionCertificates.upperCoefficient G q =
      (34 : ℝ) • cornerMetric - literalFaceGram G q := by
  have hC : ThreeLevelHighCollisionCertificates.upperCoefficient =
      fun i j => (34 : ℝ) • cornerMetric - coefficientForm
        (gramPieces ThreeLevelHighCollisionCoefficientTables.faceBase
          ThreeLevelHighCollisionCoefficientTables.faceUp
          ThreeLevelHighCollisionCoefficientTables.faceDown) i j := by
    funext i j
    rw [ThreeLevelHighCollisionCoefficientTables.upperCoefficient_eq_metric_sub_gram,
      upperCoefficientForm_eq_literal]
  rw [hC, faceMatrixValue_sub, faceMatrixValue_const, faceMatrixValue_gram]
  rfl

/-- Literal Face Gram lower pos Semidef for the stated finite source data. -/
theorem literalFaceGram_lower_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (literalFaceGram G q - cornerMetric).PosSemidef := by
  rw [← lower_reconstruction]
  exact ThreeLevelBernsteinElevation.faceMatrixValue_posSemidef
    ThreeLevelHighCollisionCertificates.lowerCoefficient hG hq
    ThreeLevelHighCollisionCertificates.lowerCoefficient_posSemidef

/-- Literal Face Gram upper pos Semidef for the stated finite source data. -/
theorem literalFaceGram_upper_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ((34 : ℝ) • cornerMetric - literalFaceGram G q).PosSemidef := by
  rw [← upper_reconstruction]
  exact faceMatrixValue_posSemidef ThreeLevelHighCollisionCertificates.upperCoefficient hG hq
    ThreeLevelHighCollisionCertificates.upperCoefficient_posSemidef

/-- Source terms at zero for the stated finite source data. -/
theorem source_terms_at_zero (c d : ℂ) (Y : Operator 4) (k : Fin 6) :
    sourceBase (Equiv.refl (Fin 3)) c d Y k +
      sourceUp (Equiv.refl (Fin 3)) d Y k +
        sourceDown (Equiv.refl (Fin 3)) Y k =
      scaledSource (Equiv.refl (Fin 3)) 0 0 c d Y k := by
  rw [scaledSource_collision_face, faceSource_three_terms]
  simp [halfWeight, gain]

/-- Literal Up full Coordinates for the stated finite source data. -/
theorem literalUp_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelHighCollisionCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      sourceUp (Equiv.refl (Fin 3)) d Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelHighCollisionSourceTables.faceUp_mulVec c d Y hY a

/-- Literal Down full Coordinates for the stated finite source data. -/
theorem literalDown_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelHighCollisionCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      sourceDown (Equiv.refl (Fin 3)) Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelHighCollisionSourceTables.faceDown_mulVec c d Y hY a

/-- Literal Base full Coordinates for the stated finite source data. -/
theorem literalBase_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelHighCollisionCoefficientTables.faceBase *ᵥ fullCoordinates c d Y) a =
      sourceBase (Equiv.refl (Fin 3)) c d Y (sourceIndex a) (rowIndex a) (columnIndex a) := by
  have hsum := congrArg (fun M => (M *ᵥ fullCoordinates c d Y) a)
    ThreeLevelHighCollisionCoefficientTables.faceBase_add_up_add_down_eq_cornerStack
  simp only [Matrix.add_mulVec, Pi.add_apply] at hsum
  rw [literalUp_fullCoordinates c d Y hY a, literalDown_fullCoordinates c d Y hY a,
    cornerStack_mulVec_eq_actualGradient (Equiv.refl (Fin 3)),
    literalCombination_fullCoordinates (Equiv.refl (Fin 3)) c d Y hY,
    ← scaledSource_zero_spacings] at hsum
  have hsource := congrArg (fun X : Operator 4 => X (rowIndex a) (columnIndex a))
    (source_terms_at_zero c d Y (sourceIndex a))
  simp only [Matrix.add_apply] at hsource
  exact add_right_cancel (add_right_cancel (hsum.trans hsource.symm))

/-- The concrete polynomial stack acts as the exact scaled six-source map on
all15 complex coordinates; the full fast input is reconstructed internally. -/
theorem literalFaceStack_fullCoordinates (G q : ℝ) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (literalFaceStack G q *ᵥ fullCoordinates c d Y) a =
      compactFaceSource (Equiv.refl (Fin 3)) G q c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  simp only [literalFaceStack, polynomialStack, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, literalBase_fullCoordinates c d Y hY a,
    literalUp_fullCoordinates c d Y hY a, literalDown_fullCoordinates c d Y hY a]
  rw [compactFaceSource_three_terms]
  simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]

/-- Literal Face Stack actual for the stated finite source data. -/
theorem literalFaceStack_actual (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (literalFaceStack (halfWeight S) (compactAmplitude S) *ᵥ fullCoordinates c d Y) a =
      scaledSource (Equiv.refl (Fin 3)) S 0 c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  rw [literalFaceStack_fullCoordinates _ _ c d Y hY a, compactFaceSource_actual _ S hs]

/-- Literal Face Gram full Coordinates for the stated finite source data. -/
theorem literalFaceGram_fullCoordinates (S : ℝ) (hs : 0 ≤ S) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast (Equiv.refl (Fin 3)) Y) :
    ThreeLevelBernstein.quadratic (literalFaceGram (halfWeight S) (compactAmplitude S))
      (fullCoordinates c d Y) = stackSquare (Equiv.refl (Fin 3)) S 0 c d Y := by
  rw [literalFaceGram, quadratic_gram_eq_sum_normSq]
  simp_rw [literalFaceStack_actual S hs c d Y hY]
  exact sum_normSq_flat_source (scaledSource (Equiv.refl (Fin 3)) S 0 c d Y)

/-- An unconditional finite-temperature collision-face certificate for order012.
Both residual identities, every PSD coefficient and the actual source/metric
reconstruction have been discharged by ordinary kernel proofs. -/
theorem collision_scaledStackBounds (S : ℝ) (hs : 0 ≤ S) :
    ScaledStackBounds (Equiv.refl (Fin 3)) S 0 1 34 := by
  intro c d Y hY
  obtain ⟨hG,hq⟩ := physical_face_parameters S hs
  have hb := ThreeLevelBernstein.quadratic_bounds cornerMetric
    (literalFaceGram (halfWeight S) (compactAmplitude S)) 1 34
    (by simpa only [one_smul] using literalFaceGram_lower_posSemidef hG hq)
    (literalFaceGram_upper_posSemidef hG hq) (fullCoordinates c d Y)
  rw [cornerMetric_fullCoordinates_quadratic (Equiv.refl (Fin 3)) c d Y hY,
    literalFaceGram_fullCoordinates S hs c d Y hY] at hb
  exact hb

/-- Collision plain Energy bounds for the stated finite source data. -/
theorem collision_plainEnergy_bounds (S : ℝ) (hs : 0 ≤ S) (X : Operator 4) :
    (1/12 : ℝ) * invariantMass (Equiv.refl (Fin 3)) S 0 X ≤
        plainEnergy (Equiv.refl (Fin 3)) S 0 X ∧
      plainEnergy (Equiv.refl (Fin 3)) S 0 X ≤
        (17/6 : ℝ) * invariantMass (Equiv.refl (Fin 3)) S 0 X := by
  convert plainEnergy_bounds (Equiv.refl (Fin 3)) S 0 1 34
    (collision_scaledStackBounds S hs) X using 1
  norm_num

/-- Collision clock Energy bounds for the stated finite source data. -/
theorem collision_clockEnergy_bounds (β S : ℝ) (hs : 0 ≤ S)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    (1/12 : ℝ) * invariantMass (Equiv.refl (Fin 3)) S 0 X ≤
        clockEnergy (Equiv.refl (Fin 3)) β S 0 μ X ∧
      clockEnergy (Equiv.refl (Fin 3)) β S 0 μ X ≤
        (17/6 : ℝ) * invariantMass (Equiv.refl (Fin 3)) S 0 X := by
  convert clockEnergy_bounds (Equiv.refl (Fin 3)) β S 0 1 34
    (collision_scaledStackBounds S hs) μ X using 1
  norm_num

/-- Collision clock Energy comparison for the stated finite source data. -/
theorem collision_clockEnergy_comparison (β S : ℝ) (hs : 0 ≤ S)
    (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy (Equiv.refl (Fin 3)) β S 0 ν X ≤
      34 * clockEnergy (Equiv.refl (Fin 3)) β S 0 μ X :=
  clockEnergy_comparison_34 (Equiv.refl (Fin 3)) β S 0
    (collision_scaledStackBounds S hs) μ ν X

/-- Collision clock Energy kernel for the stated finite source data. -/
theorem collision_clockEnergy_kernel (β S : ℝ) (hs : 0 ≤ S)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy (Equiv.refl (Fin 3)) β S 0 μ X = 0 ↔
      ∃ c : ℂ, X = c • gibbsRoot (Equiv.refl (Fin 3)) (lowEnergies S 0) :=
  clockEnergy_eq_zero_iff (Equiv.refl (Fin 3)) β S 0 1 34
    (by norm_num) (collision_scaledStackBounds S hs) μ X

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionFace
