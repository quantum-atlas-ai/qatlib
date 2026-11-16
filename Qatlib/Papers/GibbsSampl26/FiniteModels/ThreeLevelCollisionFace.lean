/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionSourceTables
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
# The actual order012 collision face

The S=0 source reduction retains both Gaussian thermal legs, all six original
sources and the full15complex coordinate chart. A degree(4,2) tensor Bernstein
identity connects every residual occurrence to a concrete kernel-checked
positive coefficient. The actual source and metric bridges discharge the
scaled-stack certificate and yield the original normalized physical clock
bounds. Source formulas are permutation-uniform; this finite PSD certificate
is for order012 and makes no claim for the full five-variable cube.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionFace
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

def mergedLow (σ : Perm) : Operator 4 :=
  spectralProjectors σ 0 + spectralProjectors σ 1

def mergedHigh (σ : Perm) : Operator 4 := spectralProjectors σ 2

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

def faceQuarter (a : ℂ) : Fin 3 → ℂ := ![1,1,a]
def faceWeights (a e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,1,e*a; 1,1,e*a; e*a,e*a,1]
def faceSharpWeights (G e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,1,e; 1,1,e; G*e,G*e,1]
def faceFlatWeights (G e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,1,G*e; 1,1,G*e; e,e,1]

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
theorem actual_face_quarter (s : ℝ) :
    (fun i => quarterAmplitude (lowEnergies 0 s i)) =
      faceQuarter (quarterAmplitude s) := by
  funext i
  fin_cases i <;> simp [lowEnergies, faceQuarter, quarterAmplitude_zero]

/-- Actual face weights for the stated finite source data. -/
theorem actual_face_weights (s : ℝ) :
    gaussianWeights (lowEnergies 0 s) =
      faceWeights (quarterAmplitude s) (smallAmplitude s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaussianWeights, lowEnergies, faceWeights,
      gaussianAmplitude_zero, gaussianAmplitude_neg, small_mul_quarter]

/-- Exact two-cluster source formula for every complex input, retaining both
thermal legs and every original source channel. -/
theorem actualGradient_collision_face (σ : Perm) (s : ℝ) (k : Fin 6)
    (X : Operator 4) :
    actualGradient σ (lowEnergies 0 s) k X =
      faceGradient σ (halfWeight s : ℂ) (gain s : ℂ)
        (ThreeLevelWordDual.source k) X := by
  rw [actualGradient, actual_face_quarter, actual_face_weights,
    thermalGradient_face σ _ _ (quarterAmplitude_ne_zero s),
    quarterAmplitude_sq_eq_halfWeight, smallAmplitude_eq_gain]

def faceSource (σ : Perm) (G e c d : ℂ) (Y : Operator 4)
    (k : Fin 6) : Operator 4 :=
  c • (edge σ (ThreeLevelWordDual.source k) 0 1 +
      (G*e) • edge σ (ThreeLevelWordDual.source k) 0 2) +
  d • (edge σ (ThreeLevelWordDual.source k) 1 2 +
      edge σ (ThreeLevelWordDual.source k) 0 2) +
  faceGradient σ G e (ThreeLevelWordDual.source k) Y

/-- Column One collision face for the stated finite source data. -/
theorem columnOne_collision_face (σ : Perm) (s : ℝ) (k : Fin 6) :
    columnOne σ 0 s k =
      edge σ (ThreeLevelWordDual.source k) 0 1 +
        ((halfWeight s : ℂ)*(gain s : ℂ)) •
          edge σ (ThreeLevelWordDual.source k) 0 2 := by
  rw [columnOne_eq_edges, quarterAmplitude_sq_eq_halfWeight]
  have h : farRatio 0 s = (gain s : ℂ) := by
    simp [farRatio, cexp, gain, neg_div]
  rw [h]

/-- Column Two collision face for the stated finite source data. -/
theorem columnTwo_collision_face (σ : Perm) (s : ℝ) (k : Fin 6) :
    columnTwo σ 0 s k =
      edge σ (ThreeLevelWordDual.source k) 1 2 +
        edge σ (ThreeLevelWordDual.source k) 0 2 := by
  rw [columnTwo_eq_edges]
  simp [smallAmplitude, collisionParameter, cexp]

/-- Scaled Source collision face for the stated finite source data. -/
theorem scaledSource_collision_face (σ : Perm) (s : ℝ) (c d : ℂ)
    (Y : Operator 4) (k : Fin 6) :
    scaledSource σ 0 s c d Y k =
      faceSource σ (halfWeight s : ℂ) (gain s : ℂ) c d Y k := by
  rw [scaledSource, columnOne_collision_face, columnTwo_collision_face,
    actualGradient_collision_face]
  rfl

def compactFaceSource (σ : Perm) (G q : ℝ) (c d : ℂ) (Y : Operator 4)
    (k : Fin 6) : Operator 4 :=
  faceSource σ (G : ℂ) ((q : ℂ)*(3-(G : ℂ))/2) c d Y k

/-- Compact Face Source actual for the stated finite source data. -/
theorem compactFaceSource_actual (σ : Perm) (s : ℝ) (hs : 0 ≤ s)
    (c d : ℂ) (Y : Operator 4) (k : Fin 6) :
    compactFaceSource σ (halfWeight s) (compactAmplitude s) c d Y k =
      scaledSource σ 0 s c d Y k := by
  rw [scaledSource_collision_face, compactFaceSource]
  congr 1
  exact (smallAmplitude_eq_compact hs).symm

/-- Cube Point collision face for the stated finite source data. -/
theorem cubePoint_collision_face (s : ℝ) :
    cubePoint 0 s = ![1,halfWeight s,1,compactAmplitude s,1] := by
  funext i
  fin_cases i <;> norm_num [cubePoint, halfWeight, compactAmplitude, gain, mixedWeight]


def sourceBase (σ : Perm) (c d : ℂ) (Y : Operator 4) (k : Fin 6) : Operator 4 :=
  c • edge σ (ThreeLevelWordDual.source k) 0 1 +
    d • (edge σ (ThreeLevelWordDual.source k) 1 2 +
      edge σ (ThreeLevelWordDual.source k) 0 2) +
    faceBase σ (ThreeLevelWordDual.source k) Y

def sourceUp (σ : Perm) (Y : Operator 4) (k : Fin 6) : Operator 4 :=
  faceUp σ (ThreeLevelWordDual.source k) Y

def sourceDown (σ : Perm) (c : ℂ) (Y : Operator 4) (k : Fin 6) : Operator 4 :=
  c • edge σ (ThreeLevelWordDual.source k) 0 2 +
    faceDown σ (ThreeLevelWordDual.source k) Y

/-- The entire collision-face source has only three fixed operator terms;
the two scalar amplitudes are e and G*e. -/
theorem faceSource_three_terms (σ : Perm) (G e c d : ℂ)
    (Y : Operator 4) (k : Fin 6) :
    faceSource σ G e c d Y k =
      sourceBase σ c d Y k + e • sourceUp σ Y k +
        (G*e) • sourceDown σ c Y k := by
  simp only [faceSource, faceGradient, sourceBase, sourceUp, sourceDown,
    smul_add, smul_smul]
  rw [mul_comm c (G*e)]
  abel

/-- Compact Face Source three terms for the stated finite source data. -/
theorem compactFaceSource_three_terms (σ : Perm) (G q : ℝ) (c d : ℂ)
    (Y : Operator 4) (k : Fin 6) :
    compactFaceSource σ G q c d Y k =
      sourceBase σ c d Y k +
      ((q : ℂ)*(3-(G : ℂ))/2) • sourceUp σ Y k +
      ((G : ℂ)*((q : ℂ)*(3-(G : ℂ))/2)) • sourceDown σ c Y k :=
  faceSource_three_terms σ _ _ c d Y k

/-- Physical face parameters for the stated finite source data. -/
theorem physical_face_parameters (s : ℝ) (hs : 0 ≤ s) :
    halfWeight s ∈ Set.Icc (0 : ℝ) 1 ∧
      compactAmplitude s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨⟨(halfWeight_pos s).le, halfWeight_le_one hs⟩,
    ⟨(compactAmplitude_pos hs).le, compactAmplitude_le_one hs⟩⟩


def faceWeight (i : Fin 5) (j : Fin 3) (G q : ℝ) : ℝ :=
  ThreeLevelBernstein.univariateWeight 4 i G *
    ThreeLevelBernstein.univariateWeight 2 j q

def coefficientWeight (t : Fin 6) (i : Fin 5) (j : Fin 3) : ℝ :=
  ![1,
    (j : ℝ)*(12-(i : ℝ))/16,
    (j : ℝ)*(i : ℝ)*(10-(i : ℝ))/48,
    if j = 2 then ((i : ℝ)^2-19*(i : ℝ)+108)/48 else 0,
    if j = 2 then ((i : ℝ)^3-15*(i : ℝ)^2+68*(i : ℝ))/96 else 0,
    if j = 2 then (i : ℝ)*((i : ℝ)-1)*((i : ℝ)^2-11*(i : ℝ)+36)/96 else 0] t

def polynomialWeight (t : Fin 6) (G q : ℝ) : ℝ :=
  let e := q*(3-G)/2
  ![1,e,G*e,e^2,G*e^2,G^2*e^2] t

/-- Coefficient Weight reconstruction for the stated finite source data. -/
theorem coefficientWeight_reconstruction (t : Fin 6) (G q : ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 3, faceWeight i j G q * coefficientWeight t i j) =
      polynomialWeight t G q := by
  fin_cases t <;>
    norm_num [faceWeight, coefficientWeight, polynomialWeight,
      ThreeLevelBernstein.univariateWeight, Fin.sum_univ_succ, Nat.choose] <;> ring

/-- Face Weight nonneg for the stated finite source data. -/
theorem faceWeight_nonneg (i : Fin 5) (j : Fin 3) {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ faceWeight i j G q :=
  mul_nonneg (ThreeLevelBernstein.univariateWeight_nonneg 4 i hG)
    (ThreeLevelBernstein.univariateWeight_nonneg 2 j hq)

/-- Face Weight sum for the stated finite source data. -/
theorem faceWeight_sum (G q : ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 3, faceWeight i j G q) = 1 := by
  simpa [coefficientWeight, polynomialWeight] using
    coefficientWeight_reconstruction 0 G q

variable {n : Type*}

def faceMatrixValue (C : Fin 5 → Fin 3 → Matrix n n ℂ) (G q : ℝ) :
    Matrix n n ℂ := ∑ i, ∑ j, faceWeight i j G q • C i j

def coefficientForm (H : Fin 6 → Matrix n n ℂ) (i : Fin 5) (j : Fin 3) :
    Matrix n n ℂ := ∑ t, coefficientWeight t i j • H t

/-- Face Matrix Value coefficient Form for the stated finite source data. -/
theorem faceMatrixValue_coefficientForm (H : Fin 6 → Matrix n n ℂ) (G q : ℝ) :
    faceMatrixValue (coefficientForm H) G q =
      ∑ t, polynomialWeight t G q • H t := by
  simp only [faceMatrixValue, coefficientForm, Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i : Fin 5, ∑ t : Fin 6, ∑ j : Fin 3,
        (faceWeight i j G q * coefficientWeight t i j) • H t := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ t : Fin 6, ∑ i : Fin 5, ∑ j : Fin 3,
        (faceWeight i j G q * coefficientWeight t i j) • H t :=
      Finset.sum_comm
    _ = ∑ t : Fin 6,
        (∑ i : Fin 5, ∑ j : Fin 3,
          faceWeight i j G q * coefficientWeight t i j) • H t := by
      simp only [Finset.sum_smul]
    _ = _ := by simp only [coefficientWeight_reconstruction]

/-- Face Matrix Value const for the stated finite source data. -/
theorem faceMatrixValue_const (M : Matrix n n ℂ) (G q : ℝ) :
    faceMatrixValue (fun _ _ => M) G q = M := by
  simp only [faceMatrixValue, ← Finset.sum_smul, faceWeight_sum, one_smul]

/-- Face Matrix Value sub for the stated finite source data. -/
theorem faceMatrixValue_sub (C D : Fin 5 → Fin 3 → Matrix n n ℂ) (G q : ℝ) :
    faceMatrixValue (fun i j => C i j - D i j) G q =
      faceMatrixValue C G q - faceMatrixValue D G q := by
  simp only [faceMatrixValue, smul_sub, Finset.sum_sub_distrib]

/-- Face Matrix Value pos Semidef for the stated finite source data. -/
theorem faceMatrixValue_posSemidef (C : Fin 5 → Fin 3 → Matrix n n ℂ)
    {G q : ℝ} (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ i j, (C i j).PosSemidef) :
    (faceMatrixValue C G q).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_sum _ fun j _ =>
    (hC i j).smul (faceWeight_nonneg i j hG hq)

variable {m : Type*} [Fintype m]

def gramPieces (B U V : Matrix m n ℂ) : Fin 6 → Matrix n n ℂ :=
  ![Bᴴ*B, Bᴴ*U+Uᴴ*B, Bᴴ*V+Vᴴ*B, Uᴴ*U, Uᴴ*V+Vᴴ*U, Vᴴ*V]

def polynomialStack (B U V : Matrix m n ℂ) (G q : ℝ) : Matrix m n ℂ :=
  B + (q*(3-G)/2) • U + (G*(q*(3-G)/2)) • V

/-- Polynomial Stack gram for the stated finite source data. -/
theorem polynomialStack_gram (B U V : Matrix m n ℂ) (G q : ℝ) :
    (polynomialStack B U V G q)ᴴ * polynomialStack B U V G q =
      ∑ t, polynomialWeight t G q • gramPieces B U V t := by
  simp [polynomialStack, polynomialWeight, gramPieces, Fin.sum_univ_succ,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
  module

/-- Face Matrix Value gram for the stated finite source data. -/
theorem faceMatrixValue_gram (B U V : Matrix m n ℂ) (G q : ℝ) :
    faceMatrixValue (coefficientForm (gramPieces B U V)) G q =
      (polynomialStack B U V G q)ᴴ * polynomialStack B U V G q := by
  rw [faceMatrixValue_coefficientForm, polynomialStack_gram]


open ThreeLevelGramCertificateCorner ThreeLevelCoordinateMetric ThreeLevelCornerForm

abbrev literalFaceStack (G q : ℝ) : Matrix (Fin 96) (Fin 15) ℂ :=
  polynomialStack ThreeLevelCollisionCoefficientTables.faceBase
    ThreeLevelCollisionCoefficientTables.faceUp
    ThreeLevelCollisionCoefficientTables.faceDown G q

def literalFaceGram (G q : ℝ) : Matrix (Fin 15) (Fin 15) ℂ :=
  (literalFaceStack G q)ᴴ * literalFaceStack G q

/-- Coefficient Weight eq rational for the stated finite source data. -/
theorem coefficientWeight_eq_rational (t : Fin 6) (i : Fin 5) (j : Fin 3) :
    coefficientWeight t i j =
      (ThreeLevelCollisionCoefficientTables.coefficientWeight t i j : ℝ) := by
  fin_cases t <;>
    simp [coefficientWeight, ThreeLevelCollisionCoefficientTables.coefficientWeight] <;>
    split_ifs <;> push_cast <;> ring

/-- Gram Pieces eq literal for the stated finite source data. -/
theorem gramPieces_eq_literal :
    gramPieces ThreeLevelCollisionCoefficientTables.faceBase
      ThreeLevelCollisionCoefficientTables.faceUp ThreeLevelCollisionCoefficientTables.faceDown =
        ThreeLevelCollisionCoefficientTables.gramPiece := by
  funext t
  fin_cases t <;>
    simp [gramPieces, ThreeLevelCollisionCoefficientTables.gramPiece,
      ThreeLevelCollisionCoefficientTables.gramBB_eq,
      ThreeLevelCollisionCoefficientTables.gramBU_eq,
      ThreeLevelCollisionCoefficientTables.gramBV_eq,
      ThreeLevelCollisionCoefficientTables.gramUU_eq,
      ThreeLevelCollisionCoefficientTables.gramUV_eq,
      ThreeLevelCollisionCoefficientTables.gramVV_eq]

/-- Coefficient Form eq literal for the stated finite source data. -/
theorem coefficientForm_eq_literal (i : Fin 5) (j : Fin 3) :
    coefficientForm (gramPieces ThreeLevelCollisionCoefficientTables.faceBase
      ThreeLevelCollisionCoefficientTables.faceUp
      ThreeLevelCollisionCoefficientTables.faceDown) i j =
        ThreeLevelCollisionCoefficientTables.coefficientGram i j := by
  simp only [coefficientForm, gramPieces_eq_literal, coefficientWeight_eq_rational,
    ThreeLevelCollisionCoefficientTables.coefficientGram]

/-- Every lower residual coefficient is the previously checked concrete
Gaussian-rational matrix, with the exact six-product incidence discharged. -/
theorem lower_reconstruction (G q : ℝ) :
    faceMatrixValue ThreeLevelCollisionCertificates.lowerCoefficient G q =
      literalFaceGram G q - cornerMetric := by
  have hC : ThreeLevelCollisionCertificates.lowerCoefficient =
      fun i j => coefficientForm
        (gramPieces ThreeLevelCollisionCoefficientTables.faceBase
          ThreeLevelCollisionCoefficientTables.faceUp
          ThreeLevelCollisionCoefficientTables.faceDown) i j - cornerMetric := by
    funext i j
    rw [ThreeLevelCollisionCoefficientTables.lowerCoefficient_eq_gram_sub_metric,
      coefficientForm_eq_literal]
  rw [hC, faceMatrixValue_sub, faceMatrixValue_gram, faceMatrixValue_const]
  rfl

/-- Upper reconstruction for the stated finite source data. -/
theorem upper_reconstruction (G q : ℝ) :
    faceMatrixValue ThreeLevelCollisionCertificates.upperCoefficient G q =
      (34 : ℝ) • cornerMetric - literalFaceGram G q := by
  have hC : ThreeLevelCollisionCertificates.upperCoefficient =
      fun i j => (34 : ℝ) • cornerMetric - coefficientForm
        (gramPieces ThreeLevelCollisionCoefficientTables.faceBase
          ThreeLevelCollisionCoefficientTables.faceUp
          ThreeLevelCollisionCoefficientTables.faceDown) i j := by
    funext i j
    rw [ThreeLevelCollisionCoefficientTables.upperCoefficient_eq_metric_sub_gram,
      coefficientForm_eq_literal]
  rw [hC, faceMatrixValue_sub, faceMatrixValue_const, faceMatrixValue_gram]
  rfl

/-- Literal Face Gram lower pos Semidef for the stated finite source data. -/
theorem literalFaceGram_lower_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (literalFaceGram G q - cornerMetric).PosSemidef := by
  rw [← lower_reconstruction]
  exact faceMatrixValue_posSemidef ThreeLevelCollisionCertificates.lowerCoefficient hG hq
    ThreeLevelCollisionCertificates.lowerCoefficient_posSemidef

/-- Literal Face Gram upper pos Semidef for the stated finite source data. -/
theorem literalFaceGram_upper_posSemidef {G q : ℝ}
    (hG : G ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ((34 : ℝ) • cornerMetric - literalFaceGram G q).PosSemidef := by
  rw [← upper_reconstruction]
  exact faceMatrixValue_posSemidef ThreeLevelCollisionCertificates.upperCoefficient hG hq
    ThreeLevelCollisionCertificates.upperCoefficient_posSemidef

/-- Source terms at zero for the stated finite source data. -/
theorem source_terms_at_zero (c d : ℂ) (Y : Operator 4) (k : Fin 6) :
    sourceBase (Equiv.refl (Fin 3)) c d Y k +
      sourceUp (Equiv.refl (Fin 3)) Y k +
        sourceDown (Equiv.refl (Fin 3)) c Y k =
      scaledSource (Equiv.refl (Fin 3)) 0 0 c d Y k := by
  rw [scaledSource_collision_face, faceSource_three_terms]
  simp [halfWeight, gain]

/-- Literal Up full Coordinates for the stated finite source data. -/
theorem literalUp_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelCollisionCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      sourceUp (Equiv.refl (Fin 3)) Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelCollisionSourceTables.faceUp_mulVec c d Y hY a

/-- Literal Down full Coordinates for the stated finite source data. -/
theorem literalDown_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelCollisionCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      sourceDown (Equiv.refl (Fin 3)) c Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  ThreeLevelCollisionSourceTables.faceDown_mulVec c d Y hY a

/-- Literal Base full Coordinates for the stated finite source data. -/
theorem literalBase_fullCoordinates (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelCollisionCoefficientTables.faceBase *ᵥ fullCoordinates c d Y) a =
      sourceBase (Equiv.refl (Fin 3)) c d Y (sourceIndex a) (rowIndex a) (columnIndex a) := by
  have hsum := congrArg (fun M => (M *ᵥ fullCoordinates c d Y) a)
    ThreeLevelCollisionCoefficientTables.faceBase_add_up_add_down_eq_cornerStack
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
theorem literalFaceStack_actual (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (literalFaceStack (halfWeight s) (compactAmplitude s) *ᵥ fullCoordinates c d Y) a =
      scaledSource (Equiv.refl (Fin 3)) 0 s c d Y
        (sourceIndex a) (rowIndex a) (columnIndex a) := by
  rw [literalFaceStack_fullCoordinates _ _ c d Y hY a, compactFaceSource_actual _ s hs]

/-- Literal Face Gram full Coordinates for the stated finite source data. -/
theorem literalFaceGram_fullCoordinates (s : ℝ) (hs : 0 ≤ s) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast (Equiv.refl (Fin 3)) Y) :
    ThreeLevelBernstein.quadratic (literalFaceGram (halfWeight s) (compactAmplitude s))
      (fullCoordinates c d Y) = stackSquare (Equiv.refl (Fin 3)) 0 s c d Y := by
  rw [literalFaceGram, quadratic_gram_eq_sum_normSq]
  simp_rw [literalFaceStack_actual s hs c d Y hY]
  exact sum_normSq_flat_source (scaledSource (Equiv.refl (Fin 3)) 0 s c d Y)

/-- An unconditional finite-temperature collision-face certificate for order012.
Both residual identities, every PSD coefficient and the actual source/metric
reconstruction have been discharged by ordinary kernel proofs. -/
theorem collision_scaledStackBounds (s : ℝ) (hs : 0 ≤ s) :
    ScaledStackBounds (Equiv.refl (Fin 3)) 0 s 1 34 := by
  intro c d Y hY
  obtain ⟨hG,hq⟩ := physical_face_parameters s hs
  have hb := ThreeLevelBernstein.quadratic_bounds cornerMetric
    (literalFaceGram (halfWeight s) (compactAmplitude s)) 1 34
    (by simpa only [one_smul] using literalFaceGram_lower_posSemidef hG hq)
    (literalFaceGram_upper_posSemidef hG hq) (fullCoordinates c d Y)
  rw [cornerMetric_fullCoordinates_quadratic (Equiv.refl (Fin 3)) c d Y hY,
    literalFaceGram_fullCoordinates s hs c d Y hY] at hb
  exact hb

/-- Collision plain Energy bounds for the stated finite source data. -/
theorem collision_plainEnergy_bounds (s : ℝ) (hs : 0 ≤ s) (X : Operator 4) :
    (1/12 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 s X ≤
        plainEnergy (Equiv.refl (Fin 3)) 0 s X ∧
      plainEnergy (Equiv.refl (Fin 3)) 0 s X ≤
        (17/6 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 s X := by
  convert plainEnergy_bounds (Equiv.refl (Fin 3)) 0 s 1 34
    (collision_scaledStackBounds s hs) X using 1
  norm_num

/-- Collision clock Energy bounds for the stated finite source data. -/
theorem collision_clockEnergy_bounds (β s : ℝ) (hs : 0 ≤ s)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    (1/12 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 s X ≤
        clockEnergy (Equiv.refl (Fin 3)) β 0 s μ X ∧
      clockEnergy (Equiv.refl (Fin 3)) β 0 s μ X ≤
        (17/6 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 s X := by
  convert clockEnergy_bounds (Equiv.refl (Fin 3)) β 0 s 1 34
    (collision_scaledStackBounds s hs) μ X using 1
  norm_num

/-- Collision clock Energy comparison for the stated finite source data. -/
theorem collision_clockEnergy_comparison (β s : ℝ) (hs : 0 ≤ s)
    (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy (Equiv.refl (Fin 3)) β 0 s ν X ≤
      34 * clockEnergy (Equiv.refl (Fin 3)) β 0 s μ X :=
  clockEnergy_comparison_34 (Equiv.refl (Fin 3)) β 0 s
    (collision_scaledStackBounds s hs) μ ν X

/-- Collision clock Energy kernel for the stated finite source data. -/
theorem collision_clockEnergy_kernel (β s : ℝ) (hs : 0 ≤ s)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy (Equiv.refl (Fin 3)) β 0 s μ X = 0 ↔
      ∃ c : ℂ, X = c • gibbsRoot (Equiv.refl (Fin 3)) (lowEnergies 0 s) :=
  clockEnergy_eq_zero_iff (Equiv.refl (Fin 3)) β 0 s 1 34
    (by norm_num) (collision_scaledStackBounds s hs) μ X

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionFace
