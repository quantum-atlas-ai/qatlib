/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionFace

@[expose] public section


/-!
# Bernstein elevation for the high-cluster collision face

The high-cluster lower certificate uses degree (4,3), whereas the actual
six-product Gram polynomial already has degree (4,2). This module proves the
degree-(4,3) reconstruction and its exact relation to degree-(4,2) coefficients.
The full complex matrix and its arbitrary complex quadratic inputs are retained.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinElevation
open ThreeLevelCollisionFace (polynomialWeight gramPieces polynomialStack)

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

def faceWeight (i : Fin 5) (j : Fin 4) (A p : ℝ) : ℝ :=
  ThreeLevelBernstein.univariateWeight 4 i A *
    ThreeLevelBernstein.univariateWeight 3 j p

def coefficientWeight (t : Fin 6) (i : Fin 5) (j : Fin 4) : ℝ :=
  ![1,
    (j : ℝ)*(12-(i : ℝ))/24,
    (j : ℝ)*(i : ℝ)*(10-(i : ℝ))/72,
    (j : ℝ)*((j : ℝ)-1)*((i : ℝ)^2-19*(i : ℝ)+108)/288,
    (j : ℝ)*((j : ℝ)-1)*((i : ℝ)^3-15*(i : ℝ)^2+68*(i : ℝ))/576,
    (j : ℝ)*((j : ℝ)-1)*(i : ℝ)*((i : ℝ)-1)*
      ((i : ℝ)^2-11*(i : ℝ)+36)/576] t

/-- Coefficient Weight reconstruction for the stated finite source data. -/
theorem coefficientWeight_reconstruction (t : Fin 6) (A p : ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 4, faceWeight i j A p * coefficientWeight t i j) =
      polynomialWeight t A p := by
  fin_cases t <;>
    norm_num [faceWeight, coefficientWeight, polynomialWeight,
      ThreeLevelBernstein.univariateWeight, Fin.sum_univ_succ, Nat.choose] <;> ring

/-- Face Weight nonneg for the stated finite source data. -/
theorem faceWeight_nonneg (i : Fin 5) (j : Fin 4) {A p : ℝ}
    (hA : A ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ faceWeight i j A p :=
  mul_nonneg (ThreeLevelBernstein.univariateWeight_nonneg 4 i hA)
    (ThreeLevelBernstein.univariateWeight_nonneg 3 j hp)

/-- Face Weight sum for the stated finite source data. -/
theorem faceWeight_sum (A p : ℝ) :
    (∑ i : Fin 5, ∑ j : Fin 4, faceWeight i j A p) = 1 := by
  simpa [coefficientWeight, polynomialWeight] using
    coefficientWeight_reconstruction 0 A p

variable {n : Type*}

def faceMatrixValue (C : Fin 5 → Fin 4 → Matrix n n ℂ) (A p : ℝ) :
    Matrix n n ℂ := ∑ i, ∑ j, faceWeight i j A p • C i j

def coefficientForm (H : Fin 6 → Matrix n n ℂ) (i : Fin 5) (j : Fin 4) :
    Matrix n n ℂ := ∑ t, coefficientWeight t i j • H t

/-- Face Matrix Value coefficient Form for the stated finite source data. -/
theorem faceMatrixValue_coefficientForm (H : Fin 6 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (coefficientForm H) A p =
      ∑ t, polynomialWeight t A p • H t := by
  simp only [faceMatrixValue, coefficientForm, Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i : Fin 5, ∑ t : Fin 6, ∑ j : Fin 4,
        (faceWeight i j A p * coefficientWeight t i j) • H t := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ t : Fin 6, ∑ i : Fin 5, ∑ j : Fin 4,
        (faceWeight i j A p * coefficientWeight t i j) • H t :=
      Finset.sum_comm
    _ = ∑ t : Fin 6,
        (∑ i : Fin 5, ∑ j : Fin 4,
          faceWeight i j A p * coefficientWeight t i j) • H t := by
      simp only [Finset.sum_smul]
    _ = _ := by simp only [coefficientWeight_reconstruction]

/-- Face Matrix Value const for the stated finite source data. -/
theorem faceMatrixValue_const (M : Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (fun _ _ => M) A p = M := by
  simp only [faceMatrixValue, ← Finset.sum_smul, faceWeight_sum, one_smul]

/-- Face Matrix Value sub for the stated finite source data. -/
theorem faceMatrixValue_sub (C D : Fin 5 → Fin 4 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (fun i j => C i j - D i j) A p =
      faceMatrixValue C A p - faceMatrixValue D A p := by
  simp only [faceMatrixValue, smul_sub, Finset.sum_sub_distrib]

/-- Face Matrix Value pos Semidef for the stated finite source data. -/
theorem faceMatrixValue_posSemidef (C : Fin 5 → Fin 4 → Matrix n n ℂ)
    {A p : ℝ} (hA : A ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ i j, (C i j).PosSemidef) :
    (faceMatrixValue C A p).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_sum _ fun j _ =>
    (hC i j).smul (faceWeight_nonneg i j hA hp)

variable {m : Type*} [Fintype m]

/-- Face Matrix Value gram for the stated finite source data. -/
theorem faceMatrixValue_gram (B U V : Matrix m n ℂ) (A p : ℝ) :
    faceMatrixValue (coefficientForm (gramPieces B U V)) A p =
      (polynomialStack B U V A p)ᴴ * polynomialStack B U V A p := by
  rw [faceMatrixValue_coefficientForm, ThreeLevelCollisionFace.polynomialStack_gram]

/-- Exact degree-two to degree-three elevation in the second variable. -/
def elevateCoefficients (C : Fin 5 → Fin 3 → Matrix n n ℂ)
    (i : Fin 5) (j : Fin 4) : Matrix n n ℂ :=
  ![C i 0,
    (1/3 : ℝ) • C i 0 + (2/3 : ℝ) • C i 1,
    (2/3 : ℝ) • C i 1 + (1/3 : ℝ) • C i 2,
    C i 2] j

/-- Elevate Coefficients pos Semidef for the stated finite source data. -/
theorem elevateCoefficients_posSemidef (C : Fin 5 → Fin 3 → Matrix n n ℂ)
    (hC : ∀ i j, (C i j).PosSemidef) (i : Fin 5) (j : Fin 4) :
    (elevateCoefficients C i j).PosSemidef := by
  fin_cases j
  · exact hC i 0
  · exact ((hC i 0).smul (by norm_num : (0 : ℝ) ≤ 1/3)).add
      ((hC i 1).smul (by norm_num : (0 : ℝ) ≤ 2/3))
  · exact ((hC i 1).smul (by norm_num : (0 : ℝ) ≤ 2/3)).add
      ((hC i 2).smul (by norm_num : (0 : ℝ) ≤ 1/3))
  · exact hC i 2

/-- Face Matrix Value elevate Coefficients for the stated finite source data. -/
theorem faceMatrixValue_elevateCoefficients
    (C : Fin 5 → Fin 3 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (elevateCoefficients C) A p =
      ThreeLevelCollisionFace.faceMatrixValue C A p := by
  simp only [faceMatrixValue, ThreeLevelCollisionFace.faceMatrixValue]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [faceWeight, ThreeLevelCollisionFace.faceWeight,
    elevateCoefficients, ThreeLevelBernstein.univariateWeight,
    Fin.sum_univ_succ, Nat.choose]
  module

/-- Coefficient Form eq elevate Coefficients for the stated finite source data. -/
theorem coefficientForm_eq_elevateCoefficients
    (H : Fin 6 → Matrix n n ℂ) :
    coefficientForm H =
      elevateCoefficients (ThreeLevelCollisionFace.coefficientForm H) := by
  funext i j
  fin_cases j <;>
    simp [coefficientForm, elevateCoefficients, ThreeLevelCollisionFace.coefficientForm,
      coefficientWeight, ThreeLevelCollisionFace.coefficientWeight,
      Fin.sum_univ_succ] <;> module


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinElevation
