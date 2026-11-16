/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinElevation

@[expose] public section


/-!
# Exact first-axis elevation for the remaining collision certificates

The remaining low120 finite family uses degree (6,3). Its actual source Gram
polynomial is already represented at degree (4,2). This module raises the first
axis from four to six and composes it with the existing second-axis elevation.
All identities retain the full complex matrices and arbitrary complex inputs.
No positivity of the remaining low120 coefficient family is asserted here.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinFirstElevation
open ThreeLevelCollisionFace (polynomialWeight gramPieces polynomialStack)

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

/-- Exact rational convex weights for degree four to degree six. -/
def elevationWeight : Matrix (Fin 7) (Fin 5) ℚ :=
  !![1,0,0,0,0;
     1/3,2/3,0,0,0;
     1/15,8/15,2/5,0,0;
     0,1/5,3/5,1/5,0;
     0,0,2/5,8/15,1/15;
     0,0,0,2/3,1/3;
     0,0,0,0,1]

/-- Elevation Weight nonneg for the stated finite source data. -/
theorem elevationWeight_nonneg (i : Fin 7) (k : Fin 5) :
    (0 : ℝ) ≤ (elevationWeight i k : ℝ) := by
  fin_cases i <;> fin_cases k <;> norm_num [elevationWeight]

/-- Elevation Weight sum for the stated finite source data. -/
theorem elevationWeight_sum (i : Fin 7) :
    (∑ k : Fin 5, (elevationWeight i k : ℝ)) = 1 := by
  fin_cases i <;> norm_num [elevationWeight, Fin.sum_univ_succ]

/-- Univariate reconstruction for the stated finite source data. -/
theorem univariate_reconstruction (k : Fin 5) (A : ℝ) :
    (∑ i : Fin 7, ThreeLevelBernstein.univariateWeight 6 i A *
      (elevationWeight i k : ℝ)) = ThreeLevelBernstein.univariateWeight 4 k A := by
  fin_cases k <;>
    norm_num [ThreeLevelBernstein.univariateWeight, elevationWeight,
      Fin.sum_univ_succ, Nat.choose] <;> ring

def faceWeight (i : Fin 7) (j : Fin 4) (A p : ℝ) : ℝ :=
  ThreeLevelBernstein.univariateWeight 6 i A *
    ThreeLevelBernstein.univariateWeight 3 j p

/-- Face Weight nonneg for the stated finite source data. -/
theorem faceWeight_nonneg (i : Fin 7) (j : Fin 4) {A p : ℝ}
    (hA : A ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ faceWeight i j A p :=
  mul_nonneg (ThreeLevelBernstein.univariateWeight_nonneg 6 i hA)
    (ThreeLevelBernstein.univariateWeight_nonneg 3 j hp)

/-- Face Weight sum for the stated finite source data. -/
theorem faceWeight_sum (A p : ℝ) :
    (∑ i : Fin 7, ∑ j : Fin 4, faceWeight i j A p) = 1 := by
  norm_num [faceWeight, ThreeLevelBernstein.univariateWeight,
    Fin.sum_univ_succ, Nat.choose]
  ring

variable {n : Type*}

def faceMatrixValue (C : Fin 7 → Fin 4 → Matrix n n ℂ) (A p : ℝ) :
    Matrix n n ℂ := ∑ i, ∑ j, faceWeight i j A p • C i j

def elevateCoefficients (C : Fin 5 → Fin 4 → Matrix n n ℂ)
    (i : Fin 7) (j : Fin 4) : Matrix n n ℂ :=
  ∑ k : Fin 5, (elevationWeight i k : ℝ) • C k j

/-- Elevate Coefficients pos Semidef for the stated finite source data. -/
theorem elevateCoefficients_posSemidef (C : Fin 5 → Fin 4 → Matrix n n ℂ)
    (hC : ∀ k j, (C k j).PosSemidef) (i : Fin 7) (j : Fin 4) :
    (elevateCoefficients C i j).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => (hC k j).smul (elevationWeight_nonneg i k)

/-- Face Matrix Value elevate Coefficients for the stated finite source data. -/
theorem faceMatrixValue_elevateCoefficients
    (C : Fin 5 → Fin 4 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (elevateCoefficients C) A p =
      ThreeLevelBernsteinElevation.faceMatrixValue C A p := by
  simp only [faceMatrixValue, elevateCoefficients, Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i : Fin 7, ∑ k : Fin 5, ∑ j : Fin 4,
        (faceWeight i j A p * (elevationWeight i k : ℝ)) • C k j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k : Fin 5, ∑ i : Fin 7, ∑ j : Fin 4,
        (faceWeight i j A p * (elevationWeight i k : ℝ)) • C k j :=
      Finset.sum_comm
    _ = ∑ k : Fin 5, ∑ j : Fin 4, ∑ i : Fin 7,
        (faceWeight i j A p * (elevationWeight i k : ℝ)) • C k j := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ k : Fin 5, ∑ j : Fin 4,
        ThreeLevelBernsteinElevation.faceWeight k j A p • C k j := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_smul]
      congr 1
      simp only [faceWeight, ThreeLevelBernsteinElevation.faceWeight]
      calc
        _ = (∑ i : Fin 7, ThreeLevelBernstein.univariateWeight 6 i A *
            (elevationWeight i k : ℝ)) *
              ThreeLevelBernstein.univariateWeight 3 j p := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [univariate_reconstruction]
    _ = _ := rfl

/-- Face Matrix Value const for the stated finite source data. -/
theorem faceMatrixValue_const (M : Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (fun _ _ => M) A p = M := by
  simp only [faceMatrixValue, ← Finset.sum_smul, faceWeight_sum, one_smul]

/-- Face Matrix Value sub for the stated finite source data. -/
theorem faceMatrixValue_sub (C D : Fin 7 → Fin 4 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (fun i j => C i j - D i j) A p =
      faceMatrixValue C A p - faceMatrixValue D A p := by
  simp only [faceMatrixValue, smul_sub, Finset.sum_sub_distrib]

/-- Face Matrix Value pos Semidef for the stated finite source data. -/
theorem faceMatrixValue_posSemidef (C : Fin 7 → Fin 4 → Matrix n n ℂ)
    {A p : ℝ} (hA : A ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ i j, (C i j).PosSemidef) :
    (faceMatrixValue C A p).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_sum _ fun j _ =>
    (hC i j).smul (faceWeight_nonneg i j hA hp)

def coefficientWeight (t : Fin 6) (i : Fin 7) (j : Fin 4) : ℝ :=
  ∑ k : Fin 5, (elevationWeight i k : ℝ) *
    ThreeLevelBernsteinElevation.coefficientWeight t k j

def coefficientForm (H : Fin 6 → Matrix n n ℂ) (i : Fin 7) (j : Fin 4) :
    Matrix n n ℂ := ∑ t, coefficientWeight t i j • H t

/-- Coefficient Form eq elevate Coefficients for the stated finite source data. -/
theorem coefficientForm_eq_elevateCoefficients (H : Fin 6 → Matrix n n ℂ) :
    coefficientForm H =
      elevateCoefficients (ThreeLevelBernsteinElevation.coefficientForm H) := by
  funext i j
  simp only [coefficientForm, coefficientWeight, Finset.sum_smul, elevateCoefficients,
    ThreeLevelBernsteinElevation.coefficientForm, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- Face Matrix Value coefficient Form for the stated finite source data. -/
theorem faceMatrixValue_coefficientForm (H : Fin 6 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (coefficientForm H) A p =
      ∑ t, polynomialWeight t A p • H t := by
  rw [coefficientForm_eq_elevateCoefficients, faceMatrixValue_elevateCoefficients,
    ThreeLevelBernsteinElevation.faceMatrixValue_coefficientForm]

/-- Composition raises the original (4,2) coefficient grid to (6,3). -/
def elevateBoth (C : Fin 5 → Fin 3 → Matrix n n ℂ) :
    Fin 7 → Fin 4 → Matrix n n ℂ :=
  elevateCoefficients (ThreeLevelBernsteinElevation.elevateCoefficients C)

/-- Face Matrix Value elevate Both for the stated finite source data. -/
theorem faceMatrixValue_elevateBoth
    (C : Fin 5 → Fin 3 → Matrix n n ℂ) (A p : ℝ) :
    faceMatrixValue (elevateBoth C) A p = ThreeLevelCollisionFace.faceMatrixValue C A p := by
  rw [elevateBoth, faceMatrixValue_elevateCoefficients,
    ThreeLevelBernsteinElevation.faceMatrixValue_elevateCoefficients]

/-- Elevate Both pos Semidef for the stated finite source data. -/
theorem elevateBoth_posSemidef (C : Fin 5 → Fin 3 → Matrix n n ℂ)
    (hC : ∀ i j, (C i j).PosSemidef) (i : Fin 7) (j : Fin 4) :
    (elevateBoth C i j).PosSemidef :=
  elevateCoefficients_posSemidef _
    (ThreeLevelBernsteinElevation.elevateCoefficients_posSemidef C hC) i j

/-- Coefficient Form eq elevate Both for the stated finite source data. -/
theorem coefficientForm_eq_elevateBoth (H : Fin 6 → Matrix n n ℂ) :
    coefficientForm H = elevateBoth (ThreeLevelCollisionFace.coefficientForm H) := by
  rw [coefficientForm_eq_elevateCoefficients,
    ThreeLevelBernsteinElevation.coefficientForm_eq_elevateCoefficients]
  rfl

variable {m : Type*} [Fintype m]

/-- Face Matrix Value gram for the stated finite source data. -/
theorem faceMatrixValue_gram (B U V : Matrix m n ℂ) (A p : ℝ) :
    faceMatrixValue (coefficientForm (gramPieces B U V)) A p =
      (polynomialStack B U V A p)ᴴ * polynomialStack B U V A p := by
  rw [faceMatrixValue_coefficientForm, ThreeLevelCollisionFace.polynomialStack_gram]


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinFirstElevation
