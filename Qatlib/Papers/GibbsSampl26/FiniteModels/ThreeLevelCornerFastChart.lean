/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelGramCertificateCorner
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm

@[expose] public section


/-!
# Explicit coordinates for the actual thirteen-dimensional fast space

The fixed literal F is connected to the existing Hilbert--Schmidt fastPart,
for every complex matrix. The sparse coordinate formula is checked directly
against the actual projectors, and is a left inverse on the literal fast
columns. All spectral-label permutations share this projection.

This discharges the fast-span transport left separate by the scalar-corner
certificate. The quadratic-form normalization and final ScaledStackBounds
consumer remain separate obligations; no continuum certificate is claimed.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCornerFastChart
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelGramCertificate ThreeLevelGramCertificateCorner

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

noncomputable def fastCoordinates (X : Operator 4) : Fin 15 → ℂ :=
  ![0, 0, X 0 1, X 0 2, X 0 3, X 1 0,
    X 1 1 - X 3 3 - (3*Complex.I/4)*X 3 2,
    X 1 2 + (Complex.I/2)*X 3 2,
    X 1 3 + X 3 2/2,
    X 2 0,
    X 2 1 + (Complex.I/2)*X 3 2,
    X 2 2 - X 3 3,
    X 2 3 + X 3 2,
    X 3 0,
    X 3 1 - X 3 2/2]

/-- Fast Coordinates first zero for the stated finite source data. -/
theorem fastCoordinates_first_zero (X : Operator 4) : fastCoordinates X 0 = 0 := rfl

/-- Fast Coordinates second zero for the stated finite source data. -/
theorem fastCoordinates_second_zero (X : Operator 4) : fastCoordinates X 1 = 0 := rfl

/-- Literal Combination fast Coordinates for the stated finite source data. -/
theorem literalCombination_fastCoordinates (X : Operator 4) :
    literalCombination (fastCoordinates X) = fastPart (Equiv.refl (Fin 3)) X := by
  simp only [fastPart, populationPart, population, populationCoefficient,
    hsInner, spectralProjectors_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [literalCombination, fastCoordinates, literalInput, fromParts,
      inputMatrixReal, inputMatrixImag, inputReal, inputImag, flatIndex,
      spectralProjectors, ThreeLevelWordDual.projectors, ThreeLevelWordDual.pZero,
      ThreeLevelWordDual.pOne, ThreeLevelWordDual.pTwo_entries, projectorRank,
      Matrix.trace, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    norm_num <;> ring_nf <;> simp [Complex.I_sq] <;> ring


/-- Population Part permutation for the stated finite source data. -/
theorem populationPart_permutation (σ : Perm) (X : Operator 4) :
    populationPart σ X = populationPart (Equiv.refl (Fin 3)) X := by
  change (∑ i, (hsInner (ThreeLevelWordDual.projectors (σ i)) X /
    (projectorRank (σ i) : ℂ)) • ThreeLevelWordDual.projectors (σ i)) =
    ∑ i, (hsInner (ThreeLevelWordDual.projectors i) X /
      (projectorRank i : ℂ)) • ThreeLevelWordDual.projectors i
  exact Equiv.sum_comp σ (fun i : Fin 3 =>
    (hsInner (ThreeLevelWordDual.projectors i) X /
      (projectorRank i : ℂ)) • ThreeLevelWordDual.projectors i)

/-- Fast Part permutation for the stated finite source data. -/
theorem fastPart_permutation (σ : Perm) (X : Operator 4) :
    fastPart σ X = fastPart (Equiv.refl (Fin 3)) X := by
  simp only [fastPart, populationPart_permutation σ X]

/-- Literal Combination fast Coordinates perm for the stated finite source data. -/
theorem literalCombination_fastCoordinates_perm (σ : Perm) (X : Operator 4) :
    literalCombination (fastCoordinates X) = fastPart σ X :=
  (literalCombination_fastCoordinates X).trans (fastPart_permutation σ X).symm

/-- Literal Combination of Is Fast for the stated finite source data. -/
theorem literalCombination_of_IsFast (σ : Perm) (X : Operator 4) (hX : IsFast σ X) :
    literalCombination (fastCoordinates X) = X :=
  (literalCombination_fastCoordinates_perm σ X).trans (fastPart_eq_self σ X hX)

/-- Fast Coordinates literal Combination for the stated finite source data. -/
theorem fastCoordinates_literalCombination (z : Fin 15 → ℂ)
    (h0 : z 0 = 0) (h1 : z 1 = 0) :
    fastCoordinates (literalCombination z) = z := by
  funext i
  fin_cases i <;>
    simp [fastCoordinates, literalCombination, literalInput, fromParts,
      inputMatrixReal, inputMatrixImag, inputReal, inputImag, flatIndex,
      Matrix.smul_apply, Matrix.sum_apply, Fin.sum_univ_succ, smul_eq_mul, h0, h1] <;>
    norm_num <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Literal Combination is Fast for the stated finite source data. -/
theorem literalCombination_isFast (σ : Perm) (z : Fin 15 → ℂ)
    (h0 : z 0 = 0) (h1 : z 1 = 0) : IsFast σ (literalCombination z) := by
  have he : literalCombination z = fastPart σ (literalCombination z) := by
    simpa only [fastCoordinates_literalCombination z h0 h1] using
      literalCombination_fastCoordinates_perm σ (literalCombination z)
  rw [he]
  exact fastPart_isFast σ _

/-- Is Fast iff literal Combination for the stated finite source data. -/
theorem IsFast_iff_literalCombination (σ : Perm) (X : Operator 4) :
    IsFast σ X ↔ ∃ z : Fin 15 → ℂ,
      z 0 = 0 ∧ z 1 = 0 ∧ literalCombination z = X := by
  constructor
  · intro hX
    exact ⟨fastCoordinates X, fastCoordinates_first_zero X,
      fastCoordinates_second_zero X, literalCombination_of_IsFast σ X hX⟩
  · rintro ⟨z,h0,h1,rfl⟩
    exact literalCombination_isFast σ z h0 h1

/-- Fast coordinates unique for the stated finite source data. -/
theorem fast_coordinates_unique (X : Operator 4)
    (z : Fin 15 → ℂ) (h0 : z 0 = 0) (h1 : z 1 = 0)
    (hz : literalCombination z = X) : z = fastCoordinates X := by
  rw [← hz, fastCoordinates_literalCombination z h0 h1]

/-- Actual fast gradient chart for the stated finite source data. -/
theorem actual_fast_gradient_chart (σ : Perm) (X : Operator 4) (hX : IsFast σ X)
    (a : Fin 96) :
    (cornerStack *ᵥ fastCoordinates X) a =
      actualGradient σ (fun _ => 0) (sourceIndex a) X (rowIndex a) (columnIndex a) := by
  rw [cornerStack_mulVec_eq_actualGradient σ, literalCombination_of_IsFast σ X hX]


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCornerFastChart
