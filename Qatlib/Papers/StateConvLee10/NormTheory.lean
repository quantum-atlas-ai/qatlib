/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormBasicLawsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityQuan

/-!
# Filtered norm laws and rectangular duality

This module exposes filtered and unfiltered matrix norms and the query distance between Gram
matrices. It proves rectangular certificate and dual formulations, basic norm inequalities,
filter closure rules, and direct-sum and tensor-product formulas in the framework of
[LeeEtAl2011].

## Main statements

* `source_rectangular_budget`: rectangular norm bounds are equivalent to certificates and finite
  values have bounded-dimensional witnesses.
* `source_rectangular_duality`: the rectangular norm equals its Schur-product dual.
* `source_norm_filter_closure`: the norm obeys the stated filter transformations.
* `source_norm_products`: composition, direct sums, and tensor products satisfy the displayed
  bounds and identities.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.GramQueryCore.FilteredNorm

namespace Qatlib.Papers.StateConvLee10.NormTheory

/-- The rectangular filtered norm of `A` with respect to the filter family `Z` [LeeEtAl2011]. -/
def source_filtered_norm {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  sourceRectValue A Z

/-- The unfiltered matrix norm `sourceUnfiltered A` [LeeEtAl2011]. -/
def source_unfiltered_norm {R S : Type} [Fintype R] [Fintype S]
    (A : Matrix R S ℂ) : ℝ≥0∞ :=
  sourceUnfiltered A

/-- The filtered norm of `ρ - σ` with respect to the alphabet-difference filters of `input`
[LeeEtAl2011]. -/
def source_query_distance {X : Type} [Fintype X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  source_filtered_norm (ρ-σ) (sourceAlphabetDelta input)

/-- The rectangular norm equals the lifted filtered gamma-two norm, its nonnegative real bounds
are equivalent to certificates, and every finite value has an attaining witness of dimension
at most `n * (|R| + |S|)` [LeeEtAl2011]. -/
theorem source_rectangular_budget :
    ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      sourceRectValue A Z = filteredGamma2 (sourceRectLift A) (fun j => sourceRectLift (Z j)) ∧
      (∀ w : ℝ, 0 ≤ w →
        (sourceRectValue A Z ≤ ENNReal.ofReal w ↔ sourceRectCert n A Z w)) ∧
      (sourceRectValue A Z < ⊤ → ∃ (w : ℝ) (m : ℕ)
        (u : R → Fin n → QState (Fin m)) (v : S → Fin n → QState (Fin m)),
        0 ≤ w ∧ m ≤ n*(Fintype.card R+Fintype.card S) ∧
        sourceRectValue A Z = ENNReal.ofReal w ∧
        (∀ r s, A r s = ∑ j, Z j r s * ∑ k, star (u r j k)*v s j k) ∧
        (∀ r, ∑ j, ‖toEuclidean_fromVec (u r j)‖^2 ≤ w) ∧
        (∀ s, ∑ j, ‖toEuclidean_fromVec (v s j)‖^2 ≤ w)) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.rectangularBudgetRealization

/-- The rectangular norm equals its Schur-product dual; finite values have maximizing dual
witnesses, while an infinite value yields dual objectives above any prescribed real
threshold [LeeEtAl2011]. -/
theorem source_rectangular_duality :
    ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      sourceRectValue A Z = sourceRectDual A Z ∧
      (sourceRectValue A Z < ⊤ → ∃ M : Matrix R S ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ sourceRectValue A Z=ENNReal.ofReal ‖A ⊙ M‖) ∧
      (sourceRectValue A Z = ⊤ → ∀ t : ℝ, ∃ M : Matrix R S ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ t ≤ ‖A ⊙ M‖) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.rectangularSchurDuality

/-- The rectangular filtered norm satisfies the displayed normalization, zero and support
characterizations, scaling rules, triangle inequality, and Hadamard-product inequalities
[LeeEtAl2011]. -/
theorem source_norm_basic_laws :
  ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (n : ℕ) (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
    (A ≠ 0 → sourceRectValue A (fun _ : Fin 1 => A)=1) ∧
    (sourceRectValue A Z=0 ↔ A=0) ∧
    (sourceRectValue A Z=⊤ ↔ ¬sourceSupports A Z) ∧
    (∀ c : ℂ, sourceRectValue (c • A) Z=ENNReal.ofReal ‖c‖*sourceRectValue A Z) ∧
    (∀ c : ℂ, c ≠ 0 → sourceRectValue A (fun j => c • Z j)=
      (ENNReal.ofReal ‖c‖)⁻¹*sourceRectValue A Z) ∧
    sourceRectValue (A+B) Z ≤ sourceRectValue A Z+sourceRectValue B Z ∧
    sourceRectValue (A ⊙ B) Z ≤ sourceRectValue A Z*sourceUnfiltered B ∧
    sourceRectValue (A ⊙ B) (fun j => Z j ⊙ B) ≤ sourceRectValue A Z ∧
    ((sourceRectValue A (fun j => Z j ⊙ B) < ⊤ ∨ B ≠ 0) →
      sourceRectValue A Z ≤ sourceRectValue A (fun j => Z j ⊙ B)*sourceUnfiltered B) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.filteredNormBasicLaws

/-- The rectangular filtered norm obeys the stated surjective reindexing, filter addition and
restriction, absolutely bounded filter-combination, and disjoint-filter merging rules
[LeeEtAl2011]. -/
theorem source_norm_filter_closure :
  (∀ (R S R' S' : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      [Fintype R'] [DecidableEq R'] [Fintype S'] [DecidableEq S'] (n : ℕ)
      (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
      (f : R' → R) (g : S' → S), Function.Surjective f → Function.Surjective g →
      sourceRectValue (A.submatrix f g) (fun j => (Z j).submatrix f g)=sourceRectValue A Z) ∧
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n m : ℕ) (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      sourceRectValue A (sourceFilterUnion Y Z) ≤ sourceRectValue A Z ∧
      ((∀ i, ∃ (j : Fin n) (rows : Finset R) (cols : Finset S),
        ∀ r s, Y i r s=if r ∈ rows ∧ s ∈ cols then Z j r s else 0) →
        sourceRectValue A (sourceFilterUnion Y Z)=sourceRectValue A Z)) ∧
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (p : Fin n → ℂ),
      (∑ j, ‖p j‖) ≤ 1 → sourceRectValue A
        (sourceFilterUnion Z (fun _ : Fin 1 => ∑ j, p j • Z j))=sourceRectValue A Z) ∧
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin (n+2) → Matrix R S ℂ),
      sourceRowColumnDisjoint (Z 0) (Z 1) →
        sourceRectValue A (sourceMergeTwo Z)=sourceRectValue A Z) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.filteredNormClosureLaws

/-- The rectangular filtered norm satisfies the stated filter-composition bound under its
finiteness or nonzero condition, equals the maximum for direct sums, and is multiplicative
for tensor products with tensor filters [LeeEtAl2011]. -/
theorem source_norm_products :
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n m : ℕ) (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ)
      (Z : Fin n → Matrix R S ℂ),
      (sourceRectValue A Y < ⊤ ∨ (⨆ j, sourceRectValue (Y j) Z) ≠ 0) →
      sourceRectValue A Z ≤ sourceRectValue A Y * ⨆ j, sourceRectValue (Y j) Z) ∧
  (∀ (R S U V : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] (n : ℕ)
      (A : Matrix R S ℂ) (B : Matrix U V ℂ)
      (Y : Fin n → Matrix R S ℂ) (Z : Fin n → Matrix U V ℂ),
      sourceRectValue (sourceDirectSum A B) (fun j => sourceDirectSum (Y j) (Z j))=
        max (sourceRectValue A Y) (sourceRectValue B Z)) ∧
  (∀ (R S U V : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] (n m : ℕ)
      (A : Matrix R S ℂ) (B : Matrix U V ℂ)
      (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ),
      sourceRectValue (sourceTensor A B) (sourceFilterTensor Y Z)=
        sourceRectValue A Y*sourceRectValue B Z) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.filteredNormCompositionAndProducts

end Qatlib.Papers.StateConvLee10.NormTheory
