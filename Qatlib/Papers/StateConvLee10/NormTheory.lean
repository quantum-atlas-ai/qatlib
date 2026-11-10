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

def source_filtered_norm {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : ℝ≥0∞ :=
  sourceRectValue A Z

def source_unfiltered_norm {R S : Type} [Fintype R] [Fintype S]
    (A : Matrix R S ℂ) : ℝ≥0∞ :=
  sourceUnfiltered A

def source_query_distance {X : Type} [Fintype X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  source_filtered_norm (ρ-σ) (sourceAlphabetDelta input)

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

theorem source_rectangular_duality :
    ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      sourceRectValue A Z = sourceRectDual A Z ∧
      (sourceRectValue A Z < ⊤ → ∃ M : Matrix R S ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ sourceRectValue A Z=ENNReal.ofReal ‖A ⊙ M‖) ∧
      (sourceRectValue A Z = ⊤ → ∀ t : ℝ, ∃ M : Matrix R S ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ t ≤ ‖A ⊙ M‖) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.rectangularSchurDuality

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
