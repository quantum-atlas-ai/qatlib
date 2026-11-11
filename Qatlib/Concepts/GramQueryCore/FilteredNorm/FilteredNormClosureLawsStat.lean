/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Filtered norm closure specification

The proposition `FilteredNormClosureLaws` states the behavior of the rectangular filtered value
under submatrix restriction, surjective pullback, masked filter extension, contractive filter
combinations, and disjoint merging. It packages closure properties of the filtered γ₂ framework
[LeeEtAl2011].

## Main statements

* `FilteredNormClosureLaws`: The conjunction of submatrix monotonicity, invariance under
  surjective pullback, redundant filter extension, and disjoint filter merging laws.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The conjunction of submatrix monotonicity, invariance under surjective pullback, redundant
filter extension, and disjoint filter merging laws. -/
def FilteredNormClosureLaws : Prop :=
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
        sourceRectValue A (sourceMergeTwo Z)=sourceRectValue A Z)
end Qatlib.Concepts.GramQueryCore.FilteredNorm
