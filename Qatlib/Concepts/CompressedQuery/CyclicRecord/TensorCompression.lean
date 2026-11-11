/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.Entries
import Qatlib.Foundations.MatrixAlgebra.TupleMatrices.Coordinate
import Qatlib.Foundations.MatrixAlgebra.TupleMatrices.IsometryAction

/-!
# Product compression of complete tables

This module forms `tableCompression` by applying the single-cell compression matrix
independently at every address. The resulting matrix is isometric, maps the uniform
complete-table vector to the empty database ket, and is invariant under simultaneous relabelling
of labels.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `tableCompression_isometry`: Product compression has orthonormal columns.
* `tableCompression_uniform`: The uniform complete-table vector compresses to the empty
  database.
* `tableCompression_relabel`: Compression entries are unchanged by simultaneous label
  permutations.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
open Qatlib.Foundations.MatrixAlgebra.TupleMatrices
variable {X L : Type*} [Fintype X] [Fintype L] [Nonempty L]

/-- The product matrix applying single-cell compression independently to each complete-table
coordinate. -/
def tableCompression : Matrix (X → Option L) (X → L) ℂ :=
    tupleMatrix (fun _x : X => compression (L := L))

/-- The table compression matrix satisfies `tableCompressionᴴ * tableCompression = 1`. -/
theorem tableCompression_isometry : (tableCompression (X := X) (L := L))ᴴ*tableCompression (X := X) (L := L)=1 := by
  exact tupleMatrix_isometry (fun _x : X => compression (L := L)) (fun _x => compression_isometry)

/-- Single-cell compression sends the uniform label vector with amplitude `coefficient L` to the
empty basis ket. -/
theorem compression_uniform : compression (L := L)*ᵥ (fun _ : L => (coefficient L : ℂ))=Pi.single none 1 := by
  funext i
  cases i with
  | none =>
    change (∑ y : L,uniformSwap none (some y)*(coefficient L : ℂ))=1
    simp_rw [swap_none_some]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← pow_two]
    exact coefficient_complex
  | some x =>
    change (∑ y : L,uniformSwap (some x) (some y)*(coefficient L : ℂ))=0
    simp_rw [swap_some_some,sub_mul,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul]
    have h := coefficient_complex (L := L)
    linear_combination -(coefficient L : ℂ)*h
omit [Fintype L] [Nonempty L] in

/-- The product of empty-cell indicator amplitudes is the indicator amplitude of the all-empty
database. -/
theorem product_empty (db : X → Option L) :
    (∏ x,(Pi.single (none : Option L) (1 : ℂ) : Option L → ℂ) (db x))=(Pi.single (fun _ : X => (none : Option L)) (1 : ℂ) : (X → Option L) → ℂ) db := by
  by_cases h : db=(fun _ => none)
  · subst db
    simp
  · have he : ∃ x,db x ≠ none := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨x,hx⟩ := he
    rw [Pi.single_eq_of_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    simp [hx]

/-- Table compression sends the product uniform vector on complete tables to the all-empty
database ket. -/
theorem tableCompression_uniform :
    tableCompression (X := X) (L := L)*ᵥ (fun _f : X → L => ∏ _x : X,(coefficient L : ℂ))=
      Pi.single (fun _ : X => (none : Option L)) 1 := by
  funext db
  have h := tupleMatrix_product_apply (fun _x : X => compression (L := L))
    (fun _x : X => fun _y : L => (coefficient L : ℂ)) db
  simp only [compression_uniform] at h
  exact h.trans (product_empty db)

/-- The complex linear isometry on Euclidean table spaces induced by the table compression
matrix. -/
def tableCompressionAction : EuclideanSpace ℂ (X → L) →ₗᵢ[ℂ] EuclideanSpace ℂ (X → Option L) :=
  rectangularAction (tableCompression (X := X) (L := L)) (by
    ext f g
    have h := congrArg (fun M : Matrix (X → L) (X → L) ℂ => M f g)
      (tableCompression_isometry (X := X) (L := L))
    by_cases hfg : f=g <;> simpa [Matrix.one_apply,hfg] using h)
omit [Nonempty L] in

/-- Simultaneously permuting the optional row label and the column label leaves a single-cell
compression entry unchanged. -/
theorem compression_relabel (σ : Equiv.Perm L) (i : Option L) (y : L) :
    compression (Option.map σ i) (σ y)=compression i y := by
  cases i with
  | none => exact (swap_none_some (σ y)).trans (swap_none_some y).symm
  | some x =>
    simp only [compression,Option.map_some,swap_some_some,σ.injective.eq_iff]
omit [Nonempty L] in

/-- Simultaneously applying the same label permutation to every optional database cell and every
complete-table value leaves a table compression entry unchanged. -/
theorem tableCompression_relabel (σ : Equiv.Perm L) (db : X → Option L) (f : X → L) :
    tableCompression (fun x => Option.map σ (db x)) (σ ∘ f)=tableCompression db f := by
  apply Finset.prod_congr rfl
  intro x hx
  exact compression_relabel σ (db x) (f x)
end Qatlib.Concepts.CompressedQuery.CyclicRecord
