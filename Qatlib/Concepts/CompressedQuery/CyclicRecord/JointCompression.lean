/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.TensorCompression
import Qatlib.Concepts.CompressedQuery.CyclicRecord.DatabaseQuery
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Joint compression and query intertwining

`jointCompression` tensors table compression with the identity on algorithm registers and
induces a linear isometry on joint states. The theorem `databaseQuery_compression` shows that
recording queries intertwine with ordinary table phase queries for arbitrary joint input states.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `jointCompression_isometry`: The columns of the joint compression matrix are orthonormal.
* `databaseQuery_compression`: Compression intertwines ordinary phase queries and recording
  queries.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
open Qatlib.Foundations.MatrixAlgebra.TupleMatrices
variable {W X P L : Type*} [Fintype W] [Fintype X] [Fintype P] [Fintype L] [Nonempty L]

/-- The tensor product of the identity on register states and the table compression matrix. -/
def jointCompression : Matrix (DatabaseBasis W X P L) (Registers W X P × (X → L)) ℂ :=
  (1 : Matrix (Registers W X P) (Registers W X P) ℂ) ⊗ₖ tableCompression

/-- The joint compression matrix satisfies `jointCompressionᴴ * jointCompression = 1`. -/
theorem jointCompression_isometry :
    (jointCompression (W := W) (X := X) (P := P) (L := L))ᴴ *
      jointCompression (W := W) (X := X) (P := P) (L := L)=1 := by
  unfold jointCompression
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one,Matrix.mul_one,tableCompression_isometry,Matrix.one_kronecker_one]

/-- The complex linear isometry induced by joint compression from complete-table states to
optional-label database states. -/
def jointCompressionAction : EuclideanSpace ℂ (Registers W X P × (X → L)) →ₗᵢ[ℂ]
    EuclideanSpace ℂ (DatabaseBasis W X P L) :=
  rectangularAction jointCompression (by
    ext a b
    have h := congrArg (fun C : Matrix (Registers W X P × (X → L)) (Registers W X P × (X → L)) ℂ => C a b)
      (jointCompression_isometry (W := W) (X := X) (P := P) (L := L))
    by_cases hab : a=b <;> simpa [Matrix.one_apply,hab] using h)

/-- A compressed amplitude is the sum over complete tables of the table compression coefficient
times the original joint amplitude. -/
theorem jointCompressionAction_apply
    (ψ : EuclideanSpace ℂ (Registers W X P × (X → L))) (η : Registers W X P) (db : X → Option L) :
    jointCompressionAction ψ (η,db)=∑ f : X → L,tableCompression db f*ψ (η,f) := by
  change (∑ b : Registers W X P × (X → L),jointCompression (η,db) b*ψ b)=_
  rw [Fintype.sum_prod_type]
  simp [jointCompression,Matrix.one_apply]

/-- Multiply each joint amplitude by the phase selected by its phase register and the complete
table value at its query address. -/
def standardPhase (phase : P → L → ℂ)
    (ψ : EuclideanSpace ℂ (Registers W X P × (X → L))) :
    EuclideanSpace ℂ (Registers W X P × (X → L)) :=
  WithLp.toLp 2 (fun b => phase b.1.2.2 (b.2 b.1.2.1)*ψ b)

/-- For unit modulus phases, applying a recording database query after joint compression equals
compressing the corresponding ordinary phase query state. -/
theorem databaseQuery_compression (phase : P → L → ℂ)
    (hp : ∀ p y,star (phase p y)*phase p y=1)
    (ψ : EuclideanSpace ℂ (Registers W X P × (X → L))) :
    databaseQuery phase hp (jointCompressionAction ψ)=jointCompressionAction (standardPhase phase ψ) := by
  ext b
  rcases b with ⟨η,db⟩
  rw [databaseQuery_apply,jointCompressionAction_apply]
  simp_rw [jointCompressionAction_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  calc
    _ = (∑ value : Option L,recording (phase η.2.2) (db η.2.1) value*
        tableCompression (Function.update db η.2.1 value) f)*ψ (η,f) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro value hv
      ring
    _ = _ := by
      have h := coordinate_intertwines (compression (L := L)) (recording (phase η.2.2))
        (phase η.2.2) (compression_intertwines (phase η.2.2)) db f η.2.1
      change (∑ value : Option L,recording (phase η.2.2) (db η.2.1) value*
        tableCompression (Function.update db η.2.1 value) f)=tableCompression db f*phase η.2.2 (f η.2.1) at h
      rw [h]
      change _=tableCompression db f*(phase η.2.2 (f η.2.1)*ψ (η,f))
      ring
end Qatlib.Concepts.CompressedQuery.CyclicRecord
