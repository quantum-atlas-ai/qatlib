/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Sqrt
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Span-program graph and reflection matrices

Defines finite graph labels, the target-augmented witness biadjacency, and their Hermitian block
adjacencies. The module also distinguishes input-matching projectors from complement marks and
builds `pixProj` on the unmarked vertex space.

`twoReflectionUnitary` is the matrix product of the input reflection and the reflection
specified by a supplied matrix `Δ`; it is a unitary reflection product when `Δ` is an orthogonal
projector. These graph definitions follow the setting of [Reichardt2011].

## Main statements

* `blockAdjacency`: places a matrix and its adjoint in the off-diagonal blocks.
* `adjacency`: constructs the unmarked witness graph.
* `pixProj`: retains row vertices, the root, and input-matching column labels.
* `twoReflectionUnitary`: forms the product of the two reflection matrices.

## References

* [Reichardt, 2011][Reichardt2011]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix

section Construction

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

/-- The subtype of inputs on which the Boolean function is false. -/
abbrev Fin0 (X : Type) (f : X → Bool) : Type := {x : X // f x = false}

/-- The input-label vertex type consisting of a query position, a Boolean label, and a witness
coordinate. -/
abbrev IVert (n m : ℕ) : Type := Fin n × Bool × Fin m

/-- The column-label type with a distinguished root and the input-label vertices. -/
abbrev ColLab (X : Type) (_f : X → Bool) (n m : ℕ) : Type := Unit ⊕ IVert n m

/-- The graph vertex type consisting of false-input row vertices and column vertices. -/
abbrev Vertex (X : Type) (f : X → Bool) (n m : ℕ) : Type :=
  Fin0 X f ⊕ ColLab X f n m

/-- The row-label type consisting of false-input rows and additional input-label vertices. -/
abbrev RowLab (X : Type) (f : X → Bool) (n m : ℕ) : Type :=
  Fin0 X f ⊕ IVert n m

/-- The constant target vector on false-input rows, with entry `1 / (3 * sqrt W)`. -/
noncomputable def tvec {X : Type} [Fintype X] {f : X → Bool} (W : ℝ) :
    QState (Fin0 X f) :=
  fun _ => ((1 / (3 * Real.sqrt W) : ℝ) : ℂ)

/-- The witness matrix whose entries are conjugated witness coordinates on labels complementary
to the row input, and zero otherwise. -/
noncomputable def bigA (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) : Matrix (Fin0 X f) (IVert n m) ℂ :=
  fun x (j, b, k) => if b = !(input x j) then star (v x j k) else 0

/-- The biadjacency matrix formed by adjoining the target vector as a root column to `bigA`. -/
noncomputable def biadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) :
    Matrix (Fin0 X f) (ColLab X f n m) ℂ :=
  Matrix.fromCols (Matrix.of fun x _ => tvec W x) (bigA input f v)

/-- The Hermitian bipartite adjacency with off-diagonal blocks `B` and `Bᴴ` and zero diagonal
blocks. -/
noncomputable def blockAdjacency {R C : Type} [DecidableEq R] [DecidableEq C]
    (B : Matrix R C ℂ) : Matrix (R ⊕ C) (R ⊕ C) ℂ :=
  fun p q =>
    match p, q with
    | Sum.inl r, Sum.inr c => B r c
    | Sum.inr c, Sum.inl r => star (B r c)
    | _, _ => 0

/-- The unmarked graph adjacency associated with the target-augmented witness biadjacency. -/
noncomputable def adjacency (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) :
    Matrix (Vertex X f n m) (Vertex X f n m) ℂ :=
  blockAdjacency (biadj input f v W)

/-- The diagonal projector onto input-matching Boolean labels. -/
noncomputable def pixBar (input : X → Fin n → Bool) (x : X) :
    Matrix (IVert n m) (IVert n m) ℂ :=
  Matrix.diagonal fun jb => if jb.2.1 = !(input x jb.1) then (0 : ℂ) else 1

/-- The biadjacency formed by adjoining input-matching label rows to the target-augmented
witness matrix. -/
noncomputable def markedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m) (ColLab X f n m) ℂ :=
  Matrix.fromCols
    (Matrix.fromRows (Matrix.of fun x _ => tvec W x)
      (0 : Matrix (IVert n m) Unit ℂ))
    (Matrix.fromRows (bigA input f v) (pixBar input x))

/-- The matrix formed by stacking the witness matrix above the input-matching label projector. -/
noncomputable def restrictedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) :
    Matrix (RowLab X f n m) (IVert n m) ℂ :=
  Matrix.fromRows (bigA input f v) (pixBar input x)

/-- The Hermitian block adjacency of `markedBiadj`. -/
noncomputable def markedAdjacency (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m ⊕ ColLab X f n m) (RowLab X f n m ⊕ ColLab X f n m) ℂ :=
  blockAdjacency (markedBiadj input f v W x)

/-- Marks precisely the non-root column labels whose Boolean component complements the input
bit. -/
def complementMark (input : X → Fin n → Bool) (_f : X → Bool) (x : X) :
    ColLab X _f n m → Bool :=
  fun c =>
    match c with
    | Sum.inl _ => false
    | Sum.inr (j, b, _) => decide (b = !(input x j))

/-- The diagonal projector retaining row vertices, the root, and input-matching column labels. -/
noncomputable def pixProj (input : X → Fin n → Bool) (f : X → Bool) (x : X) :
    Matrix (Vertex X f n m) (Vertex X f n m) ℂ :=
  Matrix.diagonal fun l =>
    match l with
    | Sum.inl _ => (1 : ℂ)
    | Sum.inr c => if complementMark input f x c then (0 : ℂ) else 1

/-- The matrix product of `2 • pixProj - 1` and `2 • Δ - 1`, representing the two reflections
when `Δ` is an orthogonal projector. -/
noncomputable def twoReflectionUnitary (input : X → Fin n → Bool) (f : X → Bool)
    (x : X) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) :
    Matrix (Vertex X f n m) (Vertex X f n m) ℂ :=
  ((2 : ℂ) • pixProj input f x - 1) * ((2 : ℂ) • Δ - 1)

end Construction

end Qatlib.Concepts.QueryComplexity.Reflections
