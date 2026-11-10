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
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix

section Construction

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

abbrev Fin0 (X : Type) (f : X → Bool) : Type := {x : X // f x = false}

abbrev IVert (n m : ℕ) : Type := Fin n × Bool × Fin m

abbrev ColLab (X : Type) (_f : X → Bool) (n m : ℕ) : Type := Unit ⊕ IVert n m

abbrev Vertex (X : Type) (f : X → Bool) (n m : ℕ) : Type :=
  Fin0 X f ⊕ ColLab X f n m

abbrev RowLab (X : Type) (f : X → Bool) (n m : ℕ) : Type :=
  Fin0 X f ⊕ IVert n m

noncomputable def tvec {X : Type} [Fintype X] {f : X → Bool} (W : ℝ) :
    QState (Fin0 X f) :=
  fun _ => ((1 / (3 * Real.sqrt W) : ℝ) : ℂ)

noncomputable def bigA (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) : Matrix (Fin0 X f) (IVert n m) ℂ :=
  fun x (j, b, k) => if b = !(input x j) then star (v x j k) else 0

noncomputable def biadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) :
    Matrix (Fin0 X f) (ColLab X f n m) ℂ :=
  Matrix.fromCols (Matrix.of fun x _ => tvec W x) (bigA input f v)

noncomputable def blockAdjacency {R C : Type} [DecidableEq R] [DecidableEq C]
    (B : Matrix R C ℂ) : Matrix (R ⊕ C) (R ⊕ C) ℂ :=
  fun p q =>
    match p, q with
    | Sum.inl r, Sum.inr c => B r c
    | Sum.inr c, Sum.inl r => star (B r c)
    | _, _ => 0

noncomputable def adjacency (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) :
    Matrix (Vertex X f n m) (Vertex X f n m) ℂ :=
  blockAdjacency (biadj input f v W)

noncomputable def pixBar (input : X → Fin n → Bool) (x : X) :
    Matrix (IVert n m) (IVert n m) ℂ :=
  Matrix.diagonal fun jb => if jb.2.1 = !(input x jb.1) then (0 : ℂ) else 1

noncomputable def markedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m) (ColLab X f n m) ℂ :=
  Matrix.fromCols
    (Matrix.fromRows (Matrix.of fun x _ => tvec W x)
      (0 : Matrix (IVert n m) Unit ℂ))
    (Matrix.fromRows (bigA input f v) (pixBar input x))

noncomputable def restrictedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) :
    Matrix (RowLab X f n m) (IVert n m) ℂ :=
  Matrix.fromRows (bigA input f v) (pixBar input x)

noncomputable def markedAdjacency (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m ⊕ ColLab X f n m) (RowLab X f n m ⊕ ColLab X f n m) ℂ :=
  blockAdjacency (markedBiadj input f v W x)

def complementMark (input : X → Fin n → Bool) (_f : X → Bool) (x : X) :
    ColLab X _f n m → Bool :=
  fun c =>
    match c with
    | Sum.inl _ => false
    | Sum.inr (j, b, _) => decide (b = !(input x j))

noncomputable def pixProj (input : X → Fin n → Bool) (f : X → Bool) (x : X) :
    Matrix (Vertex X f n m) (Vertex X f n m) ℂ :=
  Matrix.diagonal fun l =>
    match l with
    | Sum.inl _ => (1 : ℂ)
    | Sum.inr c => if complementMark input f x c then (0 : ℂ) else 1

noncomputable def twoReflectionUnitary (input : X → Fin n → Bool) (f : X → Bool)
    (x : X) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) :
    Matrix (Vertex X f n m) (Vertex X f n m) ℂ :=
  ((2 : ℂ) • pixProj input f x - 1) * ((2 : ℂ) • Δ - 1)

end Construction

end Qatlib.Concepts.QueryComplexity.Reflections
