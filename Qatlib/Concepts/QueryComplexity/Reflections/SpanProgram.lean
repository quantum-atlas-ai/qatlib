/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgramGraph

/-!
# Source dual feasibility and span-program witnesses

Defines `SourceDualFeasible`, combining a uniform witness norm budget with unit overlap across
differing coordinates for false-true input pairs. It then constructs the source complement-label
projector, marked graph matrices, and explicit positive and negative witnesses.

These definitions provide the source-oriented span-program data for the reflection-query
construction in [Reichardt2011].

## Main statements

* `SourceDualFeasible`: specifies the witness norm and cross-input overlap constraints.
* `sourceMarkedAdjacency`: forms the Hermitian adjacency from the complement-marked biadjacency.
* `sourcePositiveWitness`: defines the root-augmented positive witness.
* `sourceNegativeWitness`: defines the false-row and complement-label negative witness.

## References

* [Reichardt, 2011][Reichardt2011]
-/

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators
variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

/-- The witness norm budget together with unit overlap, summed over differing input coordinates,
between every false-input and true-input witness pair. -/
def SourceDualFeasible (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) : Prop :=
  (∀ x,∑ j,∑ k,‖v x j k‖^2 ≤ W) ∧
  (∀ x y,f x=false → f y=true →
    (∑ j : Fin n,if input x j≠input y j then Inner (v x j) (v y j) else 0)=1)

/-- The diagonal projector onto labels whose Boolean component is the complement of the input
bit. -/
def sourcePixBar (input : X → Fin n → Bool) (x : X) : Matrix (IVert n m) (IVert n m) ℂ :=
  Matrix.diagonal fun jb=>if jb.2.1= !(input x jb.1) then 1 else 0

/-- The source marked biadjacency formed from the target column, witness matrix, and
complement-label projector. -/
def sourceMarkedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m) (ColLab X f n m) ℂ :=
  Matrix.fromCols
    (Matrix.fromRows (Matrix.of fun x _=>tvec W x) (0 : Matrix (IVert n m) Unit ℂ))
    (Matrix.fromRows (bigA input f v) (sourcePixBar input x))

/-- The source restricted biadjacency obtained by stacking the witness matrix above the
complement-label projector. -/
def sourceRestrictedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) : Matrix (RowLab X f n m) (IVert n m) ℂ :=
  Matrix.fromRows (bigA input f v) (sourcePixBar input x)

/-- The Hermitian block adjacency associated with the source marked biadjacency. -/
def sourceMarkedAdjacency (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m ⊕ ColLab X f n m) (RowLab X f n m ⊕ ColLab X f n m) ℂ :=
  blockAdjacency (sourceMarkedBiadj input f v W x)

/-- The column-side witness with root coordinate `-3 * sqrt W` and input-matching witness
entries elsewhere. -/
def sourcePositiveWitness (input : X → Fin n → Bool) (_f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) : QState (ColLab X _f n m)
  | Sum.inl _=>((-3*Real.sqrt W : ℝ) : ℂ)
  | Sum.inr (j,b,k)=>if b=input x j then v x j k else 0

/-- The row-side witness with coefficient minus one at the selected false-input row and witness
entries on complement input labels. -/
def sourceNegativeWitness (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) : QState (RowLab X f n m)
  | Sum.inl y=>if y.val=x then -1 else 0
  | Sum.inr (j,b,k)=>if b= !(input x j) then v x j k else 0
end Qatlib.Concepts.QueryComplexity.Reflections
