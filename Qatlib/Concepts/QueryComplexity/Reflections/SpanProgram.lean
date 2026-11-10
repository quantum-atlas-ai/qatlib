/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgramGraph
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators
variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

def SourceDualFeasible (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) : Prop :=
  (∀ x,∑ j,∑ k,‖v x j k‖^2 ≤ W) ∧
  (∀ x y,f x=false → f y=true →
    (∑ j : Fin n,if input x j≠input y j then Inner (v x j) (v y j) else 0)=1)

def sourcePixBar (input : X → Fin n → Bool) (x : X) : Matrix (IVert n m) (IVert n m) ℂ :=
  Matrix.diagonal fun jb=>if jb.2.1= !(input x jb.1) then 1 else 0

def sourceMarkedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m) (ColLab X f n m) ℂ :=
  Matrix.fromCols
    (Matrix.fromRows (Matrix.of fun x _=>tvec W x) (0 : Matrix (IVert n m) Unit ℂ))
    (Matrix.fromRows (bigA input f v) (sourcePixBar input x))

def sourceRestrictedBiadj (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) : Matrix (RowLab X f n m) (IVert n m) ℂ :=
  Matrix.fromRows (bigA input f v) (sourcePixBar input x)

def sourceMarkedAdjacency (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    Matrix (RowLab X f n m ⊕ ColLab X f n m) (RowLab X f n m ⊕ ColLab X f n m) ℂ :=
  blockAdjacency (sourceMarkedBiadj input f v W x)

def sourcePositiveWitness (input : X → Fin n → Bool) (_f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) : QState (ColLab X _f n m)
  | Sum.inl _=>((-3*Real.sqrt W : ℝ) : ℂ)
  | Sum.inr (j,b,k)=>if b=input x j then v x j k else 0

def sourceNegativeWitness (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (x : X) : QState (RowLab X f n m)
  | Sum.inl y=>if y.val=x then -1 else 0
  | Sum.inr (j,b,k)=>if b= !(input x j) then v x j k else 0
end Qatlib.Concepts.QueryComplexity.Reflections
