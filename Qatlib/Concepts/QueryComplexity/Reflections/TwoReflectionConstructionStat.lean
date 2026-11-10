/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgramGraph
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.Reflections

open Matrix
open scoped BigOperators

def TwoReflectionConstruction : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    (adjacency input f v W)ᴴ = adjacency input f v W ∧
    (∀ x : X, IsOrthogonalProjector (pixProj (m := m) input f x)) ∧
    (∀ x : X, (2 : ℂ) • pixProj (m := m) input f x
        - (1 : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
        = PhaseOracle (fun l => match l with
          | Sum.inl _ => false
          | Sum.inr c => complementMark input f x c)) ∧
    (∃ Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ,
      IsOrthogonalProjector Δ ∧
      ∀ z : QState (Vertex X f n m),
        adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)

end Qatlib.Concepts.QueryComplexity.Reflections
