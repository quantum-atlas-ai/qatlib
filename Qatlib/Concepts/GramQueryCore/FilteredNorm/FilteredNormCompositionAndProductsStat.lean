/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def FilteredNormCompositionAndProducts : Prop :=
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
        sourceRectValue A Y*sourceRectValue B Z)
end Qatlib.Concepts.GramQueryCore.FilteredNorm
