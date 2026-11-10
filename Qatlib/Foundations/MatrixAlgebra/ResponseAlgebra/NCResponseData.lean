/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

open Matrix

abbrev NCPoly (J : Type) := List J →₀ ℂ

variable {J X S : Type} [Fintype X] [Fintype S] [DecidableEq S]

noncomputable def ncWordEval (A : J → Matrix S S ℂ) : List J → Matrix S S ℂ
  | [] => 1
  | j :: w => A j * ncWordEval A w

noncomputable def ncPolyEval (A : J → Matrix S S ℂ) (q : NCPoly J) : Matrix S S ℂ :=
  Finsupp.linearCombination ℂ (ncWordEval A) q

noncomputable def ncResponseTensor (v : EuclideanSpace ℂ X) (M : Matrix S S ℂ) :
    Matrix (X × S) S ℂ := fun p y => v p.1 * M p.2 y

noncomputable def ncCollectTensor (c : X → ℂ) (M : Matrix S S ℂ) :
    Matrix S (X × S) ℂ := fun x p => c p.1 * M x p.2

variable [Fintype J]

noncomputable def ncTransition (T : J → Matrix X X ℂ) (A : J → Matrix S S ℂ) :
    Matrix (X × S) (X × S) ℂ := ∑ j, Matrix.kronecker (T j) (A j)

noncomputable def ncInjection (H : List J → EuclideanSpace ℂ X) : Matrix (X × S) S ℂ :=
  ncResponseTensor (H []) 1

noncomputable def ncCollection (C : J → X → ℂ) (A : J → Matrix S S ℂ) :
    Matrix S (X × S) ℂ := ∑ j, ncCollectTensor (C j) (A j)

end Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra
