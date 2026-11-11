/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Data for noncommutative matrix responses

`NCPoly` represents noncommutative polynomials as finitely supported complex coefficients on
words, with `ncWordEval` preserving the order of matrix multiplication. `ncPolyEval` forms the
corresponding finite linear combination.

The response tensors, Kronecker transition matrix, injection, and collection matrices provide
the rectangular block data used to realize these evaluations. For the underlying matrix product
constructions, see [HornJohnson1991].

## Main statements

* `ncWordEval`: ordered matrix evaluation of a word.
* `ncTransition`: the sum of transition matrices tensored with substituted matrices.
* `ncInjection` and `ncCollection`: the input and output matrices of a response realization.

## References

* [Horn and Johnson, 1991][HornJohnson1991]
-/

namespace Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

open Matrix

/-- A noncommutative polynomial represented by finitely supported complex coefficients on words
over `J`. -/
abbrev NCPoly (J : Type) := List J →₀ ℂ

variable {J X S : Type} [Fintype X] [Fintype S] [DecidableEq S]

/-- The ordered product of the matrices attached to a word, with the empty word evaluated as the
identity. -/
noncomputable def ncWordEval (A : J → Matrix S S ℂ) : List J → Matrix S S ℂ
  | [] => 1
  | j :: w => A j * ncWordEval A w

/-- The finite linear combination of word evaluations weighted by the coefficients of a
noncommutative polynomial. -/
noncomputable def ncPolyEval (A : J → Matrix S S ℂ) (q : NCPoly J) : Matrix S S ℂ :=
  Finsupp.linearCombination ℂ (ncWordEval A) q

/-- The rectangular matrix with entry `v x * M s t` at row `(x, s)` and column `t`. -/
noncomputable def ncResponseTensor (v : EuclideanSpace ℂ X) (M : Matrix S S ℂ) :
    Matrix (X × S) S ℂ := fun p y => v p.1 * M p.2 y

/-- The rectangular collection matrix with entry `c x * M s t` at row `s` and column `(x, t)`. -/
noncomputable def ncCollectTensor (c : X → ℂ) (M : Matrix S S ℂ) :
    Matrix S (X × S) ℂ := fun x p => c p.1 * M x p.2

variable [Fintype J]

/-- The sum of Kronecker products pairing each response transition `T j` with the substituted
matrix `A j`. -/
noncomputable def ncTransition (T : J → Matrix X X ℂ) (A : J → Matrix S S ℂ) :
    Matrix (X × S) (X × S) ℂ := ∑ j, Matrix.kronecker (T j) (A j)

/-- The response tensor of the state at the empty word and the identity matrix. -/
noncomputable def ncInjection (H : List J → EuclideanSpace ℂ X) : Matrix (X × S) S ℂ :=
  ncResponseTensor (H []) 1

/-- The sum of collection tensors pairing each coefficient function `C j` with the substituted
matrix `A j`. -/
noncomputable def ncCollection (C : J → X → ℂ) (A : J → Matrix S S ℂ) :
    Matrix S (X × S) ℂ := ∑ j, ncCollectTensor (C j) (A j)

end Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra
