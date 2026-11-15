/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace Qatlib.Foundations.MatrixAlgebra.Permanent

def PerturbedPermanentExpansion : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℂ),
    Matrix.permanent
        (Matrix.of fun i j => if i = 0 ∧ j = 0 then X 0 0 - r else X i j)
      = Matrix.permanent X
        - r * Matrix.permanent (Matrix.of fun i j => X (Fin.succ i) (Fin.succ j))

end Qatlib.Foundations.MatrixAlgebra.Permanent
