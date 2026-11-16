/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.GurvitsBarnumCore
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.UnitaryResolution
public import Qatlib.Foundations.PPTMatrix.OperatorCones.GurvitsBarnumSVD

@[expose] public section




/-!
# Lemma 2 (Gurvits–Barnum): equal diagonal blocks imply separability

Every positive operator `[[D, Y], [Yᴴ, D]]` on a qubit and a finite-dimensional system is
separable. The proof normalizes on the support of `D`, applies the same-space SVD
two-unitary formula, and uses the orthonormal unitary eigenbasis product identity.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

/-- **Lemma 2** (Gurvits–Barnum 2002, Proposition 1). -/
theorem isSeparable_qubitBlocks_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (D Y : Matrix n n ℂ) (h : (qubitBlocks D Y Yᴴ D).PosSemidef) :
    IsSeparable (qubitBlocks D Y Yᴴ D) :=
  ManuscriptGB.isSeparable_equal_diagonal_by_svd_and_eigenbasis D Y h

end Qatlib.Foundations.PPTMatrix.OperatorCones
