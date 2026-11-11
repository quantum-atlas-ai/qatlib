/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin

/-!
# Configurations and local weights for spin models

This module defines finite spin configurations, computational basis vectors, and matrix elements
for the circuit representation of spin models in [VanDenNestEtAl2009]. The four-index weights in
`QWeight` are packaged as two-site matrices by `twoLocalGate`, and `IsUnitary` records the
conjugate-transpose identity.

## Main statements

* `matElem_eq_apply`: computational basis matrix elements equal matrix entries.
* `twoLocalGate_apply`: local gate entries recover the supplied vertex weights.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults

/-- Configurations of `N` sites, each taking one of `q` spin values. -/
abbrev Config (q N : ℕ) := Fin N → Fin q

/-- Complex vertex weights indexed by four `q`-valued spins. -/
abbrev QWeight (q : ℕ) := Fin q → Fin q → Fin q → Fin q → ℂ

/-- The computational basis vector supported at the configuration `L`. -/
def basisVec {q N : ℕ} (L : Config q N) : Config q N → ℂ := fun x => if x = L then 1 else 0

/-- The matrix element between the computational basis vectors indexed by `L` and `R`. -/
def matElem {q N : ℕ} (M : Matrix (Config q N) (Config q N) ℂ) (L R : Config q N) : ℂ :=
  ∑ a, ∑ b, basisVec L a * M a b * basisVec R b

/-- A computational basis matrix element is the corresponding matrix entry. -/
theorem matElem_eq_apply {q N : ℕ} (M : Matrix (Config q N) (Config q N) ℂ) (L R : Config q N) :
    matElem M L R = M L R := by
  simp [matElem, basisVec]

/-- The condition `Uᴴ * U = 1` for a finite complex square matrix. -/
def IsUnitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  Uᴴ * U = 1

/-- The two-site matrix whose entries are the four-index weights `w`. -/
def twoLocalGate {q : ℕ} (w : QWeight q) : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ :=
  fun (i, j) (k, l) => w i j k l

/-- The entry of `twoLocalGate w` at the paired indices is `w i j k l`. -/
theorem twoLocalGate_apply {q : ℕ} (w : QWeight q) (i j k l : Fin q) :
    twoLocalGate w (i, j) (k, l) = w i j k l := rfl

/-- The identity matrix on configurations has diagonal entries one and off-diagonal entries
zero. -/
theorem one_apply_config {q N : ℕ} (L R : Config q N) :
    (1 : Matrix (Config q N) (Config q N) ℂ) L R = if L = R then 1 else 0 :=
  Matrix.one_apply

end Qatlib.Papers.SpinModels08.MainResults
