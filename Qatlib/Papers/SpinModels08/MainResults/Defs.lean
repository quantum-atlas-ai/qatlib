/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults

abbrev Config (q N : ℕ) := Fin N → Fin q

abbrev QWeight (q : ℕ) := Fin q → Fin q → Fin q → Fin q → ℂ

def basisVec {q N : ℕ} (L : Config q N) : Config q N → ℂ := fun x => if x = L then 1 else 0

def matElem {q N : ℕ} (M : Matrix (Config q N) (Config q N) ℂ) (L R : Config q N) : ℂ :=
  ∑ a, ∑ b, basisVec L a * M a b * basisVec R b

theorem matElem_eq_apply {q N : ℕ} (M : Matrix (Config q N) (Config q N) ℂ) (L R : Config q N) :
    matElem M L R = M L R := by
  simp [matElem, basisVec]

def IsUnitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  Uᴴ * U = 1

def twoLocalGate {q : ℕ} (w : QWeight q) : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ :=
  fun (i, j) (k, l) => w i j k l

theorem twoLocalGate_apply {q : ℕ} (w : QWeight q) (i j k l : Fin q) :
    twoLocalGate w (i, j) (k, l) = w i j k l := rfl

theorem one_apply_config {q N : ℕ} (L R : Config q N) :
    (1 : Matrix (Config q N) (Config q N) ℂ) L R = if L = R then 1 else 0 :=
  Matrix.one_apply

end Qatlib.Papers.SpinModels08.MainResults
