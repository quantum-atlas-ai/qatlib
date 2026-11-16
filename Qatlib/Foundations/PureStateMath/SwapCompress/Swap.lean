/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section


/-!
# The compression identities in Reichardt's Lemma 9.7

These are the two matrix identities from the beginning of Lemma 9.7 of
arXiv:0904.2759v1. They do not assert the separate walk-oracle identity or
an implementation of the query algorithm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open Matrix

namespace Qatlib.Foundations.PureStateMath.SwapCompress

/-- The source embedding places the vector indexed by `v` in the `v` row block. -/
def szegedyT {V : Type} [DecidableEq V] (φ : V → V → ℂ) :
    Matrix (V × V) V ℂ :=
  fun p v => if p.1 = v then φ v p.2 else 0

/-- The source swap exchanges the two vertex coordinates. -/
def szegedyS (V : Type) [DecidableEq V] : Matrix (V × V) (V × V) ℂ :=
  fun p q => if p = (q.2, q.1) then 1 else 0

/-- The source compressed swap is `Tᴴ S T`. -/
def szegedyM {V : Type} [Fintype V] [DecidableEq V] (φ : V → V → ℂ) :
    Matrix V V ℂ :=
  (szegedyT φ)ᴴ * (szegedyS V * szegedyT φ)

/-- Each entry of the compressed swap is the actual pair of source amplitudes. -/
theorem swapEntry {V : Type} [Fintype V] [DecidableEq V]
    (φ : V → V → ℂ) (v w : V) :
    szegedyM φ v w = star (φ v w) * φ w v := by
  simp [szegedyM, szegedyT, szegedyS, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and, apply_ite, ite_mul]

end Qatlib.Foundations.PureStateMath.SwapCompress
