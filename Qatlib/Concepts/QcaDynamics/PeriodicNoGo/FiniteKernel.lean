/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.LocalKernel
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic

/-!
# Finite convolution kernels and unitarity

Connects translation invariant matrices on finite abelian groups to autocorrelation equations
for their scalar weights. `finiteKernel_model_iff` identifies matrix unitarity with the
finite-neighborhood condition `Unitary`, while the action lemmas recover the corresponding
convolution update. This supplies finite-group counterparts of the scalar dynamics considered in
[Meyer1996].

## Main statements

* `finiteKernel_unitary_iff`: characterizes unitarity by delta autocorrelation.
* `finiteKernel_model_iff`: relates matrix unitarity to the weight model.
* `finiteKernel_model_step`: identifies matrix action with `step`.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

open Qatlib.Concepts.QcaDynamics.ScalarNoGo

namespace Qatlib.Concepts.QcaDynamics.PeriodicNoGo

/-- The translation invariant matrix whose entry at `(x, y)` is `w (y - x)`. -/
def finiteKernel {V : Type*} [Sub V] (w : V → ℂ) : Matrix V V ℂ := fun x y => w (y-x)

/-- The Gram matrix of `finiteKernel w` is given by weight autocorrelations at displacement `y -
x`. -/
theorem finiteKernel_gram {V : Type*} [AddCommGroup V] [Fintype V]
    (w : V → ℂ) (x y : V) :
    (finiteKernel w * (finiteKernel w)ᴴ) x y =
      ∑ e : V, w e * star (w (e-(y-x))) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, finiteKernel]
  apply Fintype.sum_equiv (Equiv.subRight x)
  intro z
  simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]

/-- A finite convolution kernel is unitary exactly when its weight autocorrelation is one at
zero displacement and zero elsewhere. -/
theorem finiteKernel_unitary_iff {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (w : V → ℂ) :
    finiteKernel w ∈ Matrix.unitaryGroup V ℂ ↔
      ∀ d : V, (∑ e : V, w e * star (w (e-d))) = if d=0 then 1 else 0 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  constructor
  · intro h d
    have hh := congrArg (fun M : Matrix V V ℂ => M 0 d) h
    try dsimp only at hh
    rw [finiteKernel_gram] at hh
    simpa only [sub_zero, Matrix.one_apply, eq_comm] using hh
  · intro h
    ext x y
    rw [finiteKernel_gram, h (y-x)]
    simp only [Matrix.one_apply, sub_eq_zero, eq_comm]

/-- The action of `finiteKernel w` is the sum of `w e * φ (x + e)` over all displacements. -/
theorem finiteKernel_step {V : Type*} [AddCommGroup V] [Fintype V]
    (w φ : V → ℂ) (x : V) :
    (finiteKernel w *ᵥ φ) x = ∑ e : V, w e * φ (x+e) := by
  simp only [Matrix.mulVec, dotProduct, finiteKernel]
  apply Fintype.sum_equiv (Equiv.subRight x)
  intro z
  simp only [Equiv.subRight_apply, add_sub_cancel]

/-- The adjoint kernel acts by summing conjugate weights against `φ (x - e)`. -/
theorem finiteKernel_adjointStep {V : Type*} [AddCommGroup V] [Fintype V]
    (w φ : V → ℂ) (x : V) :
    ((finiteKernel w)ᴴ *ᵥ φ) x = ∑ e : V, star (w e) * φ (x-e) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, finiteKernel]
  apply Fintype.sum_equiv (Equiv.subLeft x)
  intro z
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

/-- If the support of `w` lies in `E`, its full autocorrelation sum can be restricted to `E`. -/
theorem correlation_sum_neighborhood {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (E : Finset V) (w : V → ℂ) (hs : ∀ e,w e ≠ 0 → e∈E) (d : V) :
    (∑ e : V,w e*star (w (e-d))) = ∑ e ∈ E,w e*star (w (e-d)) := by
  symm
  apply Finset.sum_subset (Finset.subset_univ E)
  intro e _ he
  have hw : w e=0 := by
    by_contra hw
    exact he (hs e hw)
  simp only [hw,zero_mul]

/-- Normalization and vanishing nonzero autocorrelations on a finite neighborhood containing the
support imply unitarity of the kernel matrix. -/
theorem finiteKernel_unitary_of_neighborhood {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (E : Finset V) (w : V → ℂ) (hs : ∀ e,w e ≠ 0 → e∈E)
    (hu : (∑e∈E,w e*star (w e))=1 ∧
      ∀d:V,d≠0 → (∑e∈E,w e*star (w (e-d)))=0) :
    finiteKernel w ∈ Matrix.unitaryGroup V ℂ := by
  apply (finiteKernel_unitary_iff w).mpr
  intro d
  rw [correlation_sum_neighborhood E w hs d]
  by_cases hd : d=0
  · subst d
    simpa only [sub_zero,if_pos rfl] using! hu.1
  · simpa only [if_neg hd] using hu.2 d hd

/-- The matrix `finiteKernel A.weight` is unitary exactly when the finite-neighborhood weight
model satisfies `Unitary A`. -/
theorem finiteKernel_model_iff {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (A : Weights V) : finiteKernel A.weight ∈ Matrix.unitaryGroup V ℂ ↔ Unitary A := by
  constructor
  · intro h
    have hu := (finiteKernel_unitary_iff A.weight).mp h
    constructor
    · have h0 := hu 0
      rw [correlation_sum_neighborhood A.neighborhood A.weight A.support 0] at h0
      simpa using h0
    · intro d hd
      have hh := hu d
      rw [correlation_sum_neighborhood A.neighborhood A.weight A.support d] at hh
      simpa [hd] using hh
  · intro h
    exact finiteKernel_unitary_of_neighborhood A.neighborhood A.weight A.support h

/-- Matrix application of `finiteKernel A.weight` agrees with the finite-neighborhood update
`step A`. -/
theorem finiteKernel_model_step {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (A : Weights V) (φ : V → ℂ) (x : V) :
    (finiteKernel A.weight *ᵥ φ) x = step A φ x := by
  rw [finiteKernel_step]
  symm
  apply Finset.sum_subset (Finset.subset_univ A.neighborhood)
  intro e _ he
  have hz : A.weight e = 0 := by
    by_contra h
    exact he (A.support e h)
  simp only [hz, zero_mul]

end Qatlib.Concepts.QcaDynamics.PeriodicNoGo
