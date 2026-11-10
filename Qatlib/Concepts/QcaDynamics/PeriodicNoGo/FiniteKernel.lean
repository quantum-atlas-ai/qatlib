/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.LocalKernel
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

open Qatlib.Concepts.QcaDynamics.ScalarNoGo

namespace Qatlib.Concepts.QcaDynamics.PeriodicNoGo

def finiteKernel {V : Type*} [Sub V] (w : V → ℂ) : Matrix V V ℂ := fun x y => w (y-x)

theorem finiteKernel_gram {V : Type*} [AddCommGroup V] [Fintype V]
    (w : V → ℂ) (x y : V) :
    (finiteKernel w * (finiteKernel w)ᴴ) x y =
      ∑ e : V, w e * star (w (e-(y-x))) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, finiteKernel]
  apply Fintype.sum_equiv (Equiv.subRight x)
  intro z
  simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]

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

theorem finiteKernel_step {V : Type*} [AddCommGroup V] [Fintype V]
    (w φ : V → ℂ) (x : V) :
    (finiteKernel w *ᵥ φ) x = ∑ e : V, w e * φ (x+e) := by
  simp only [Matrix.mulVec, dotProduct, finiteKernel]
  apply Fintype.sum_equiv (Equiv.subRight x)
  intro z
  simp only [Equiv.subRight_apply, add_sub_cancel]

theorem finiteKernel_adjointStep {V : Type*} [AddCommGroup V] [Fintype V]
    (w φ : V → ℂ) (x : V) :
    ((finiteKernel w)ᴴ *ᵥ φ) x = ∑ e : V, star (w e) * φ (x-e) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, finiteKernel]
  apply Fintype.sum_equiv (Equiv.subLeft x)
  intro z
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

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
