/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Diagonal

/-!
# Permutation invariance of unitary digraphs

This module proves that unitary realizability is invariant under `PermEquivalentTo`. The
equivalence `lemma2` formalizes Lemma 2 of [Severini2003], allowing unitary realizations and
obstructions to be transported between permutation-equivalent digraphs.

## Main statements

* `permEquiv_unitary_forward`: Transport a unitary realization along permutation equivalence.
* `lemma2`: Unitary realizability is equivalent for permutation-equivalent digraphs.

## References

* [Severini, 2003][Severini2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Permutation

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Matrix

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Unitary realizability transfers from `D` to a permutation-equivalent digraph `D'`
[Severini2003]. -/
theorem permEquiv_unitary_forward {D : Digraph V} {D' : Digraph W}
    (h : PermEquivalentTo D D') (hD : IsUnitaryDigraph D) : IsUnitaryDigraph D' := by
  obtain ⟨U, hU, hpat⟩ := hD
  obtain ⟨σ, τ, hadj⟩ := h

  have hrow : ∀ a c : V, (∑ j : V, U a j * star (U c j)) = if a = c then 1 else 0 := by
    intro a c
    have h1 : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
    have h2 := congrFun (congrFun h1 a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    simpa only [Matrix.star_apply] using h2
  refine ⟨fun a b => U (σ.symm a) (τ.symm b), ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.star_apply]
    change (∑ x : W, U (σ.symm a) (τ.symm x) * star (U (σ.symm c) (τ.symm x)))
        = (if a = c then 1 else 0)
    have hreindex :
        (∑ x : W, U (σ.symm a) (τ.symm x) * star (U (σ.symm c) (τ.symm x)))
          = ∑ y : V, U (σ.symm a) y * star (U (σ.symm c) y) :=
      Fintype.sum_equiv τ.symm
        (fun x => U (σ.symm a) (τ.symm x) * star (U (σ.symm c) (τ.symm x)))
        (fun y => U (σ.symm a) y * star (U (σ.symm c) y))
        (fun x => rfl)
    rw [hreindex, hrow]
    by_cases hac : a = c
    · subst hac; simp
    · have : σ.symm a ≠ σ.symm c := fun hh => hac (σ.symm.injective hh)
      simp [hac, this]
  · intro a b
    change U (σ.symm a) (τ.symm b) ≠ 0 ↔ D'.Adj a b
    have hpat' : U (σ.symm a) (τ.symm b) ≠ 0 ↔ D.Adj (σ.symm a) (τ.symm b) :=
      hpat (σ.symm a) (τ.symm b)
    have hadj' : D.Adj (σ.symm a) (τ.symm b) ↔ D'.Adj a b := by
      simpa [σ.apply_symm_apply, τ.apply_symm_apply] using
        (hadj (σ.symm a) (τ.symm b)).symm
    exact hpat'.trans hadj'

/-- Permutation-equivalent digraphs are either both unitary digraphs or both fail to be unitary
digraphs [Severini2003]. -/
theorem lemma2 {D : Digraph V} {D' : Digraph W} (h : PermEquivalentTo D D') :
    (IsUnitaryDigraph D ↔ IsUnitaryDigraph D') := by
  constructor
  · exact permEquiv_unitary_forward h
  · obtain ⟨σ, τ, hadj⟩ := h
    refine permEquiv_unitary_forward ⟨σ.symm, τ.symm, ?_⟩
    intro i j
    have := hadj (σ.symm i) (τ.symm j)
    simpa [σ.apply_symm_apply, τ.apply_symm_apply] using this.symm

end Qatlib.Papers.UnitaryDigraph.MainResults.Permutation
