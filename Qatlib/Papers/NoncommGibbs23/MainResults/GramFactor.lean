/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommGibbs23.MainResults.Model
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

/-- Every finite positive semidefinite complex matrix admits a finite Gram
factor, obtained by taking its positive square root. -/
theorem propositionII3_psdGram {ι : Type*} [Fintype ι]
    (α : Matrix ι ι ℂ) (hα : α.PosSemidef) :
    ∃ (κ : Type) (_ : Fintype κ) (c : κ → ι → ℂ),
      ∀ i j, α i j = ∑ k, star (c k i) * c k j := by
  classical
  let S : Matrix ι ι ℂ := CFC.sqrt α
  let e := Fintype.equivFin ι
  refine ⟨Fin (Fintype.card ι), inferInstance, fun k i => S (e.symm k) i, ?_⟩
  have hs : (CFC.sqrt α)ᴴ = CFC.sqrt α :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg α)).1
  have hm : (CFC.sqrt α)ᴴ * CFC.sqrt α = α := by
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self α hα.nonneg
  intro i j
  have hi : α i j = ∑ k : ι, star (S k i) * S k j := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, S] using
      (congrFun (congrFun hm i) j).symm
  exact hi.trans (e.symm.sum_comp (fun k : ι => star (S k i) * S k j)).symm

end Qatlib.Papers.NoncommGibbs23.MainResults
