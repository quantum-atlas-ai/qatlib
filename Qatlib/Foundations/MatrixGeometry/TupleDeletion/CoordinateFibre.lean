/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.Incidence
import Mathlib.Logic.Embedding.Set
import Mathlib.Data.Fintype.Card

/-!
# Coordinate fibers of injective tuples

Identifies a fiber of coordinate deletion with the labels absent from the remaining coordinates.
The equivalence `coordinateFibreEquiv` computes its cardinality, and the matrix `coordinateGram`
satisfies a scaled square identity; summing these matrices gives the full deletion Gram matrix.
See [MagniezZur2026] for related background.

## Main statements

* `coordinate_fibre_card`: The deletion fiber at `i` has cardinality `Fintype.card L -
  Fintype.card (Off I i)`.
* `deletion_gram_coordinates`: The deletion Gram matrix is the sum of the coordinate Gram
  matrices.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

/-- The subtype of labels not used by the tuple after coordinate `i` is deleted. -/
abbrev Available (i : I) (u : InjectiveTuple I L) := {z : L // z ∉ Set.range (eraseTuple i u)}

/-- The injective tuple obtained by replacing coordinate `i` of `u` with an available label. -/
def completeCoordinate (i : I) (u : InjectiveTuple I L) (z : Available i u) : InjectiveTuple I L where
  toFun := Function.update u i z.1
  inj' a b hab := by
    by_cases ha : a=i
    · subst a
      by_cases hb : b=i
      · exact hb.symm
      · rw [Function.update_self,Function.update_of_ne hb] at hab
        exact False.elim (z.2 ⟨⟨b,hb⟩,hab.symm⟩)
    · by_cases hb : b=i
      · subst b
        rw [Function.update_of_ne ha,Function.update_self] at hab
        exact False.elim (z.2 ⟨⟨a,ha⟩,hab⟩)
      · rw [Function.update_of_ne ha,Function.update_of_ne hb] at hab
        exact u.injective hab
omit [Fintype I] [Fintype L] in

/-- Replacing coordinate `i` with an available label leaves the tuple obtained by deleting `i`
unchanged. -/
theorem erase_complete (i : I) (u : InjectiveTuple I L) (z : Available i u) :
    eraseTuple i (completeCoordinate i u z)=eraseTuple i u := by
  apply Function.Embedding.ext
  intro j
  exact Function.update_of_ne j.2 _ _

/-- The equivalence between injective tuples with the same deletion at `i` as `u` and labels
available at that coordinate. -/
def coordinateFibreEquiv (i : I) (u : InjectiveTuple I L) :
    {v : InjectiveTuple I L // eraseTuple i v=eraseTuple i u} ≃ Available i u where
  toFun v := ⟨v.1 i,by
    rintro ⟨j,hj⟩
    have he : v.1 j=u j := (eraseTuple_eq_iff i v.1 u).mp v.2 j j.2
    have hij : (j : I)=i := v.1.injective (he.trans hj)
    exact j.2 hij⟩
  invFun z := ⟨completeCoordinate i u z,erase_complete i u z⟩
  left_inv v := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    by_cases hj : j=i
    · subst j
      change Function.update (u : I → L) i (v.1 i) i=v.1 i
      exact Function.update_self i (v.1 i) (u : I → L)
    · change Function.update u i (v.1 i) j=v.1 j
      rw [Function.update_of_ne hj]
      exact ((eraseTuple_eq_iff i v.1 u).mp v.2 j hj).symm
  right_inv z := by
    apply Subtype.ext
    change Function.update (u : I → L) i z.1 i=z.1
    exact Function.update_self i z.1 (u : I → L)

/-- The deletion fiber at `i` has cardinality `Fintype.card L - Fintype.card (Off I i)`. -/
theorem coordinate_fibre_card (i : I) (u : InjectiveTuple I L) :
    Fintype.card {v : InjectiveTuple I L // eraseTuple i v=eraseTuple i u}=
      Fintype.card L-Fintype.card (Off I i) := by
  rw [Fintype.card_congr (coordinateFibreEquiv i u)]
  change Fintype.card {z : L // ¬ z ∈ Set.range (eraseTuple i u)}=_
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_range]

/-- The matrix with entry one exactly when two injective tuples agree after deleting coordinate
`i`, and zero otherwise. -/
def coordinateGram (i : I) : Matrix (InjectiveTuple I L) (InjectiveTuple I L) ℂ :=
  fun u v => if eraseTuple i u=eraseTuple i v then 1 else 0

/-- The coordinate Gram matrix squared equals itself scaled by the complex cast of the
coordinate-fiber cardinality `Fintype.card L - Fintype.card (Off I i)`. -/
theorem coordinateGram_squared (i : I) :
    coordinateGram (L := L) i*coordinateGram (L := L) i=
      ((Fintype.card L-Fintype.card (Off I i) : ℕ) : ℂ) • coordinateGram (L := L) i := by
  ext u v
  change (∑ z : InjectiveTuple I L,(if eraseTuple i u=eraseTuple i z then (1 : ℂ) else 0)*
    (if eraseTuple i z=eraseTuple i v then 1 else 0))=_
  by_cases huv : eraseTuple i u=eraseTuple i v
  · have hs : (∑ z : InjectiveTuple I L,(if eraseTuple i u=eraseTuple i z then (1 : ℂ) else 0)*
        (if eraseTuple i z=eraseTuple i v then 1 else 0))=
        (Fintype.card {z : InjectiveTuple I L // eraseTuple i z=eraseTuple i u} : ℂ) := by
      simp_rw [← huv]
      have he (z : InjectiveTuple I L) :
          (if eraseTuple i u=eraseTuple i z then (1 : ℂ) else 0)*
          (if eraseTuple i z=eraseTuple i u then 1 else 0)=
          if eraseTuple i z=eraseTuple i u then 1 else 0 := by
        by_cases h : eraseTuple i z=eraseTuple i u <;> simp [h,Ne.symm]
      simp_rw [he]
      simp [Fintype.card_subtype]
    rw [hs,coordinate_fibre_card]
    simp [coordinateGram,huv]
  · have hs : ∀ z : InjectiveTuple I L,
        (if eraseTuple i u=eraseTuple i z then (1 : ℂ) else 0)*
        (if eraseTuple i z=eraseTuple i v then 1 else 0)=0 := by
      intro z
      by_cases huz : eraseTuple i u=eraseTuple i z
      · have hzv : eraseTuple i z ≠ eraseTuple i v := fun hz => huv (huz.trans hz)
        simp [huz,hzv]
      · simp [huz]
    simp [hs,coordinateGram,huv]

/-- The deletion Gram matrix is the sum of the coordinate Gram matrices. -/
theorem deletion_gram_coordinates :
    (deletion (I := I) (L := L))ᴴ*deletion=∑ i : I,coordinateGram (L := L) i := by
  ext u v
  rw [deletion_gram_entry]
  simp only [Matrix.sum_apply,coordinateGram]
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
