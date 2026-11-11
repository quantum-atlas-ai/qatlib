/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.Incidence
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A bottom eigenvector for tuple adjacency

Counts injective tuples and deletion rows using descending factorials. If `I` is nonempty and `2
* Fintype.card I ≤ Fintype.card L`, the deletion matrix has fewer rows than columns, producing a
nonzero adjacency eigenvector with eigenvalue `-Fintype.card I`. See [MagniezZur2026] for
related background.

## Main statements

* `deletion_dimension_lt`: If `I` is nonempty and the label cardinality is at least twice the
  coordinate cardinality, there are strictly fewer deletion rows than injective tuples.
* `exists_bottom_eigenvector`: If `I` is nonempty and `2 * Fintype.card I ≤ Fintype.card L`,
  injective-tuple adjacency has a nonzero eigenvector with eigenvalue `-Fintype.card I`.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix Module
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

/-- Deleting one coordinate leaves `Fintype.card I - 1` coordinates. -/
theorem off_card (i : I) : Fintype.card (Off I i)=Fintype.card I-1 := by
  simp [Off,Fintype.card_subtype_compl]

/-- The number of injective tuples is the descending factorial `(Fintype.card L).descFactorial
(Fintype.card I)`. -/
theorem injectiveTuple_card : Fintype.card (InjectiveTuple I L)=(Fintype.card L).descFactorial (Fintype.card I) :=
  Fintype.card_embedding_eq

/-- The number of deletion rows is `Fintype.card I * (Fintype.card L).descFactorial
(Fintype.card I - 1)`. -/
theorem deletionRow_card :
    Fintype.card (DeletionRow I L)=Fintype.card I*(Fintype.card L).descFactorial (Fintype.card I-1) := by
  simp [DeletionRow]

/-- If `I` is nonempty and the label cardinality is at least twice the coordinate cardinality,
there are strictly fewer deletion rows than injective tuples. -/
theorem deletion_dimension_lt (hs : 0 < Fintype.card I) (hN : 2*Fintype.card I ≤ Fintype.card L) :
    Fintype.card (DeletionRow I L)<Fintype.card (InjectiveTuple I L) := by
  rw [deletionRow_card,injectiveTuple_card]
  have he : Fintype.card I=Fintype.card I-1+1 := by omega
  conv_rhs => rw [he,Nat.descFactorial_succ]
  apply Nat.mul_lt_mul_of_pos_right
  · omega
  · apply Nat.descFactorial_pos.mpr
    omega

/-- If `I` is nonempty and `2 * Fintype.card I ≤ Fintype.card L`, injective-tuple adjacency has
a nonzero eigenvector with eigenvalue `-Fintype.card I`. -/
theorem exists_bottom_eigenvector (hs : 0 < Fintype.card I) (hN : 2*Fintype.card I ≤ Fintype.card L) :
    ∃ v : InjectiveTuple I L → ℂ, v ≠ 0 ∧ adjacency *ᵥ v=(-(Fintype.card I : ℂ)) • v := by
  have hK : (deletion (I := I) (L := L)).mulVecLin.ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa only [Module.finrank_pi,Module.finrank_self,mul_one] using deletion_dimension_lt hs hN
  obtain ⟨v,hv,hnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  refine ⟨v,hnz,?_⟩
  have hz : (adjacency (I := I) (L := L)+(Fintype.card I : ℂ) • 1)*ᵥ v=0 := by
    have he : v ∈ (adjacency (I := I) (L := L)+(Fintype.card I : ℂ) • 1).mulVecLin.ker := by
      rw [shifted_adjacency_kernel]
      exact hv
    exact he
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at hz
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hz
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
