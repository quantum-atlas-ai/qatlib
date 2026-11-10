/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

abbrev InjectiveTuple (I L : Type*) := I ↪ L

abbrev Off (I : Type*) (i : I) := {j : I // j ≠ i}

def eraseTuple (i : I) (y : InjectiveTuple I L) : Off I i ↪ L where
  toFun j := y j
  inj' _ _ h := Subtype.ext (y.injective h)

abbrev DeletionRow (I L : Type*) := Σ i : I, Off I i ↪ L

def deletion : Matrix (DeletionRow I L) (InjectiveTuple I L) ℂ :=
  fun row y => if eraseTuple row.1 y=row.2 then 1 else 0
omit [Fintype I] [Fintype L] in

theorem eraseTuple_eq_iff (i : I) (u v : InjectiveTuple I L) :
    eraseTuple i u=eraseTuple i v ↔ ∀ j, j ≠ i → u j=v j := by
  constructor
  · intro he j hj
    exact congrArg (fun f : Off I i ↪ L => f ⟨j,hj⟩) he
  · intro he
    apply Function.Embedding.ext
    intro j
    exact he j j.2

def adjacency : Matrix (InjectiveTuple I L) (InjectiveTuple I L) ℂ :=
  fun u v => if u ≠ v ∧ ∃ i, eraseTuple i u=eraseTuple i v then 1 else 0
omit [Fintype L] in

theorem deletion_entry (i : I) (z : Off I i ↪ L) (u : InjectiveTuple I L) :
    deletion ⟨i,z⟩ u=if eraseTuple i u=z then 1 else 0 := rfl

theorem deletion_gram_entry (u v : InjectiveTuple I L) :
    (((deletion (I := I) (L := L))ᴴ*deletion) : Matrix (InjectiveTuple I L) (InjectiveTuple I L) ℂ) u v =
      ∑ i : I, if eraseTuple i u=eraseTuple i v then (1 : ℂ) else 0 := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sigma,deletion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (eraseTuple i u)]
  · simp [eq_comm]
  · intro z hz hne
    simp [Ne.symm hne]
  · simp
omit [Fintype I] [Fintype L] in

theorem erase_unique (u v : InjectiveTuple I L) (huv : u ≠ v) (i j : I)
    (hi : eraseTuple i u=eraseTuple i v) (hj : eraseTuple j u=eraseTuple j v) : i=j := by
  by_contra hne
  apply huv
  apply Function.Embedding.ext
  intro k
  by_cases hk : k=i
  · subst k
    exact (eraseTuple_eq_iff j u v).mp hj i hne
  · exact (eraseTuple_eq_iff i u v).mp hi k hk

theorem deletion_gram :
    (deletion (I := I) (L := L))ᴴ*deletion=adjacency+(Fintype.card I : ℂ) • 1 := by
  ext u v
  rw [deletion_gram_entry]
  by_cases huv : u=v
  · subst v
    simp [adjacency]
  · by_cases he : ∃ i, eraseTuple i u=eraseTuple i v
    · obtain ⟨i,hi⟩ := he
      have hex : ∃ i, eraseTuple i u=eraseTuple i v := ⟨i,hi⟩
      rw [Finset.sum_eq_single i]
      · simp [hi,adjacency,huv,hex]
      · intro j hj hji
        have hn : eraseTuple j u ≠ eraseTuple j v := fun h => hji (erase_unique u v huv j i h hi)
        simp [hn]
      · simp
    · have hn (i : I) : eraseTuple i u ≠ eraseTuple i v := fun h => he ⟨i,h⟩
      simp [hn,adjacency,huv]

theorem shifted_adjacency_psd :
    (adjacency (I := I) (L := L)+(Fintype.card I : ℂ) • 1).PosSemidef := by
  rw [← deletion_gram]
  exact posSemidef_conjTranspose_mul_self deletion

theorem shifted_adjacency_kernel :
    (adjacency (I := I) (L := L)+(Fintype.card I : ℂ) • 1).mulVecLin.ker=deletion.mulVecLin.ker := by
  rw [← deletion_gram]
  exact ker_mulVecLin_conjTranspose_mul_self deletion
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
