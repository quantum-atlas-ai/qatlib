/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Prod

/-!
# Splitting a qubit register by its support

The equivalence `split S` separates the ordered coordinates in a wire set `S` from its
complement. The maps `mask`, `outside`, `merge`, and `fill` describe this separation explicitly
and give an entrywise characterization of `partitionLift`. For background, see
[KitaevShenVyalyi2002].

## Main statements

* `merge_mask_outside`: recombining the two coordinate restrictions recovers the register.
* `partitionLift_apply`: local matrix entries with equality enforced outside the support.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open Qatlib  Matrix
open scoped Classical BigOperators Kronecker
set_option autoImplicit false

/-- Boolean assignments to the wires outside the finite support set `S`. -/
abbrev Outside (N : ℕ) (S : Finset (Fin N)) := {i : Fin N // i∉S} → Bool

/-- The increasing embedding enumerating the wires in `S` by `Fin S.card`. -/
def wireEmbedding {N : ℕ} (S : Finset (Fin N)) : Fin S.card ↪ Fin N :=
  (S.orderEmbOfFin rfl).toEmbedding

/-- The equivalence identifying Boolean assignments on `S` with a register in increasing wire
order. -/
def orderedCoordinates {N : ℕ} (S : Finset (Fin N)) :
    (S→Bool) ≃ Reg S.card :=
  let o : Fin S.card ≃ S := (S.orderIsoOfFin rfl).toEquiv
  { toFun := fun f j => f (o j)
    invFun := fun u i => u (o.symm i)
    left_inv := by
      intro f
      funext i
      exact congrArg f (o.apply_symm_apply i)
    right_inv := by
      intro u
      funext j
      exact congrArg u (o.symm_apply_apply j) }

/-- The equivalence separating a register into its ordered coordinates on `S` and its
coordinates outside `S`. -/
def split {N : ℕ} (S : Finset (Fin N)) :
    Reg N ≃ Reg S.card × Outside N S :=
  (Equiv.piEquivPiSubtypeProd (fun i : Fin N => i∈S) (fun _ => Bool)).trans
    (Equiv.prodCongr (orderedCoordinates S) (Equiv.refl (Outside N S)))

/-- The restriction of a register to the wires in `S`, listed in increasing order. -/
def mask {N : ℕ} (S : Finset (Fin N)) (x : Reg N) : Reg S.card :=
  fun j => x (wireEmbedding S j)

/-- The restriction of a register to the complement of `S`. -/
def outside {N : ℕ} (S : Finset (Fin N)) (x : Reg N) : Outside N S :=
  fun i => x i

/-- The register obtained by combining ordered support coordinates with complementary
coordinates. -/
def merge {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) : Reg N :=
  (split S).symm (u,v)

/-- Splitting a register returns its `mask` and `outside` restrictions. -/
theorem split_apply {N : ℕ} (S : Finset (Fin N)) (x : Reg N) :
    split S x=(mask S x,outside S x) := rfl

/-- A merged register uses the ordered support value on `S` and the supplied complementary value
off `S`. -/
theorem merge_apply {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) (i : Fin N) :
    merge S u v i = if h:i∈S then
      u ((S.orderIsoOfFin rfl).symm ⟨i,h⟩) else v ⟨i,h⟩ := rfl

/-- Restricting a merged register to `S` recovers its ordered support coordinates. -/
theorem mask_merge {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) : mask S (merge S u v)=u := by
  exact congrArg Prod.fst ((split S).apply_symm_apply (u,v))

/-- Restricting a merged register outside `S` recovers its complementary coordinates. -/
theorem outside_merge {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) : outside S (merge S u v)=v := by
  exact congrArg Prod.snd ((split S).apply_symm_apply (u,v))

/-- Merging the support and complementary restrictions of a register recovers that register. -/
theorem merge_mask_outside {N : ℕ} (S : Finset (Fin N)) (x : Reg N) :
    merge S (mask S x) (outside S x)=x :=
  (split S).symm_apply_apply x

/-- Two complementary restrictions are equal exactly when the registers agree at every wire
outside `S`. -/
theorem outside_eq_iff {N : ℕ} (S : Finset (Fin N)) (x y : Reg N) :
    outside S x=outside S y ↔ ∀i : Fin N,i∉S → x i=y i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i,hi⟩
  · intro h
    funext i
    exact h i i.property

/-- The register extending ordered support coordinates by false on every wire outside `S`. -/
def fill {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card) : Reg N :=
  merge S u (fun _ => false)

/-- Restricting `fill S u` to its support recovers `u`. -/
theorem mask_fill {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card) :
    mask S (fill S u)=u := mask_merge S u _

/-- The complementary restriction of `fill S u` is constantly false. -/
theorem outside_fill {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card) :
    outside S (fill S u)=(fun _ => false) := outside_merge S u _

/-- Filling the support restriction of a register preserves its values on `S`. -/
theorem fill_mask_on {N : ℕ} (S : Finset (Fin N)) (x : Reg N)
    (i : Fin N) (hi : i∈S) : fill S (mask S x) i=x i := by
  change merge S (mask S x) (fun _ => false) i=x i
  rw [merge_apply,dif_pos hi]
  exact congrArg x (congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩))

/-- A filled register has value false at every wire outside `S`. -/
theorem fill_off {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card)
    (i : Fin N) (hi : i∉S) : fill S u i=false := by
  change merge S u (fun _ => false) i=false
  rw [merge_apply,dif_neg hi]

/-- A lifted matrix has local entry `M (mask S x) (mask S y)` when the complementary coordinates
agree, and zero otherwise. -/
theorem partitionLift_apply {N : ℕ} (S : Finset (Fin N))
    (M : Matrix (Reg S.card) (Reg S.card) ℂ) (x y : Reg N) :
    partitionLift (split S) M x y =
      if outside S x=outside S y then M (mask S x) (mask S y) else 0 := by
  simp only [partitionLift,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_symm,Matrix.kronecker_apply,Matrix.one_apply,split_apply]
  split_ifs <;> simp_all

/-- A matrix with the stated local-entry formula equals the corresponding partition lift. -/
theorem eq_partitionLift_of_entries {N : ℕ} (S : Finset (Fin N))
    (H : Matrix (Reg N) (Reg N) ℂ)
    (M : Matrix (Reg S.card) (Reg S.card) ℂ)
    (h : ∀x y,H x y = if outside S x=outside S y
      then M (mask S x) (mask S y) else 0) :
    H=partitionLift (split S) M := by
  ext x y
  rw [partitionLift_apply]
  exact h x y

end Qatlib.Concepts.TensorRegisters.RegisterModel
