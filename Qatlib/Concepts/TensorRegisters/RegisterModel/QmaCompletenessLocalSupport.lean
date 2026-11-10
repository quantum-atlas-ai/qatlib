/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Prod
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open Qatlib  Matrix
open scoped Classical BigOperators Kronecker
set_option autoImplicit false

abbrev Outside (N : ℕ) (S : Finset (Fin N)) := {i : Fin N // i∉S} → Bool

def wireEmbedding {N : ℕ} (S : Finset (Fin N)) : Fin S.card ↪ Fin N :=
  (S.orderEmbOfFin rfl).toEmbedding

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

def split {N : ℕ} (S : Finset (Fin N)) :
    Reg N ≃ Reg S.card × Outside N S :=
  (Equiv.piEquivPiSubtypeProd (fun i : Fin N => i∈S) (fun _ => Bool)).trans
    (Equiv.prodCongr (orderedCoordinates S) (Equiv.refl (Outside N S)))

def mask {N : ℕ} (S : Finset (Fin N)) (x : Reg N) : Reg S.card :=
  fun j => x (wireEmbedding S j)

def outside {N : ℕ} (S : Finset (Fin N)) (x : Reg N) : Outside N S :=
  fun i => x i

def merge {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) : Reg N :=
  (split S).symm (u,v)

theorem split_apply {N : ℕ} (S : Finset (Fin N)) (x : Reg N) :
    split S x=(mask S x,outside S x) := rfl

theorem merge_apply {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) (i : Fin N) :
    merge S u v i = if h:i∈S then
      u ((S.orderIsoOfFin rfl).symm ⟨i,h⟩) else v ⟨i,h⟩ := rfl

theorem mask_merge {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) : mask S (merge S u v)=u := by
  exact congrArg Prod.fst ((split S).apply_symm_apply (u,v))

theorem outside_merge {N : ℕ} (S : Finset (Fin N))
    (u : Reg S.card) (v : Outside N S) : outside S (merge S u v)=v := by
  exact congrArg Prod.snd ((split S).apply_symm_apply (u,v))

theorem merge_mask_outside {N : ℕ} (S : Finset (Fin N)) (x : Reg N) :
    merge S (mask S x) (outside S x)=x :=
  (split S).symm_apply_apply x

theorem outside_eq_iff {N : ℕ} (S : Finset (Fin N)) (x y : Reg N) :
    outside S x=outside S y ↔ ∀i : Fin N,i∉S → x i=y i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i,hi⟩
  · intro h
    funext i
    exact h i i.property

def fill {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card) : Reg N :=
  merge S u (fun _ => false)

theorem mask_fill {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card) :
    mask S (fill S u)=u := mask_merge S u _

theorem outside_fill {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card) :
    outside S (fill S u)=(fun _ => false) := outside_merge S u _

theorem fill_mask_on {N : ℕ} (S : Finset (Fin N)) (x : Reg N)
    (i : Fin N) (hi : i∈S) : fill S (mask S x) i=x i := by
  change merge S (mask S x) (fun _ => false) i=x i
  rw [merge_apply,dif_pos hi]
  exact congrArg x (congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩))

theorem fill_off {N : ℕ} (S : Finset (Fin N)) (u : Reg S.card)
    (i : Fin N) (hi : i∉S) : fill S u i=false := by
  change merge S u (fun _ => false) i=false
  rw [merge_apply,dif_neg hi]

theorem partitionLift_apply {N : ℕ} (S : Finset (Fin N))
    (M : Matrix (Reg S.card) (Reg S.card) ℂ) (x y : Reg N) :
    partitionLift (split S) M x y =
      if outside S x=outside S y then M (mask S x) (mask S y) else 0 := by
  simp only [partitionLift,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_symm,Matrix.kronecker_apply,Matrix.one_apply,split_apply]
  split_ifs <;> simp_all

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
