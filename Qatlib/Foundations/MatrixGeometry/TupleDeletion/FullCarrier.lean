/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.Incidence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Prod
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
open Matrix Module
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

abbrev TupleHilbert (I L : Type*) [Fintype I] [Fintype L] := EuclideanSpace ℂ (I → L)

theorem tupleHilbert_dimension : finrank ℂ (TupleHilbert I L)=Fintype.card L^Fintype.card I := by
  simp [TupleHilbert,finrank_euclideanSpace]

def embeddingSubtype : InjectiveTuple I L ≃ {y : I → L // Function.Injective y} where
  toFun y := ⟨y,y.injective⟩
  invFun y := ⟨y.1,y.2⟩
  left_inv y := by cases y;rfl
  right_inv y := by cases y;rfl

def extend {K : Type*} [Zero K] (v : InjectiveTuple I L → K) (y : I → L) : K :=
  if h : Function.Injective y then v ⟨y,h⟩ else 0
omit [Fintype L] in

theorem extend_injective {K : Type*} [Zero K] (v : InjectiveTuple I L → K) (y : InjectiveTuple I L) :
    extend v y=v y := by
  cases y with
  | mk f hf =>
    change (if h : Function.Injective f then v ⟨f,h⟩ else 0)=v ⟨f,hf⟩
    rw [dif_pos hf]

theorem sum_extend {K : Type*} [AddCommMonoid K] (v : InjectiveTuple I L → K) :
    ∑ y : I → L, extend v y=∑ u : InjectiveTuple I L,v u := by
  let e := embeddingSubtype (I := I) (L := L)
  letI : Fintype {y : I → L // Function.Injective y} := Fintype.ofEquiv (InjectiveTuple I L) e
  have he : (∑ u : InjectiveTuple I L,v u)=∑ y : {y : I → L // Function.Injective y},extend v y.1 := by
    apply Fintype.sum_equiv e
    intro u
    exact (extend_injective v u).symm
  rw [he]
  have hf := Finset.sum_subtype (F := inferInstance) (p := fun y : I → L => Function.Injective y)
    (Finset.univ.filter (fun y : I → L => Function.Injective y)) (by simp) (fun y => extend v y)
  rw [← hf,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : Function.Injective y <;> simp [extend,h]

theorem extend_norm (v : InjectiveTuple I L → ℂ) :
    ‖WithLp.toLp 2 (extend v)‖=‖(WithLp.toLp 2 v : EuclideanSpace ℂ (InjectiveTuple I L))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  have h := sum_extend (fun u : InjectiveTuple I L => ‖v u‖^2)
  convert! h using 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : Function.Injective y <;> simp [extend,h]

abbrev FullRow (I L : Type*) := Σ i : I, Off I i → L

def fullDeletion : Matrix (FullRow I L) (I → L) ℂ :=
  fun row y => if (fun j : Off I row.1 => y j)=row.2 then 1 else 0

def splitCoordinate (i : I) : (I → L) ≃ L × (Off I i → L) := Equiv.piSplitAt i (fun _ => L)

def fibreSum (v : (I → L) → ℂ) (i : I) (z : Off I i → L) : ℂ :=
  ∑ value : L,v ((splitCoordinate i).symm (value,z))

theorem fullDeletion_apply (v : (I → L) → ℂ) (i : I) (z : Off I i → L) :
    (fullDeletion (I := I) (L := L)*ᵥ v) ⟨i,z⟩=fibreSum v i z := by
  change (∑ y : I → L,(if (fun j : Off I i => y j)=z then (1 : ℂ) else 0)*v y)=_
  simp only [ite_mul,one_mul,zero_mul]
  have he := Fintype.sum_equiv (splitCoordinate (L := L) i)
    (fun y : I → L => if (fun j : Off I i => y j)=z then v y else 0)
    (fun p : L × (Off I i → L) => if p.2=z then v ((splitCoordinate i).symm p) else 0)
    (fun y => by (try dsimp only);rw [(splitCoordinate i).symm_apply_apply];rfl)
  rw [he,Fintype.sum_prod_type]
  unfold fibreSum
  apply Finset.sum_congr rfl
  intro value hvalue
  simp

theorem fullDeletion_kernel_iff (v : (I → L) → ℂ) :
    fullDeletion (I := I) (L := L)*ᵥ v=0 ↔ ∀ i z,fibreSum v i z=0 := by
  constructor
  · intro he i z
    rw [← fullDeletion_apply]
    exact congrFun he ⟨i,z⟩
  · intro he
    funext row
    exact (fullDeletion_apply v row.1 row.2).trans (he row.1 row.2)
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
