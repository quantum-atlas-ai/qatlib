/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.TensorSupport
variable {S : Type*} [Fintype S] [DecidableEq S]

def tensor (A : S→Matrix Bool Bool ℂ) : Matrix (S→Bool) (S→Bool) ℂ :=
  fun x y=>∏i,A i (x i) (y i)

theorem tensor_mul (A B : S→Matrix Bool Bool ℂ) :
    tensor A*tensor B=tensor (fun i=>A i*B i) := by
  ext x y
  change (∑z:S→Bool,(∏i,A i (x i) (z i))*(∏i,B i (z i) (y i)))=
    ∏i,∑b:Bool,A i (x i) b*B i b (y i)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b=>A i (x i) b*B i b (y i))).symm

theorem tensor_commute (A B : S→Matrix Bool Bool ℂ) (h : ∀i,Commute (A i) (B i)) :
    Commute (tensor A) (tensor B) := by
  change tensor A*tensor B=tensor B*tensor A
  rw [tensor_mul,tensor_mul]
  apply congrArg tensor
  funext i
  exact h i

def generators (s : Finset S) : Set (Matrix (S→Bool) (S→Bool) ℂ) :=
  {A|∃f:S→Matrix Bool Bool ℂ,(∀i,i∉s→f i=1) ∧tensor f=A}

def onSupport (s : Finset S) : Subalgebra ℂ (Matrix (S→Bool) (S→Bool) ℂ) :=
  Algebra.adjoin ℂ (generators s)

theorem tensor_mem (s : Finset S) (A : S→Matrix Bool Bool ℂ) (hA : ∀i,i∉s→A i=1) :
    tensor A∈onSupport s := Algebra.subset_adjoin ⟨A,hA,rfl⟩

theorem support_mono {s t : Finset S} (h : s⊆t) : onSupport s≤onSupport t := by
  apply Algebra.adjoin_le
  rintro A ⟨f,hf,rfl⟩
  apply tensor_mem
  intro i hi
  exact hf i (fun hmem=>hi (h hmem))

theorem disjoint_tensor_commute {s t : Finset S} (hst : Disjoint s t)
    (A B : S→Matrix Bool Bool ℂ) (hA : ∀i,i∉s→A i=1) (hB : ∀i,i∉t→B i=1) :
    Commute (tensor A) (tensor B) := by
  apply tensor_commute
  intro i
  by_cases hi:i∈s
  · have hit:i∉t := fun ht=>(Finset.disjoint_left.mp hst) hi ht
    rw [hB i hit]
    exact Commute.one_right _
  · rw [hA i hi]
    exact Commute.one_left _

theorem tensor_commutes_algebra {s t : Finset S} (hst : Disjoint s t)
    (A : S→Matrix Bool Bool ℂ) (hA : ∀i,i∉s→A i=1)
    (B : Matrix (S→Bool) (S→Bool) ℂ) (hB : B∈onSupport t) : Commute (tensor A) B := by
  have hc : onSupport t≤Subalgebra.centralizer ℂ {tensor A} := by
    apply Algebra.adjoin_le
    rintro C ⟨f,hf,rfl⟩
    change ∀ D ∈ ({tensor A} : Set (Matrix (S→Bool) (S→Bool) ℂ)), D*tensor f=tensor f*D
    intro D hD
    have hd : D=tensor A := Set.mem_singleton_iff.mp hD
    subst D
    exact disjoint_tensor_commute hst A f hA hf
  exact ((Subalgebra.mem_centralizer_iff (R:=ℂ)).mp (hc hB)) _ (Set.mem_singleton _)

theorem disjoint_commute {s t : Finset S} (hst : Disjoint s t)
    (A B : Matrix (S→Bool) (S→Bool) ℂ) (hA : A∈onSupport s) (hB : B∈onSupport t) :
    Commute A B := by
  have hc : onSupport s≤Subalgebra.centralizer ℂ {B} := by
    apply Algebra.adjoin_le
    rintro C ⟨f,hf,rfl⟩
    change ∀ D ∈ ({B} : Set (Matrix (S→Bool) (S→Bool) ℂ)), D*tensor f=tensor f*D
    intro D hD
    have hd:D=B := Set.mem_singleton_iff.mp hD
    subst D
    exact (tensor_commutes_algebra hst f hf B hB).symm
  exact (((Subalgebra.mem_centralizer_iff (R:=ℂ)).mp (hc hA)) _ (Set.mem_singleton _)).symm

theorem mul_mem_union {s t : Finset S} (A B : Matrix (S→Bool) (S→Bool) ℂ)
    (hA : A∈onSupport s) (hB : B∈onSupport t) : A*B∈onSupport (s∪t) :=
  (onSupport (s∪t)).mul_mem (support_mono Finset.subset_union_left hA) (support_mono Finset.subset_union_right hB)

theorem commutator_mem_union {s t : Finset S} (A B : Matrix (S→Bool) (S→Bool) ℂ)
    (hA : A∈onSupport s) (hB : B∈onSupport t) : A*B-B*A∈onSupport (s∪t) := by
  apply (onSupport (s∪t)).sub_mem (mul_mem_union A B hA hB)
  have he := mul_mem_union B A hB hA
  simpa only [Finset.union_comm] using he

end Qatlib.Foundations.MatrixAlgebra.TensorSupport
