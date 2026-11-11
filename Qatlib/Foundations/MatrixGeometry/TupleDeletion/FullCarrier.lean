/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.Incidence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Prod

/-!
# Full tuple space and zero extension

Defines `TupleHilbert`, the complex Euclidean space on all tuples, and extends amplitudes on
injective tuples by zero. The extension preserves sums and Euclidean norm.

The full deletion matrix `fullDeletion` acts by coordinate-fiber sums, and
`fullDeletion_kernel_iff` characterizes its kernel by the vanishing of every such sum. See
[MagniezZur2026] for related background.

## Main statements

* `extend_norm`: Zero extension preserves the Euclidean norm of complex amplitudes on injective
  tuples.
* `fullDeletion_kernel_iff`: An amplitude function lies in the kernel of the full deletion
  matrix exactly when every coordinate-fiber sum vanishes.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
open Matrix Module
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

/-- The complex Euclidean space of amplitude functions on all tuples `I → L`. -/
abbrev TupleHilbert (I L : Type*) [Fintype I] [Fintype L] := EuclideanSpace ℂ (I → L)

/-- The complex dimension of the full tuple Hilbert space is `Fintype.card L ^ Fintype.card I`. -/
theorem tupleHilbert_dimension : finrank ℂ (TupleHilbert I L)=Fintype.card L^Fintype.card I := by
  simp [TupleHilbert,finrank_euclideanSpace]

/-- The equivalence between embeddings `I ↪ L` and functions `I → L` equipped with a proof of
injectivity. -/
def embeddingSubtype : InjectiveTuple I L ≃ {y : I → L // Function.Injective y} where
  toFun y := ⟨y,y.injective⟩
  invFun y := ⟨y.1,y.2⟩
  left_inv y := by cases y;rfl
  right_inv y := by cases y;rfl

/-- Extends a function on injective tuples to all tuples by assigning zero to noninjective
tuples. -/
def extend {K : Type*} [Zero K] (v : InjectiveTuple I L → K) (y : I → L) : K :=
  if h : Function.Injective y then v ⟨y,h⟩ else 0
omit [Fintype L] in

/-- Zero extension agrees with the original function at every injective tuple. -/
theorem extend_injective {K : Type*} [Zero K] (v : InjectiveTuple I L → K) (y : InjectiveTuple I L) :
    extend v y=v y := by
  cases y with
  | mk f hf =>
    change (if h : Function.Injective f then v ⟨f,h⟩ else 0)=v ⟨f,hf⟩
    rw [dif_pos hf]

/-- Summing the zero extension over all tuples equals summing the original function over
injective tuples. -/
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

/-- Zero extension preserves the Euclidean norm of complex amplitudes on injective tuples. -/
theorem extend_norm (v : InjectiveTuple I L → ℂ) :
    ‖WithLp.toLp 2 (extend v)‖=‖(WithLp.toLp 2 v : EuclideanSpace ℂ (InjectiveTuple I L))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  have h := sum_extend (fun u : InjectiveTuple I L => ‖v u‖^2)
  convert! h using 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : Function.Injective y <;> simp [extend,h]

/-- The dependent sum of a deleted coordinate and an arbitrary tuple on its complement. -/
abbrev FullRow (I L : Type*) := Σ i : I, Off I i → L

/-- The incidence matrix recording whether an arbitrary tuple restricts to the specified
complementary tuple after deleting the specified coordinate. -/
def fullDeletion : Matrix (FullRow I L) (I → L) ℂ :=
  fun row y => if (fun j : Off I row.1 => y j)=row.2 then 1 else 0

/-- The equivalence separating a tuple into its value at coordinate `i` and its restriction to
the other coordinates. -/
def splitCoordinate (i : I) : (I → L) ≃ L × (Off I i → L) := Equiv.piSplitAt i (fun _ => L)

/-- The sum of an amplitude function over all values at coordinate `i`, with the complementary
tuple fixed to `z`. -/
def fibreSum (v : (I → L) → ℂ) (i : I) (z : Off I i → L) : ℂ :=
  ∑ value : L,v ((splitCoordinate i).symm (value,z))

/-- The value of the full deletion matrix applied to an amplitude function at row `(i, z)` is
its coordinate-fiber sum `fibreSum v i z`. -/
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

/-- An amplitude function lies in the kernel of the full deletion matrix exactly when every
coordinate-fiber sum vanishes. -/
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
