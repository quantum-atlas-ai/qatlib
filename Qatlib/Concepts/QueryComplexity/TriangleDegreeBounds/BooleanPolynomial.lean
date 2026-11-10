/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.Support
import Mathlib.Combinatorics.Nullstellensatz
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
open MvPolynomial
open scoped BigOperators

noncomputable def booleanPoint {I R : Type} [Zero R] [One R] (x : I → Bool) : I → R :=
  fun i => if x i then 1 else 0

noncomputable def booleanIndicator {I R : Type} [Fintype I] [CommRing R] (x : I → Bool) :
    MvPolynomial I R := ∏ i, if x i then X i else 1-X i

noncomputable def integerBooleanRepresentative {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) : MvPolynomial I ℤ :=
  ∑ x : I → Bool, if f x then booleanIndicator x else 0

private theorem booleanIndicator_eval {I R : Type} [Fintype I] [DecidableEq I]
    [CommRing R] (x y : I → Bool) :
    eval (booleanPoint y) (booleanIndicator x : MvPolynomial I R)=if x=y then 1 else 0 := by
  classical
  unfold booleanIndicator
  rw [map_prod]
  by_cases h : x=y
  · subst x
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    cases hy : y i <;> simp [booleanPoint,hy]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [booleanPoint]

theorem integerBooleanRepresentative_eval {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (y : I → Bool) :
    eval (booleanPoint y) (integerBooleanRepresentative f)=if f y then 1 else 0 := by
  classical
  unfold integerBooleanRepresentative
  rw [map_sum]
  simp_rw [apply_ite, map_zero, booleanIndicator_eval]
  rw [Finset.sum_eq_single y]
  · cases f y <;> simp
  · intro x _ hxy
    cases f x <;> simp [hxy]
  · simp

private theorem booleanIndicator_degreeOf {I R : Type} [Fintype I] [DecidableEq I]
    [CommRing R] [Nontrivial R] (x : I → Bool) (i : I) :
    (booleanIndicator x : MvPolynomial I R).degreeOf i ≤ 1 := by
  classical
  unfold booleanIndicator
  calc
    _ ≤ ∑ j : I, (if x j then (X j : MvPolynomial I R) else 1-X j).degreeOf i :=
      degreeOf_prod_le _ _ _
    _ ≤ ∑ j : I, if i=j then (1 : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      cases hx : x j
      · exact (degreeOf_sub_le i 1 (X j)).trans (by simp [degreeOf_X])
      · simp [degreeOf_X]
    _ = 1 := by simp

private theorem integerBooleanRepresentative_degreeOf {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (i : I) : (integerBooleanRepresentative f).degreeOf i ≤ 1 := by
  classical
  unfold integerBooleanRepresentative
  refine (degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro x _
  cases f x
  · simp
  · exact booleanIndicator_degreeOf x i

private theorem representative_map {I R : Type} [Fintype I] [DecidableEq I] [CommRing R]
    (f : (I → Bool) → Bool) :
    map (Int.castRingHom R) (integerBooleanRepresentative f)=
      ∑ x : I → Bool, if f x then (booleanIndicator x : MvPolynomial I R) else 0 := by
  classical
  simp [integerBooleanRepresentative,booleanIndicator,apply_ite]

theorem integerBooleanRepresentative_map_eval {I R : Type} [Fintype I] [DecidableEq I]
    [CommRing R] (f : (I → Bool) → Bool) (x : I → Bool) :
    eval (booleanPoint x) (map (Int.castRingHom R) (integerBooleanRepresentative f))=
      if f x then 1 else 0 := by
  classical
  rw [representative_map, map_sum]
  simp_rw [apply_ite, map_zero, booleanIndicator_eval]
  rw [Finset.sum_eq_single x]
  · cases f x <;> simp
  · intro y _ hyx
    cases f y <;> simp [hyx]
  · simp

private theorem multilinear_unique {I : Type} [Fintype I] [DecidableEq I]
    (p q : MvPolynomial I ℝ) (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (he : ∀ x : I → Bool, eval (booleanPoint x) p=eval (booleanPoint x) q) : p=q := by
  classical
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero_at_prod_finset (p-q) (fun _ => {0,1})
  · intro i
    have h := (degreeOf_sub_le i p q).trans (max_le (hp i) (hq i))
    simpa using Nat.lt_succ_of_le h
  · intro x hx
    let y : I → Bool := fun i => decide (x i=1)
    have hy : booleanPoint y=x := by
      ext i
      have hi := hx i
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with hi | hi <;> simp [booleanPoint,y,hi]
    rw [← hy, map_sub, he y, sub_self]

theorem integerBooleanRepresentative_real_eq {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (p : MvPolynomial I ℝ)
    (hp : ∀ x, Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p x=if f x then 1 else 0) :
    map (Int.castRingHom ℝ) (integerBooleanRepresentative f)=multilinearize p := by
  classical
  apply multilinear_unique
  · intro i
    rw [degreeOf, degrees_map_of_injective _ (Int.cast_injective (α := ℝ))]
    exact integerBooleanRepresentative_degreeOf f i
  · intro i
    apply degreeOf_le_iff.mpr
    intro d hd
    exact multilinearize_coeff_multilinear p d (mem_support_iff.mp hd) i
  · intro x
    rw [integerBooleanRepresentative_map_eval, multilinearize_eval]
    · exact (hp x).symm
    · intro i
      cases x i <;> simp [booleanPoint]

private theorem mapped_totalDegree_le {I R S : Type} [CommSemiring R] [CommSemiring S]
    (h : R →+* S) (p : MvPolynomial I R) : (map h p).totalDegree ≤ p.totalDegree := by
  classical
  unfold totalDegree
  exact Finset.sup_mono (support_map_subset h p)

theorem integerBooleanRepresentative_degree_le {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (p : MvPolynomial I ℝ)
    (hp : ∀ x, Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p x=if f x then 1 else 0) :
    (integerBooleanRepresentative f).totalDegree ≤ p.totalDegree := by
  classical
  have hd : (map (Int.castRingHom ℝ) (integerBooleanRepresentative f)).totalDegree=
      (integerBooleanRepresentative f).totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ (Int.cast_injective (α := ℝ))]
  rw [← hd, integerBooleanRepresentative_real_eq f p hp]
  exact multilinearize_totalDegree_le p

theorem integerBooleanRepresentative_map_degree_le {I R : Type} [Fintype I] [DecidableEq I]
    [CommRing R] (f : (I → Bool) → Bool) (p : MvPolynomial I ℝ)
    (hp : ∀ x, Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p x=if f x then 1 else 0) :
    (map (Int.castRingHom R) (integerBooleanRepresentative f)).totalDegree ≤ p.totalDegree :=
  (mapped_totalDegree_le _ _).trans (integerBooleanRepresentative_degree_le f p hp)

theorem exactDegree_representative {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) : ∃ p : MvPolynomial I ℝ,
      (∀ x, Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p x=if f x then 1 else 0) ∧
      p.totalDegree=Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f := by
  classical
  let S := (fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ x, Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p x=if f x then 1 else 0}
  have hn : S.Nonempty := by
    refine ⟨_,⟨map (Int.castRingHom ℝ) (integerBooleanRepresentative f),?_,rfl⟩⟩
    intro x
    exact integerBooleanRepresentative_map_eval f x
  obtain ⟨p,hp,hd⟩ := Nat.sInf_mem hn
  exact ⟨p,hp,hd⟩

theorem boolean_mod_two_representation {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) : ∃ p : MvPolynomial I (ZMod 2),
      (∀ x, eval (booleanPoint x) p=if f x then 1 else 0) ∧
      p.totalDegree ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f := by
  obtain ⟨q,hq,hd⟩ := exactDegree_representative f
  refine ⟨map (Int.castRingHom (ZMod 2)) (integerBooleanRepresentative f),
    integerBooleanRepresentative_map_eval f, ?_⟩
  exact (integerBooleanRepresentative_map_degree_le f q hq).trans hd.le

theorem integerBooleanRepresentative_real_degree_eq {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) :
    (map (Int.castRingHom ℝ) (integerBooleanRepresentative f)).totalDegree=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f := by
  classical
  apply le_antisymm
  · obtain ⟨p,hp,hd⟩ := exactDegree_representative f
    exact (integerBooleanRepresentative_map_degree_le f p hp).trans hd.le
  · exact csInf_le' ⟨map (Int.castRingHom ℝ) (integerBooleanRepresentative f),
      integerBooleanRepresentative_map_eval f,rfl⟩

theorem integerBooleanRepresentative_real_degreeOf {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (i : I) :
    (map (Int.castRingHom ℝ) (integerBooleanRepresentative f)).degreeOf i ≤ 1 := by
  rw [degreeOf,degrees_map_of_injective _ (Int.cast_injective (α := ℝ))]
  exact integerBooleanRepresentative_degreeOf f i

end Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
