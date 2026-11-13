/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.Ext
import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters

/-!
# Stabilizer-function decompositions on the Boolean cube

This module defines `IsStabilizerFun` using the explicit binary linear and quadratic phase
formula supported on an affine subspace, and defines `stabilizerRank` as the least number of
such functions in a complex linear decomposition. The definitions use the finite-field
description of stabilizer amplitudes as background [DehaeneDeMoor2003], without imposing
normalization on these functions.

The Euclidean quantity `cubeNorm` supplies the error bound in `approxStabilizerRank`. This
approximate rank is an infimum in the natural numbers, so a negative tolerance gives zero
through the empty-set infimum convention.

## Main statements

* `cubeWeight` and `quadFun` give Hamming weight and a binary quadratic polynomial.
* `stabilizerRank_eq_zero` characterizes functions of exact rank zero.
* `approxStabilizerRank_le` bounds approximate rank by exact rank for every real tolerance.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.ExactRank

open scoped Classical

/-- The Hamming weight of a Boolean vector, defined by `hammingNorm`. -/
def cubeWeight {n : ℕ} (x : BooleanVec n) : ℕ := hammingNorm x

/-- The binary polynomial `∑ i, ∑ j, Q i j * x i * x j + ∑ i, b i * x i + c` on the Boolean
cube. -/
def quadFun {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (c : ZMod 2) : BooleanVec n → ZMod 2 :=
  fun x => (∑ i, ∑ j, Q i j * x i * x j) + ∑ i, b i * x i + c

/-- The predicate that a function is an affine-subspace indicator multiplied by `Complex.I ^
(booleanDot a x).val` and `(-1) ^ (quadFun Q b c x).val` for some binary parameters. No
normalization factor is included. -/
def IsStabilizerFun {n : ℕ} (φ : BooleanVec n → ℂ) : Prop :=
  ∃ (a : BooleanVec n) (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (c : ZMod 2) (A : AffineSubspace (ZMod 2) (BooleanVec n)),
    φ = fun x => Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val *
      (if x ∈ A then (1 : ℂ) else 0)

/-- The natural-number infimum of the lengths of complex linear decompositions of `F` into
functions satisfying `IsStabilizerFun`. -/
noncomputable def stabilizerRank {n : ℕ} (F : BooleanVec n → ℂ) : ℕ :=
  sInf {r | ∃ (c : Fin r → ℂ) (φ : Fin r → BooleanVec n → ℂ),
    (∀ j, IsStabilizerFun (φ j)) ∧ F = fun x => ∑ j, c j * φ j x}

/-- The Euclidean norm of a complex-valued Boolean-cube function, computed as the square root of
the sum of its squared absolute values. -/
noncomputable def cubeNorm {n : ℕ} (F : BooleanVec n → ℂ) : ℝ :=
  Real.sqrt (∑ x, Complex.normSq (F x))

/-- The natural-number infimum of rank bounds achieved by functions within `cubeNorm` distance
`δ` of `F`. A negative tolerance makes the defining set empty, whose natural-number infimum
is zero. -/
noncomputable def approxStabilizerRank {n : ℕ} (δ : ℝ) (F : BooleanVec n → ℂ) : ℕ :=
  sInf {r | ∃ G : BooleanVec n → ℂ, cubeNorm (F - G) ≤ δ ∧ stabilizerRank G ≤ r}

end Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank

open scoped Classical

/-- The point indicator at any Boolean vector satisfies `IsStabilizerFun`. -/
private theorem stabilizer_delta {n : ℕ} (p : BooleanVec n) :
    IsStabilizerFun (fun x => if x=p then (1 : ℂ) else 0) := by
  refine ⟨0,0,0,0,affineSpan (ZMod 2) ({p} : Set (BooleanVec n)),?_⟩
  ext x
  simp [booleanDot,quadFun,AffineSubspace.mem_affineSpan_singleton]

/-- Every complex-valued function on the Boolean cube has a finite complex linear decomposition
into functions satisfying `IsStabilizerFun`. -/
private theorem stabilizer_rank_set_nonempty {n : ℕ} (F : BooleanVec n → ℂ) :
    {r | ∃ (c : Fin r → ℂ) (φ : Fin r → BooleanVec n → ℂ),
      (∀ j, IsStabilizerFun (φ j)) ∧ F=fun x => ∑ j, c j*φ j x}.Nonempty := by
  let e : Fin (Fintype.card (BooleanVec n)) ≃ BooleanVec n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (BooleanVec n),⟨fun j => F (e j),
    fun j x => if x=e j then 1 else 0,fun j => stabilizer_delta (e j),?_⟩⟩
  ext x
  symm
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro j _ hj
    have hn : x ≠ e j := by
      intro he
      apply hj
      apply e.injective
      simpa using he.symm
    simp [hn]
  · simp

/-- The exact stabilizer rank of a Boolean-cube function is zero exactly when the function is
zero. -/
theorem stabilizerRank_eq_zero {n : ℕ} (F : BooleanVec n → ℂ) :
    stabilizerRank F=0 ↔ F=0 := by
  constructor
  · intro h
    have hm := Nat.sInf_mem (stabilizer_rank_set_nonempty F)
    change stabilizerRank F ∈ {r | ∃ (c : Fin r → ℂ) (φ : Fin r → BooleanVec n → ℂ),
      (∀ j, IsStabilizerFun (φ j)) ∧ F=fun x => ∑ j, c j*φ j x} at hm
    rw [h] at hm
    obtain ⟨c,φ,_,hF⟩ := hm
    simpa using! hF
  · intro h
    apply Nat.eq_zero_of_le_zero
    unfold stabilizerRank
    apply csInf_le'
    refine ⟨0,0,?_,?_⟩
    · intro j
      exact Fin.elim0 j
    · simpa using! h

/-- The approximate stabilizer rank is at most the exact stabilizer rank for every real
tolerance. For a negative tolerance, this uses the empty-set infimum convention in the
natural numbers. -/
theorem approxStabilizerRank_le {n : ℕ} (δ : ℝ) (F : BooleanVec n → ℂ) :
    approxStabilizerRank δ F ≤ stabilizerRank F := by
  by_cases hδ : 0 ≤ δ
  · unfold approxStabilizerRank
    apply csInf_le'
    refine ⟨F,?_,le_rfl⟩
    simpa [cubeNorm] using hδ
  · have he : {r | ∃ G : BooleanVec n → ℂ,
        cubeNorm (F-G) ≤ δ ∧ stabilizerRank G ≤ r}=(∅ : Set ℕ) := by
      ext r
      constructor
      · rintro ⟨G,hG,_⟩
        have hn := Real.sqrt_nonneg (∑ x, Complex.normSq ((F-G) x))
        change 0 ≤ cubeNorm (F-G) at hn
        exact hδ (hn.trans hG)
      · intro hr
        exact hr.elim
    simp [approxStabilizerRank,he]

end Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank
