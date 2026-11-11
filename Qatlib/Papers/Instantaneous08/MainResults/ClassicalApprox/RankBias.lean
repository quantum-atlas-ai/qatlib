/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Binary bilinear bias and matrix rank

This module computes the probability that a bilinear form over `ZMod 2` vanishes on two
independent uniform vectors. Kernel counting expresses the result in terms of matrix rank,
providing the rank formula used in Lemma 6 of [ShepherdBremner2009].

## Main statements

* `card_ker_qlin`: counts the kernel of the matrix linear map using rank.
* `pairProb_bilinear_eq_rank`: computes the zero probability as `(1 + 2 ^ (-rank Q)) / 2`.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

namespace Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox

/-- The `n`-dimensional vector space over `ZMod 2`, represented by coordinate functions. -/
abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

/-- Every element of `ZMod 2` is either zero or one. -/
theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  have h2 : a.val = 0 ∨ a.val = 1 := by omega
  rcases h2 with h0 | h1
  · exact Or.inl ((ZMod.val_eq_zero a).mp h0)
  · exact Or.inr ((ZMod.val_eq_one (by norm_num) a).mp h1)

/-- The coordinate dot product over `ZMod 2` on a finite index type. -/
def dot {ι : Type} [Fintype ι] (x y : ι → ZMod 2) : ZMod 2 :=
  x ⬝ᵥ y

/-- Taking the dot product with `s` distributes over a finite sum in the first argument. -/
theorem dot_sum {ι κ : Type} [Fintype ι] [Fintype κ] (v : κ → ι → ZMod 2)
    (s : ι → ZMod 2) : dot (∑ i, v i) s = ∑ i, dot (v i) s := by
  simp only [dot, dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Scaling the first argument by `c` scales its dot product with `s` by `c`. -/
theorem dot_smul {ι : Type} [Fintype ι] (c : ZMod 2) (v s : ι → ZMod 2) :
    dot (c • v) s = c * dot v s := by
  simp [dot]

/-- For fixed `e`, the linear functional `d ↦ dot d (Q.mulVec e)`. -/
def bilinearForm {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (e : F2Vec n) :
    F2Vec n →ₗ[ZMod 2] ZMod 2 where
  toFun d := dot d (Q.mulVec e)
  map_add' d d' := by
    simp [dot]
  map_smul' c d := by
    simp [dot]

/-- The proportion of ordered pairs of binary vectors satisfying the decidable relation `P`. -/
def pairProb {n : ℕ} (P : F2Vec n → F2Vec n → Prop) [DecidableRel P] : ℝ :=
  (∑ d : F2Vec n, ∑ e : F2Vec n, if P d e then (1 : ℝ) else 0) /
    (Fintype.card (F2Vec n) : ℝ) ^ 2

/-- Pointwise equivalent relations on pairs of binary vectors have the same uniform pair
probability. -/
theorem pairProb_congr {n : ℕ} {P Q : F2Vec n → F2Vec n → Prop} [DecidableRel P]
    [DecidableRel Q] (h : ∀ d e, P d e ↔ Q d e) : pairProb P = pairProb Q := by
  unfold pairProb
  congr 1
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  by_cases hp : P d e
  · have hq : Q d e := (h d e).mp hp
    simp [hp, hq]
  · have hq : ¬ Q d e := fun hq => hp ((h d e).mpr hq)
    simp [hp, hq]

/-- There are `2 ^ n` binary vectors of dimension `n`. -/
theorem card_f2vec (n : ℕ) : Fintype.card (F2Vec n) = 2 ^ n := by
  rw [Fintype.card_pi]
  simp

/-- For fixed `e`, the sum of indicators for `dot d (Q.mulVec e) = 0` equals the cardinality of
the kernel of `bilinearForm Q e`. -/
theorem sum_indicator_eq_card_ker {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : F2Vec n) :
    (∑ d : F2Vec n, if dot d (Q.mulVec e) = 0 then (1 : ℝ) else 0) =
      (Fintype.card (LinearMap.ker (bilinearForm Q e)) : ℝ) := by
  rw [Finset.sum_boole, Fintype.card_subtype]
  congr 1
  simp only [LinearMap.mem_ker, bilinearForm]
  rfl

/-- The kernel of `bilinearForm Q e` contains all binary vectors when `Q.mulVec e = 0`, and
exactly half of them otherwise. -/
theorem card_ker_bilinearForm {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : F2Vec n) :
    (Fintype.card (LinearMap.ker (bilinearForm Q e)) : ℝ) =
      if Q.mulVec e = 0 then (Fintype.card (F2Vec n) : ℝ)
      else (Fintype.card (F2Vec n) : ℝ) / 2 := by
  by_cases h : Q.mulVec e = 0
  · rw [if_pos h]
    have hzero : bilinearForm Q e = 0 := by
      ext d
      simp [bilinearForm, dot, h]
    rw [hzero, LinearMap.ker_zero]
    simp
  · rw [if_neg h]
    have hne : bilinearForm Q e ≠ 0 := by
      intro h0
      apply h
      obtain ⟨j, hj⟩ : ∃ j, Q.mulVec e j ≠ 0 := by
        by_contra h'
        exact h (funext fun j => by
          by_contra hj
          exact h' ⟨j, hj⟩)
      have hsingle : bilinearForm Q e (Pi.single j 1) = 0 := by
        rw [h0]
        rfl
      have hsingle' : (Q.mulVec e) j = 0 := by
        simpa [bilinearForm, dot] using hsingle
      exact absurd hsingle' hj
    rcases n with _ | m
    · exfalso
      exact h (funext fun j => Fin.elim0 j)
    · have hker := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod 2)
        (V₁ := F2Vec (m + 1)) hne
      have hV : Module.finrank (ZMod 2) (F2Vec (m + 1)) = m + 1 := by
        rw [Module.finrank_pi]
        simp
      rw [hV] at hker
      have hfin : Module.finrank (ZMod 2) (LinearMap.ker (bilinearForm Q e)) = m := by
        omega
      have hcard : (Fintype.card (LinearMap.ker (bilinearForm Q e)) : ℝ) = (2 : ℝ) ^ m := by
        have hnat : Fintype.card (LinearMap.ker (bilinearForm Q e)) = 2 ^ m := by
          rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2, hfin]
        rw [hnat]
        push_cast
        ring
      rw [hcard]
      have hN : (Fintype.card (F2Vec (m + 1)) : ℝ) = (2 : ℝ) ^ (m + 1) := by
        rw [card_f2vec]
        push_cast
        ring
      rw [hN, pow_succ]
      field_simp

/-- The kernel of the linear map represented by `Q` has cardinality `2 ^ (n - rank Q)`. -/
theorem card_ker_qlin {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Fintype.card (LinearMap.ker Q.mulVecLin) = 2 ^ (n - Matrix.rank Q) := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
  congr 1
  have hker := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin (K := ZMod 2)
  have hV : Module.finrank (ZMod 2) (F2Vec n) = n := by
    rw [Module.finrank_pi]
    simp
  rw [hV] at hker
  have hrank : Module.finrank (ZMod 2) (LinearMap.range Q.mulVecLin) = Matrix.rank Q := rfl
  rw [hrank] at hker
  omega

/-- The uniform probability that `dot d (Q.mulVec e) = 0` is one half of one plus the relative
size of the kernel of `Q.mulVecLin`. -/
theorem pairProb_bilinear_eq_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    pairProb (fun d e => dot d (Q.mulVec e) = 0) =
      (1 + (Fintype.card (LinearMap.ker Q.mulVecLin) : ℝ) /
        (Fintype.card (F2Vec n) : ℝ)) / 2 := by
  rw [pairProb]
  have hinner : ∀ e : F2Vec n,
      (∑ d : F2Vec n, if dot d (Q.mulVec e) = 0 then (1 : ℝ) else 0) =
        (Fintype.card (LinearMap.ker (bilinearForm Q e)) : ℝ) :=
    fun e => sum_indicator_eq_card_ker Q e
  have hstep :
      (∑ e : F2Vec n, (Fintype.card (LinearMap.ker (bilinearForm Q e)) : ℝ)) =
        ∑ e : F2Vec n,
          ((Fintype.card (F2Vec n) : ℝ) / 2 +
            ((Fintype.card (F2Vec n) : ℝ) -
              (Fintype.card (F2Vec n) : ℝ) / 2) *
              (if Q.mulVec e = 0 then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [card_ker_bilinearForm]
    by_cases h : Q.mulVec e = 0 <;> simp [h]
  have hcount :
      (∑ e : F2Vec n, (if Q.mulVec e = 0 then (1 : ℝ) else 0)) =
        (Fintype.card (LinearMap.ker Q.mulVecLin) : ℝ) := by
    rw [Finset.sum_boole, Fintype.card_subtype]
    congr 1
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [Finset.sum_comm]
  have hnum : (∑ y : F2Vec n, ∑ x : F2Vec n,
        (if dot x (Q.mulVec y) = 0 then (1 : ℝ) else 0)) =
      ∑ y : F2Vec n, (Fintype.card (LinearMap.ker (bilinearForm Q y)) : ℝ) :=
    Finset.sum_congr rfl fun y _ => hinner y
  rw [hnum, hstep, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const]
  rw [hcount]
  simp only [Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- For independent uniform binary vectors `d` and `e`, the probability that `dot d (Q.mulVec e)
= 0` is `(1 + 1 / 2 ^ rank Q) / 2`. This is the rank expression used in [Shepherd and
Bremner, Lemma 6][ShepherdBremner2009]. -/
theorem pairProb_bilinear_eq_rank {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    pairProb (fun d e => dot d (Q.mulVec e) = 0) =
      (1 + 1 / (2 : ℝ) ^ Matrix.rank Q) / 2 := by
  rw [pairProb_bilinear_eq_zero]
  have hN : (Fintype.card (F2Vec n) : ℝ) = (2 : ℝ) ^ n := by
    rw [card_f2vec]
    push_cast
    ring
  have hcard : (Fintype.card (LinearMap.ker Q.mulVecLin) : ℝ) =
      (2 : ℝ) ^ (n - Matrix.rank Q) := by
    rw [card_ker_qlin]
    push_cast
    ring
  have hle : Matrix.rank Q ≤ n := Q.rank_le_height
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ Matrix.rank Q * (2 : ℝ) ^ (n - Matrix.rank Q) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hN, hcard, hpow]
  field_simp

end Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox
