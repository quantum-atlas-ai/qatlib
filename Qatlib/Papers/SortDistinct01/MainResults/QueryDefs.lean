/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Phase queries and block overlap bounds

This module models phase queries on a finite work register and query register. `blockProj`,
`blockNormSq`, and `blockNorm` isolate the contribution of each query index, and the overlap
identities yield the single-query estimate of Lemma 5 in [HoyerNeerbekShi2001].

## Main statements

* `inner_difference_eq`: For sign-valued oracles, the change in overlap equals twice the sum of
  coordinate products over query indices where the oracles differ.
* `lemma5_unitary_step_bound`: The same single-query overlap bound holds when a common complex
  linear isometry is applied after the two sign-valued phase oracles.

## References

* [Hoyer et al., 2001][HoyerNeerbekShi2001]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder ComplexConjugate ComplexInnerProductSpace
open Finset Complex

namespace Qatlib.Papers.SortDistinct01.MainResults.QueryDefs

/-- The product of a work-register index in `Fin Z` and a query-register index in `Fin N`. -/
abbrev QIdx (Z N : ℕ) : Type := Fin Z × Fin N

/-- The complex Euclidean space of states indexed by `QIdx Z N`. -/
abbrev QState (Z N : ℕ) : Type := EuclideanSpace ℂ (QIdx Z N)

variable {Z N : ℕ}

/-- Regard a complex coordinate function on `QIdx Z N` as a Euclidean state. -/
def mkQ (f : QIdx Z N → ℂ) : QState Z N := WithLp.toLp 2 f

/-- Multiply each state coordinate by the oracle value at its query index. -/
def phaseOracle (x : Fin N → ℂ) (u : QState Z N) : QState Z N :=
  mkQ fun j => x j.2 * u j

/-- Retain the coordinates with query index `i` and set all other coordinates to zero. -/
def blockProj (i : Fin N) (u : QState Z N) : QState Z N :=
  mkQ fun j => if j.2 = i then u j else 0

/-- The sum of squared coordinate norms in the query block indexed by `i`. -/
def blockNormSq (u : QState Z N) (i : Fin N) : ℝ :=
  ∑ z : Fin Z, ‖u (z, i)‖ ^ 2

/-- The square root of the squared norm of the query block indexed by `i`. -/
def blockNorm (u : QState Z N) (i : Fin N) : ℝ := Real.sqrt (blockNormSq u i)

/-- The squared norm of each query block is nonnegative. -/
theorem blockNormSq_nonneg (u : QState Z N) (i : Fin N) : 0 ≤ blockNormSq u i :=
  Finset.sum_nonneg fun z _ => by positivity

/-- The norm of each query block is nonnegative. -/
theorem blockNorm_nonneg (u : QState Z N) (i : Fin N) : 0 ≤ blockNorm u i :=
  Real.sqrt_nonneg _

/-- Squaring a query block norm recovers its squared norm. -/
theorem blockNorm_sq (u : QState Z N) (i : Fin N) : blockNorm u i ^ 2 = blockNormSq u i :=
  Real.sq_sqrt (blockNormSq_nonneg u i)

/-- Express the inner product of two query states as the sum of conjugate coordinate products. -/
theorem inner_apply_eq_sum (u v : QState Z N) :
    ⟪u, v⟫ = ∑ j : QIdx Z N, conj (u j) * v j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Expand the inner product after two phase oracles into a coordinate sum weighted by their
oracle values. -/
theorem inner_phaseOracle (x y : Fin N → ℂ) (u v : QState Z N) :
    ⟪phaseOracle x u, phaseOracle y v⟫
      = ∑ j : QIdx Z N, (conj (x j.2) * y j.2) * (conj (u j) * v j) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [phaseOracle, mkQ, WithLp.ofLp_toLp, RCLike.inner_apply, map_mul]
  ring

/-- For sign-valued oracles, the change in overlap equals twice the sum of coordinate products
over query indices where the oracles differ. See [HoyerNeerbekShi2001]. -/
theorem inner_difference_eq {x y : Fin N → ℂ}
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (u v : QState Z N) :
    ⟪u, v⟫ - ⟪phaseOracle x u, phaseOracle y v⟫
      = 2 * ∑ j ∈ Finset.univ.filter (fun j : QIdx Z N => x j.2 ≠ y j.2),
          conj (u j) * v j := by
  have hterm : ∀ j : QIdx Z N,
      conj (u j) * v j - (conj (x j.2) * y j.2) * (conj (u j) * v j)
        = if x j.2 ≠ y j.2 then 2 * (conj (u j) * v j) else 0 := by
    intro j
    rcases hx j.2 with hx' | hx' <;> rcases hy j.2 with hy' | hy'
    · simp [hx', hy']
    · simp [hx', hy', show ¬((1 : ℂ) = -1) by norm_num]; ring
    · simp [hx', hy', show ¬((-1 : ℂ) = 1) by norm_num]; ring
    · simp [hx', hy']
  rw [inner_apply_eq_sum, inner_phaseOracle, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  trans ∑ j : QIdx Z N, if x j.2 ≠ y j.2 then 2 * (conj (u j) * v j) else 0
  · exact Finset.sum_congr rfl fun j _ => hterm j
  · rw [← Finset.sum_filter]

/-- The norm of the coordinate inner product within a query block is at most the product of the
two block norms. -/
theorem block_inner_le (u v : QState Z N) (i : Fin N) :
    ‖∑ z : Fin Z, conj (u (z, i)) * v (z, i)‖
      ≤ blockNorm u i * blockNorm v i := by
  let U : EuclideanSpace ℂ (Fin Z) := WithLp.toLp 2 (fun z => u (z, i))
  let V : EuclideanSpace ℂ (Fin Z) := WithLp.toLp 2 (fun z => v (z, i))
  have hinner : ⟪U, V⟫ = ∑ z : Fin Z, conj (u (z, i)) * v (z, i) := by
    simp [U, V, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hU : ‖U‖ = blockNorm u i := by
    rw [EuclideanSpace.norm_eq]
    simp [U, blockNorm, blockNormSq]
  have hV : ‖V‖ = blockNorm v i := by
    rw [EuclideanSpace.norm_eq]
    simp [V, blockNorm, blockNormSq]
  rw [← hinner, ← hU, ← hV]
  exact norm_inner_le_norm U V

/-- For sign-valued oracles, bound the change in overlap by twice the sum of block-norm products
over differing query indices. See [HoyerNeerbekShi2001]. -/
theorem lemma5_inner_step_bound {x y : Fin N → ℂ}
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (u v : QState Z N) :
    ‖⟪u, v⟫ - ⟪phaseOracle x u, phaseOracle y v⟫‖
      ≤ 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin N => x i ≠ y i),
          blockNorm u i * blockNorm v i := by
  rw [inner_difference_eq hx hy]
  have hsplit :
      (∑ j ∈ Finset.univ.filter (fun j : QIdx Z N => x j.2 ≠ y j.2),
          conj (u j) * v j)
        = ∑ i ∈ Finset.univ.filter (fun i : Fin N => x i ≠ y i),
            ∑ z : Fin Z, conj (u (z, i)) * v (z, i) := by
    rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.sum_comm]
    trans ∑ c : Fin N,
        if x c ≠ y c then ∑ z : Fin Z, conj (u (z, c)) * v (z, c) else 0
    · apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    · rw [← Finset.sum_filter]
  rw [hsplit, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => x i ≠ y i),
          ∑ z : Fin Z, conj (u (z, i)) * v (z, i)‖
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => x i ≠ y i),
          ‖∑ z : Fin Z, conj (u (z, i)) * v (z, i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => x i ≠ y i),
          blockNorm u i * blockNorm v i := by
        apply Finset.sum_le_sum
        intro i _
        exact block_inner_le u v i

/-- The same single-query overlap bound holds when a common complex linear isometry is applied
after the two sign-valued phase oracles. See [HoyerNeerbekShi2001]. -/
theorem lemma5_unitary_step_bound (U : QState Z N ≃ₗᵢ[ℂ] QState Z N) {x y : Fin N → ℂ}
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (u v : QState Z N) :
    ‖⟪u, v⟫ - ⟪U (phaseOracle x u), U (phaseOracle y v)⟫‖
      ≤ 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin N => x i ≠ y i),
          blockNorm u i * blockNorm v i := by
  rw [LinearIsometryEquiv.inner_map_map]
  exact lemma5_inner_step_bound hx hy u v

end Qatlib.Papers.SortDistinct01.MainResults.QueryDefs
