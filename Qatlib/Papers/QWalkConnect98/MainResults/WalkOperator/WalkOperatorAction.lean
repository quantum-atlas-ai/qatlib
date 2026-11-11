/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator.WalkOperatorDefinitions

/-!
# Action of the projected connectivity walk

The formulas for `walkF`, `walkX`, and `walkP` show that the projected operator `walkQ` acts on
diagonal lifts exactly as `walkM` acts on vertex vectors. This correspondence extends to powers
and gives formulas for diagonal and off-diagonal entries.

The vertex-space walk also preserves support within each connected component, so its iterates
vanish outside the source component. The mathematical setting is described in [Watrous1998].

## Main statements

* `walkQ_mulVec_diagLift`: intertwine `walkQ` and `walkM` through `diagLift`.
* `walkQ_pow_apply_diag` and `walkQ_pow_apply_offdiag`: entries starting from a diagonal state.
* `walkM_pow_apply_eq_zero`: preserve component support under iteration.

## References

* [Watrous, 1998][Watrous1998]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator

open Finset
open scoped BigOperators Matrix

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex in the neighbor set of `v` is reachable from `v`, with reachability stated from the
neighbor to `v`. -/
theorem reachable_of_mem_neighborFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} (h : w ∈ G.neighborFinset v) : G.Reachable w v := by
  rcases mem_closedNbhd.mp (closedNbhd_comm.mp (Finset.mem_insert_of_mem h)) with h' | h'
  · subst h'
    exact SimpleGraph.Reachable.rfl
  · exact h'.reachable

/-- The projection `walkP` retains coordinates on diagonal pairs and sets all other coordinates
to zero. -/
theorem walkP_mulVec_apply (y : V × V → ℝ) (p : V × V) :
    (walkP *ᵥ y) p = if p.1 = p.2 then y p else 0 := by
  simp only [Matrix.mulVec, dotProduct, walkP, Matrix.of_apply]
  by_cases h : p.1 = p.2
  · rw [if_pos h]
    have hterm : ∀ q : V × V,
        (if p = q ∧ p.1 = p.2 then (1 : ℝ) else 0) * y q =
          (if p = q then y q else 0) := by
      intro q
      by_cases hq : p = q
      · subst hq
        simp [h]
      · simp [hq]
    simp only [hterm]
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q _
    have h' : ¬ (p = q ∧ p.1 = p.2) := fun hc => h hc.2
    simp [h']

/-- The projection `walkP` fixes every diagonal lift. -/
theorem walkP_mulVec_diagLift (x : V → ℝ) :
    walkP *ᵥ diagLift x = diagLift x := by
  funext p
  rw [walkP_mulVec_apply]
  by_cases hp : p.1 = p.2
  · rw [if_pos hp, diagLift_apply, if_pos hp]
  · rw [if_neg hp, diagLift_apply, if_neg hp]

/-- The swap matrix `walkX` exchanges the two coordinates of each pair when acting on a vector. -/
theorem walkX_mulVec_apply (y : V × V → ℝ) (p : V × V) :
    (walkX *ᵥ y) p = y (p.2, p.1) := by
  simp only [Matrix.mulVec, dotProduct, walkX, Matrix.of_apply]
  have hterm : ∀ q : V × V,
      (if q.1 = p.2 ∧ q.2 = p.1 then (1 : ℝ) else 0) * y q =
        (if (p.2, p.1) = q then y q else 0) := by
    intro q
    by_cases hq : q = (p.2, p.1)
    · subst hq
      simp
    · have h1 : ¬ (q.1 = p.2 ∧ q.2 = p.1) := fun hc => hq (Prod.ext hc.1 hc.2)
      have h2 : ¬ ((p.2, p.1) = q) := fun hc => hq hc.symm
      simp [h1, h2]
  simp only [hterm]
  simp

/-- On a closed neighborhood, `walkF` subtracts `2 / (d + 1)` times the sum over that
neighborhood from each coordinate in its row block, and it leaves coordinates outside the
neighborhood unchanged. -/
theorem walkF_mulVec_apply (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x : V × V → ℝ) (p : V × V) :
    (walkF G d *ᵥ x) p =
      (if p.2 ∈ closedNbhd G p.1 then
        x (p.1, p.2) - 2 / (d + 1) * (∑ w ∈ closedNbhd G p.1, x (p.1, w))
      else x (p.1, p.2)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

  rw [Finset.sum_eq_single p.1]
  · by_cases hmem : p.2 ∈ closedNbhd G p.1
    · have hb : ∀ b : V, walkF G d p (p.1, b) * x (p.1, b) =
          (((if b = p.2 then 1 else 0) - (if b ∈ closedNbhd G p.1 then 2 / (d + 1) else 0)) *
            x (p.1, b)) := by
        intro b
        simp only [walkF, Matrix.of_apply, hmem, if_true]
      simp only [hb]
      have hsplit : ∀ b : V,
          ((if b = p.2 then (1 : ℝ) else 0) -
            (if b ∈ closedNbhd G p.1 then 2 / (d + 1) else 0)) * x (p.1, b) =
          ((if b = p.2 then x (p.1, b) else 0) -
            (if b ∈ closedNbhd G p.1 then (2 / (d + 1)) * x (p.1, b) else 0)) := by
        intro b
        by_cases h1 : b = p.2
        · subst h1
          by_cases h2 : p.2 ∈ closedNbhd G p.1
          · simp only [h2, if_true]
            ring
          · simp only [h2, if_true, if_false]
            ring
        · by_cases h2 : b ∈ closedNbhd G p.1
          · simp only [h1, h2, if_true, if_false]
            ring
          · simp only [h1, h2, if_true, if_false]
            ring
      simp only [hsplit, Finset.sum_sub_distrib]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ p.2), Finset.sum_ite_mem,
        Finset.univ_inter, ← Finset.mul_sum]
      rw [if_pos hmem]
    · have hb : ∀ b : V, walkF G d p (p.1, b) * x (p.1, b) =
          (if b = p.2 then x (p.1, b) else 0) := by
        intro b
        by_cases h1 : b = p.2
        · simp only [walkF, Matrix.of_apply, hmem, h1, if_true, if_false]
          ring
        · simp only [walkF, Matrix.of_apply, hmem, h1, if_true, if_false]
          ring
      simp only [hb]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ p.2), if_neg hmem]
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    have h0 : walkF G d p (a, b) = 0 := by
      simp [walkF, ha]
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p.1) h

/-- Applying `walkF` to a diagonal lift gives the stated closed-neighborhood formula with
coefficient `(if u = v then 1 else 0) - 2 / (d + 1)`. -/
theorem walkF_diagLift_apply (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x : V → ℝ) (u v : V) :
    (walkF G d *ᵥ diagLift x) (u, v) =
      (if v ∈ closedNbhd G u then
        ((if u = v then 1 else 0) - 2 / (d + 1)) * x u
      else 0) := by
  rw [walkF_mulVec_apply]
  by_cases hv : v ∈ closedNbhd G u
  · rw [if_pos hv, if_pos hv]
    have hsum : (∑ w ∈ closedNbhd G u, diagLift x (u, w)) = x u := by
      simp only [diagLift_apply]
      rw [Finset.sum_ite_eq, if_pos (self_mem_closedNbhd G u)]
    rw [hsum, diagLift_apply]
    by_cases huv : u = v
    · subst huv
      simp
      ring
    · simp [huv]
  · rw [if_neg hv, if_neg hv]
    have huv : ¬ (u = v) := fun h => hv (h ▸ self_mem_closedNbhd G u)
    simp [diagLift_apply, huv]

/-- Applying `walkF` and then the swap to a diagonal lift gives the stated formula supported on
the swapped closed-neighborhood pairs. -/
theorem walkX_walkF_diagLift_apply (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x : V → ℝ) (p : V × V) :
    (walkX *ᵥ (walkF G d *ᵥ diagLift x)) p =
      (if p.1 ∈ closedNbhd G p.2 then
        ((if p.2 = p.1 then 1 else 0) - 2 / (d + 1)) * x p.2
      else 0) := by
  rw [walkX_mulVec_apply, walkF_diagLift_apply]

/-- The expression `(1 - c) * x - c * ((1 - c) * x - c * s)` equals `(1 - c) ^ 2 * x + c ^ 2 *
s`. -/
theorem walkA_identity (c x s : ℝ) :
    (1 - c) * x - c * ((1 - c) * x - c * s) = (1 - c) ^ 2 * x + c ^ 2 * s := by
  ring

/-- The diagonal coordinate after applying `walkF`, the swap, and `walkF` to `diagLift x` is
`walkA d * x u + walkB d * ∑ w ∈ G.neighborFinset u, x w`. -/
theorem walkF_X_F_diagLift_apply (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x : V → ℝ) (u : V) :
    (walkF G d *ᵥ (walkX *ᵥ (walkF G d *ᵥ diagLift x))) (u, u) =
      walkA d * x u + walkB d * ∑ w ∈ G.neighborFinset u, x w := by
  rw [walkF_mulVec_apply]
  rw [if_pos (self_mem_closedNbhd G u)]
  have hw : ∀ b : V, (walkX *ᵥ (walkF G d *ᵥ diagLift x)) (u, b) =
      (if u ∈ closedNbhd G b then ((if b = u then 1 else 0) - 2 / (d + 1)) * x b
        else 0) := by
    intro b
    rw [walkX_walkF_diagLift_apply]
  simp only [hw]
  have hsum : (∑ w ∈ closedNbhd G u,
        (if u ∈ closedNbhd G w then ((if w = u then 1 else 0) - 2 / (d + 1)) * x w
          else 0))
      = (1 - 2 / (d + 1)) * x u - 2 / (d + 1) * ∑ w ∈ G.neighborFinset u, x w := by
    have hcongr : (∑ w ∈ closedNbhd G u,
          (if u ∈ closedNbhd G w then ((if w = u then 1 else 0) - 2 / (d + 1)) * x w
            else 0))
        = ∑ w ∈ closedNbhd G u, ((if w = u then 1 else 0) - 2 / (d + 1)) * x w := by
      apply Finset.sum_congr rfl
      intro w hwmem
      rw [if_pos (closedNbhd_comm.mp hwmem)]
    rw [hcongr]
    have hone : ∀ w : V, ((if w = u then (1 : ℝ) else 0) - 2 / (d + 1)) * x w =
        (if w = u then x w else 0) - (2 / (d + 1)) * x w := by
      intro w
      by_cases hw' : w = u
      · subst hw'
        simp
        ring
      · rw [if_neg hw', if_neg hw']
        ring
    simp only [hone, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq', if_pos (self_mem_closedNbhd G u)]
    simp only [closedNbhd]
    rw [Finset.sum_insert (G.notMem_neighborFinset_self u)]
    rw [← Finset.mul_sum]
    ring
  rw [hsum]
  have hhead : (if u ∈ closedNbhd G u then
      ((if True then (1 : ℝ) else 0) - 2 / (d + 1)) * x u else 0) =
        (1 - 2 / (d + 1)) * x u := by
    rw [if_pos (self_mem_closedNbhd G u)]
    norm_num
  rw [hhead, walkA, walkB]
  exact walkA_identity (2 / (d + 1)) (x u) (∑ w ∈ G.neighborFinset u, x w)

/-- The adjacency matrix applied to `x` sums `x` over the neighbors of the selected vertex. -/
theorem adjMatrix_mulVec_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (u : V) :
    (adjMatrix G *ᵥ x) u = ∑ w ∈ G.neighborFinset u, x w := by
  simp only [Matrix.mulVec, dotProduct, adjMatrix, Matrix.of_apply]
  rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : G.Adj u w <;> simp [hw]

/-- The walk matrix applied to `x` combines `walkA d * x u` with `walkB d` times the neighbor
sum. -/
theorem walkM_mulVec_apply (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x : V → ℝ) (u : V) :
    (walkM G d *ᵥ x) u = walkA d * x u + walkB d * ∑ w ∈ G.neighborFinset u, x w := by
  have h1 : walkM G d *ᵥ x = walkA d • x + walkB d • (adjMatrix G *ᵥ x) := by
    unfold walkM
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [adjMatrix_mulVec_apply]

/-- The projected pair-space walk on `diagLift x` equals the diagonal lift of the vertex-space
walk on `x`. -/
theorem walkQ_mulVec_diagLift (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (x : V → ℝ) :
    walkQ G d *ᵥ diagLift x = diagLift (walkM G d *ᵥ x) := by
  have hQ : walkQ G d = walkP * (walkF G d * (walkX * (walkF G d * walkP))) := by
    simp only [walkQ, Matrix.mul_assoc]
  rw [hQ]
  simp only [← Matrix.mulVec_mulVec]
  rw [walkP_mulVec_diagLift]
  funext p
  rw [walkP_mulVec_apply]
  by_cases hp : p.1 = p.2
  · rw [if_pos hp, diagLift_apply, if_pos hp]
    have hp' : p = (p.1, p.1) := by ext <;> simp [hp]
    rw [hp', walkF_X_F_diagLift_apply, walkM_mulVec_apply]
  · rw [if_neg hp, diagLift_apply, if_neg hp]

/-- Every power of the projected walk intertwines with the corresponding power of the
vertex-space walk through `diagLift`. -/
theorem walkQ_pow_mulVec_diagLift (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (k : ℕ) : ∀ x : V → ℝ,
    (walkQ G d ^ k) *ᵥ diagLift x = diagLift ((walkM G d ^ k) *ᵥ x) := by
  induction k with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, walkQ_mulVec_diagLift]
    rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- The entry of `walkQ ^ k` from `(s, s)` to `(v, v)` equals the `v` coordinate of `walkM ^ k`
applied to `basisVec s`. -/
theorem walkQ_pow_apply_diag (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (k : ℕ) (s v : V) :
    (walkQ G d ^ k) (v, v) (s, s) = ((walkM G d ^ k) *ᵥ basisVec s) v := by
  have h := congrFun (walkQ_pow_mulVec_diagLift G d k (basisVec s)) (v, v)
  have h1 : (walkQ G d ^ k *ᵥ diagLift (basisVec s)) (v, v) =
      (walkQ G d ^ k) (v, v) (s, s) := by
    simp only [Matrix.mulVec, dotProduct, diagLift_basisVec, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ (s, s))]
  have h2 : diagLift ((walkM G d ^ k) *ᵥ basisVec s) (v, v) =
      ((walkM G d ^ k) *ᵥ basisVec s) v := by
    rw [diagLift_apply, if_pos rfl]
  rw [h1, h2] at h
  exact h

/-- Every entry of `walkQ ^ k` from a diagonal state to an off-diagonal pair is zero. -/
theorem walkQ_pow_apply_offdiag (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (k : ℕ) (s : V) {p : V × V} (hp : p.1 ≠ p.2) :
    (walkQ G d ^ k) p (s, s) = 0 := by
  have h := congrFun (walkQ_pow_mulVec_diagLift G d k (basisVec s)) p
  have h1 : (walkQ G d ^ k *ᵥ diagLift (basisVec s)) p =
      (walkQ G d ^ k) p (s, s) := by
    simp only [Matrix.mulVec, dotProduct, diagLift_basisVec, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ (s, s))]
  have h2 : diagLift ((walkM G d ^ k) *ᵥ basisVec s) p = 0 := by
    rw [diagLift_apply, if_neg hp]
  rw [h1, h2] at h
  exact h

/-- The walk matrix preserves the property that a vector vanishes outside the component of `s`. -/
theorem walkM_mulVec_support (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (s : V)
    {x : V → ℝ} (hx : ∀ v, ¬ G.Reachable s v → x v = 0) :
    ∀ v, ¬ G.Reachable s v → (walkM G d *ᵥ x) v = 0 := by
  intro v hv
  rw [walkM_mulVec_apply]
  have hav : x v = 0 := hx v hv
  have hb : (∑ w ∈ G.neighborFinset v, x w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    apply hx w
    intro hreach
    exact hv (hreach.trans (reachable_of_mem_neighborFinset hw))
  rw [hav, hb]
  ring

/-- Every power of the walk matrix preserves vanishing outside the component of `s`. -/
theorem walkM_pow_apply_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (s : V) {x : V → ℝ} (hx : ∀ v, ¬ G.Reachable s v → x v = 0) (k : ℕ) :
    ∀ v, ¬ G.Reachable s v → ((walkM G d ^ k) *ᵥ x) v = 0 := by
  induction k with
  | zero =>
    intro v hv
    simpa using hx v hv
  | succ n ih =>
    intro v hv
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact walkM_mulVec_support G d s ih v hv

end

end Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
