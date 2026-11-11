/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coordinate projections and the quantum hybrid argument

Defines `QueryProjection` and discrete `UnitaryEvolution`, then proves norm preservation and the
complementary-projection mass identity. `hybrid_distance_bound` controls changes between
evolutions that agree off selected query coordinates; `projection_distance_lower` and
`query_fiber_mass` provide complementary lower-bound estimates. For the quantum-search analysis,
see [BoyerEtAl1998].

## Main statements

* `hybrid_distance_bound`: If two stepwise isometric evolutions agree on basis vectors outside
  `A n` before step `r`, their final distance is at most twice the sum of the reference
  evolution's projected norms on those sets.
* `projection_distance_lower`: For unit vectors `u` and `v`, twice the deficit `1 -
  ‖QueryProjection A u‖ - ‖QueryProjection Aᶜ v‖` is bounded by `‖v - u‖ ^ 2`.
* `query_fiber_mass`: The sum of squared projection norms over the fibers labeled `some y` is at
  most the squared norm of the state.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

/-- The coordinate projection that retains entries indexed by `A` and sets all other entries to
zero. -/
noncomputable def QueryProjection {C : Type*} [Fintype C] [DecidableEq C]
    (A : Finset C) (v : EuclideanSpace ℂ C) : EuclideanSpace ℂ C :=
  WithLp.toLp 2 (fun c => if c ∈ A then v c else 0)

/-- The discrete evolution starting from `v` and applying the linear isometry equivalence `U n`
at step `n`. -/
def UnitaryEvolution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℕ → E ≃ₗᵢ[ℂ] E) (v : E) : ℕ → E
  | 0 => v
  | n + 1 => U n (UnitaryEvolution U v n)

/-- Discrete evolution by linear isometry equivalences preserves the norm of the initial vector. -/
theorem unitaryEvolution_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℕ → E ≃ₗᵢ[ℂ] E) (v : E) (n : ℕ) :
    ‖UnitaryEvolution U v n‖ = ‖v‖ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [UnitaryEvolution] using ih

/-- The squared norms of a coordinate projection and its complementary projection sum to the
squared norm of the original vector. -/
theorem queryProjection_complement_mass {C : Type*} [Fintype C] [DecidableEq C]
    (A : Finset C) (v : EuclideanSpace ℂ C) :
    ‖QueryProjection A v‖ ^ 2 + ‖QueryProjection Aᶜ v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c ∈ A <;> simp [QueryProjection, hc]

/-- If two stepwise isometric evolutions agree on basis vectors outside `A n` before step `r`,
their final distance is at most twice the sum of the reference evolution's projected norms
on those sets. -/
theorem hybrid_distance_bound {C : Type*} [Fintype C] [DecidableEq C]
    (U V : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (A : ℕ → Finset C) (v : EuclideanSpace ℂ C) (r : ℕ)
    (hagree : ∀ n, n < r → ∀ c, c ∉ A n →
      V n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1)) :
    ‖UnitaryEvolution V v r - UnitaryEvolution U v r‖ ≤
      2 * ∑ n ∈ Finset.range r, ‖QueryProjection (A n) (UnitaryEvolution U v n)‖ := by
  have hexpand (w : EuclideanSpace ℂ C) :
      w = ∑ c : C, w c • EuclideanSpace.single c 1 := by
    ext c
    simp [Pi.single_apply]
  have hlocal (n : ℕ) (w : EuclideanSpace ℂ C)
      (ha : ∀ c, c ∉ A n →
        V n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1)) :
      ‖V n w - U n w‖ ≤ 2 * ‖QueryProjection (A n) w‖ := by
    let p := QueryProjection (A n) w
    have hcomp : V n (w - p) = U n (w - p) := by
      rw [hexpand (w - p), map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c ∈ A n
      · have hz : (w - p) c = 0 := by simp [p, QueryProjection, hc]
        simp [hz]
      · simp only [map_smul]
        rw [ha c hc]
    have heq : V n w - U n w = V n p - U n p := by
      simp only [map_sub] at hcomp
      exact sub_eq_sub_iff_sub_eq_sub.mp hcomp
    rw [heq]
    calc
      ‖V n p - U n p‖ ≤ ‖V n p‖ + ‖U n p‖ := norm_sub_le _ _
      _ = 2 * ‖p‖ := by simp; ring
  revert hagree
  induction r with
  | zero => intro _; simp [UnitaryEvolution]
  | succ r ih =>
    intro hagree
    have hprev := ih (fun n hn c hc => hagree n (Nat.lt_succ_of_lt hn) c hc)
    have hstep := hlocal r (UnitaryEvolution U v r) (hagree r (Nat.lt_succ_self r))
    calc
      ‖UnitaryEvolution V v (r + 1) - UnitaryEvolution U v (r + 1)‖ ≤
          ‖V r (UnitaryEvolution V v r) - V r (UnitaryEvolution U v r)‖ +
          ‖V r (UnitaryEvolution U v r) - U r (UnitaryEvolution U v r)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖UnitaryEvolution V v r - UnitaryEvolution U v r‖ +
          ‖V r (UnitaryEvolution U v r) - U r (UnitaryEvolution U v r)‖ := by
        rw [← map_sub, LinearIsometryEquiv.norm_map]
      _ ≤ 2 * ∑ n ∈ Finset.range r, ‖QueryProjection (A n) (UnitaryEvolution U v n)‖ +
          2 * ‖QueryProjection (A r) (UnitaryEvolution U v r)‖ := add_le_add hprev hstep
      _ = _ := by rw [Finset.sum_range_succ]; ring

/-- For unit vectors `u` and `v`, twice the deficit `1 - ‖QueryProjection A u‖ -
‖QueryProjection Aᶜ v‖` is bounded by `‖v - u‖ ^ 2`. -/
theorem projection_distance_lower {C : Type*} [Fintype C] [DecidableEq C]
    (A : Finset C) (u v : EuclideanSpace ℂ C) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    2 * (1 - ‖QueryProjection A u‖ - ‖QueryProjection Aᶜ v‖) ≤ ‖v - u‖ ^ 2 := by
  have hsplit : inner ℂ v u = inner ℂ v (QueryProjection A u) +
      inner ℂ (QueryProjection Aᶜ v) u := by
    simp only [PiLp.inner_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c ∈ A <;> simp [QueryProjection, hc]
  have h1 := @re_inner_le_norm ℂ _ _ _ _ v (QueryProjection A u)
  have h2 := @re_inner_le_norm ℂ _ _ _ _ (QueryProjection Aᶜ v) u
  rw [hv, one_mul] at h1
  rw [hu, mul_one] at h2
  have hb : (inner ℂ v u).re ≤ ‖QueryProjection A u‖ + ‖QueryProjection Aᶜ v‖ := by
    rw [hsplit, Complex.add_re]
    exact add_le_add h1 h2
  rw [@norm_sub_sq ℂ, hv, hu]
  change 2 * (1 - ‖QueryProjection A u‖ - ‖QueryProjection Aᶜ v‖) ≤
    1 ^ 2 - 2 * (inner ℂ v u).re + 1 ^ 2
  linarith

/-- The sum of squared projection norms over the fibers labeled `some y` is at most the squared
norm of the state. -/
theorem query_fiber_mass {C Y : Type*} [Fintype C] [DecidableEq C]
    [Fintype Y] [DecidableEq Y] (f : C → Option Y) (u : EuclideanSpace ℂ C) :
    (∑ y : Y, ‖QueryProjection (Finset.univ.filter (fun c => f c = some y)) u‖ ^ 2) ≤
      ‖u‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  cases hf : f c with
  | none => simp [QueryProjection, hf]
  | some y => simp [QueryProjection, hf, apply_ite, eq_comm]

end Qatlib.Concepts.SearchStopping.QueryLowerBound
