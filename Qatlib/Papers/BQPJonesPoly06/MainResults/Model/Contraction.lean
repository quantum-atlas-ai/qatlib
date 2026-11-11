/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Bridge

/-!
# Contracting components in a bridge decomposition

This module proves geometric-decay estimates for scalar recurrences and their vector components.
For a bridge between orthogonal complementary subspaces, it finds a unit vector whose projected
image has norm less than one and whose complementary component is nonzero. See
[AharonovArad2011].

## Main statements

* `contraction_recurrence`: solves a scalar multiplicative recurrence.
* `contraction_approach_B`: makes the recurrent component arbitrarily small.
* `bridge_contraction_factor`: finds a strictly contracting projected image.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- If `‖a‖ < 1`, the values `‖c * a ^ n‖` become smaller than any positive tolerance. See
[Aharonov and Arad, Lemma 6.1][AharonovArad2011]. -/
theorem geom_decay_complex (a c : ℂ) (ha : ‖a‖ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖c * a ^ n‖ < ε := by
  intro ε hε
  have hpow : Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha
  have hc : Filter.Tendsto (fun n : ℕ => c * a ^ n) Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul c
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hc) ε hε
  exact ⟨N, by simpa [dist_eq_norm] using hN N le_rfl⟩

/-- If `0 ≤ r < 1`, some `c * r ^ n` is smaller than any given positive tolerance, for every
real `c`. See [Aharonov and Arad, Lemma 6.1][AharonovArad2011]. -/
theorem geom_decay_real (r c : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, c * r ^ n < ε := by
  intro ε hε
  have hpow : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hr0])
  have hc : Filter.Tendsto (fun n : ℕ => c * r ^ n) Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul c
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hc) ε hε
  have h := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h
  exact ⟨N, lt_of_le_of_lt (le_abs_self _) h⟩

/-- A scalar sequence satisfying `x (n + 1) = a * x n` has the form `x n = x 0 * a ^ n`. See
[Aharonov and Arad, Lemma 6.1][AharonovArad2011]. -/
theorem contraction_recurrence (x : ℕ → ℂ) (a : ℂ)
    (hx : ∀ n, x (n + 1) = a * x n) :
    ∀ n, x n = x 0 * a ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [hx k, ih, pow_succ]; ring

omit [FiniteDimensional ℂ E] in

/-- For a unit vector `u`, a scalar recurrence with multiplier of norm less than one yields
arbitrarily small values of `‖(x n) • u‖`. See [Aharonov and Arad, Lemma
6.1][AharonovArad2011]. -/
theorem contraction_A_component_decay (u : E) (hu : ‖u‖ = 1) (x : ℕ → ℂ) (a : ℂ)
    (hx : ∀ n, x (n + 1) = a * x n) (ha : ‖a‖ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖(x n) • u‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := geom_decay_complex a (x 0) ha ε hε
  refine ⟨N, ?_⟩
  rw [contraction_recurrence x a hx N, norm_smul, hu, mul_one]
  exact hN

omit [FiniteDimensional ℂ E] in

/-- Some term `(x n) • u + β • v` lies arbitrarily close to `β • v` when the scalar recurrence
multiplier has norm less than one. See [Aharonov and Arad, Lemma 6.1][AharonovArad2011]. -/
theorem contraction_approach_B (u v : E) (hu : ‖u‖ = 1) (x : ℕ → ℂ) (a β : ℂ)
    (hx : ∀ n, x (n + 1) = a * x n) (ha : ‖a‖ < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, ‖(x n) • u + β • v - β • v‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := contraction_A_component_decay u hu x a hx ha ε hε
  refine ⟨N, ?_⟩
  have hsimp : (x N) • u + β • v - β • v = (x N) • u := by abel
  rw [hsimp]
  exact hN

/-- The orthogonal projection of `x` onto `A` belongs to `A`. -/
theorem starProjection_mem (A : Submodule ℂ E) (x : E) : A.starProjection x ∈ A := by
  rw [Submodule.starProjection_apply]
  exact Subtype.coe_prop _

/-- A bridge between orthogonal complementary subspaces has a unit vector in `A` whose image
projects onto `A` with norm less than one. See [Aharonov and Arad, Lemma
6.1][AharonovArad2011]. -/
theorem bridge_contraction_factor {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsBridge A B W) :
    ∃ u ∈ A, ‖u‖ = 1 ∧ ‖A.starProjection (W u)‖ < 1 := by
  obtain ⟨u, huA, hu1, b, hbB, hbne⟩ := hW
  refine ⟨u, huA, hu1, ?_⟩
  have hborth : b ∈ Aᗮ := by simpa [hBA] using hbB
  have hwperpB : (W u : E) - A.starProjection (W u) ∈ Aᗮ :=
    A.sub_starProjection_mem_orthogonal _
  have hPA : A.starProjection (W u) ∈ A := starProjection_mem A _
  have hwperp_ne : (W u : E) - A.starProjection (W u) ≠ 0 := by
    intro h0
    apply hbne
    have hWu : (W u : E) = A.starProjection (W u) := sub_eq_zero.mp h0
    rw [hWu]
    exact Submodule.inner_right_of_mem_orthogonal (K := A) hPA hborth
  have horth : inner ℂ (A.starProjection (W u)) ((W u : E) - A.starProjection (W u)) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := A) hPA hwperpB
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (A.starProjection (W u)) ((W u : E) - A.starProjection (W u)) horth
  have hsum : A.starProjection (W u) + ((W u : E) - A.starProjection (W u)) = (W u : E) := by
    abel
  rw [hsum, W.norm_map, hu1] at hpyth
  have hperp_sq_pos : 0 < ‖(W u : E) - A.starProjection (W u)‖ ^ 2 := by
    have hpos : 0 < ‖(W u : E) - A.starProjection (W u)‖ := by
      rw [norm_pos_iff]; exact hwperp_ne
    positivity
  have hPsq : ‖A.starProjection (W u)‖ ^ 2 < 1 := by nlinarith
  nlinarith [norm_nonneg (A.starProjection (W u))]

/-- A bridge between orthogonal complementary subspaces has a unit vector in `A` whose image has
a nonzero component orthogonal to `A`. See [Aharonov and Arad, Lemma 6.1][AharonovArad2011]. -/
theorem bridge_b_component_ne_zero {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsBridge A B W) :
    ∃ u ∈ A, ‖u‖ = 1 ∧ (W u : E) - A.starProjection (W u) ≠ 0 := by
  obtain ⟨u, huA, hu1, b, hbB, hbne⟩ := hW
  refine ⟨u, huA, hu1, ?_⟩
  intro h0
  apply hbne
  have hWu : (W u : E) = A.starProjection (W u) := sub_eq_zero.mp h0
  have hPA : A.starProjection (W u) ∈ A := starProjection_mem A _
  have hborth : b ∈ Aᗮ := by simpa [hBA] using hbB
  rw [hWu]
  exact Submodule.inner_right_of_mem_orthogonal (K := A) hPA hborth

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
