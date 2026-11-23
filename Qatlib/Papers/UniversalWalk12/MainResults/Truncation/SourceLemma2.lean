/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.UniversalWalk12.MainResults.Truncation.Krylov
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Genuine truncation from one controlled Hamiltonian trajectory

The source (arXiv:1205.3782v2, Lemma 2, p.31; Appendix H, pp.68-69) assumes a
Krylov-local approximation to one chosen trajectory W in {H,PHP}. The repaired interface uses
exactly that choice. Equal-duration unitary steps, the exact power telescope and the sharp
Krylov exponential remainder propagate the local estimate to the full interval.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators

namespace Qatlib.Papers.UniversalWalk12.MainResults.Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Approximate states along one actual unitary trajectory control the accumulated local error. -/
theorem power_approx_bound
    (U V : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E))
    (hV : V ∈ unitary (E →L[ℂ] E)) (Φ : E) (hΦ : ‖Φ‖ = 1)
    (M : ℕ) (δ κ : ℝ) (hκ : 0 ≤ κ) (γ : ℕ → E)
    (happrox : ∀ j ∈ Finset.range M, ‖(U ^ j) Φ - γ j‖ ≤ δ)
    (hlocal : ∀ j ∈ Finset.range M, ‖(U - V) (γ j)‖ ≤ κ * ‖γ j‖) :
    ‖(U ^ M) Φ - (V ^ M) Φ‖ ≤ (M : ℝ) * (2 * δ + κ * (1 + δ)) := by
  apply (power_error_bound U V hV Φ M).trans
  calc
    (∑ j ∈ Finset.range M, ‖(U - V) ((U ^ j) Φ)‖) ≤
        ∑ _j ∈ Finset.range M, (2 * δ + κ * (1 + δ)) := by
      apply Finset.sum_le_sum
      intro j hj
      let ψ := (U ^ j) Φ
      let ε := ψ - γ j
      have hε : ‖ε‖ ≤ δ := happrox j hj
      have hψ : ‖ψ‖ = 1 := by
        rw [ContinuousLinearMap.norm_map_of_mem_unitary ((unitary _).pow_mem hU j), hΦ]
      have hγ : ‖γ j‖ ≤ 1 + δ := by
        calc
          ‖γ j‖ = ‖ψ - (ψ - γ j)‖ := by congr 1; abel
          _ ≤ ‖ψ‖ + ‖ψ - γ j‖ := norm_sub_le _ _
          _ ≤ 1 + δ := by rw [hψ]; linarith [hε]
      have hid : (U - V) ψ = (U - V) (γ j) + (U ε - V ε) := by
        simp only [ε, sub_apply, map_sub]
        abel
      change ‖(U - V) ψ‖ ≤ _
      rw [hid]
      calc
        _ ≤ ‖(U - V) (γ j)‖ + ‖U ε - V ε‖ := norm_add_le _ _
        _ ≤ κ * ‖γ j‖ + (‖U ε‖ + ‖V ε‖) :=
          add_le_add (hlocal j hj) (norm_sub_le _ _)
        _ = κ * ‖γ j‖ + (‖ε‖ + ‖ε‖) := by
          rw [ContinuousLinearMap.norm_map_of_mem_unitary hU,
            ContinuousLinearMap.norm_map_of_mem_unitary hV]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hγ hκ]
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- Every positive equal-step subdivision obeys the genuine Krylov truncation error estimate. -/
theorem truncation_steps
    (H P W : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hP : P * P = P) (hPs : star P = P) (hW : W = H ∨ W = P * H * P)
    (Φ : E) (hΦ : ‖Φ‖ = 1) (T δ : ℝ) (N : ℕ) (hN : 0 < N)
    (γ : ℝ → E)
    (hγ : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(τ : ℂ) * Complex.I) • W) Φ - γ τ‖ ≤ δ)
    (horth : ∀ τ ∈ Icc (0 : ℝ) T, ∀ n : ℕ, n < N →
      (1 - P) ((H ^ n) (γ τ)) = 0)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ -
        NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖ ≤
      (M : ℝ) * (2 * δ + 2 * (Real.exp 1 * ‖H‖ * (t / (M : ℝ)) / (N : ℝ)) ^ N * (1 + δ)) := by
  let Δ := t / (M : ℝ)
  let U := NormedSpace.exp ((-(Δ : ℂ) * Complex.I) • H)
  let V := NormedSpace.exp ((-(Δ : ℂ) * Complex.I) • (P * H * P))
  let κ := 2 * (Real.exp 1 * ‖H‖ * Δ / (N : ℝ)) ^ N
  have hMc : 0 < (M : ℝ) := by exact_mod_cast hM
  have hΔ : 0 ≤ Δ := div_nonneg ht.1 hMc.le
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hτ (j : ℕ) (hj : j ∈ Finset.range M) : (j : ℝ) * Δ ∈ Icc (0 : ℝ) T := by
    constructor
    · positivity
    · have hjM : (j : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
      calc
        (j : ℝ) * Δ ≤ (M : ℝ) * Δ := mul_le_mul_of_nonneg_right hjM hΔ
        _ = t := by dsimp [Δ]; field_simp
        _ ≤ T := ht.2
  have hlocal (j : ℕ) (hj : j ∈ Finset.range M) :
      ‖(U - V) (γ ((j : ℝ) * Δ))‖ ≤ κ * ‖γ ((j : ℝ) * Δ)‖ := by
    have hrange : ∀ n : ℕ, n < N →
        P ((H ^ n) (γ ((j : ℝ) * Δ))) = (H ^ n) (γ ((j : ℝ) * Δ)) := by
      intro n hn
      have hh := horth _ (hτ j hj) n hn
      change (H ^ n) (γ ((j : ℝ) * Δ)) - P ((H ^ n) (γ ((j : ℝ) * Δ))) = 0 at hh
      exact (sub_eq_zero.mp hh).symm
    exact truncation_exp_scaled H P hH hP hPs _ N hN hrange Δ hΔ
  have hU : U ∈ unitary (E →L[ℂ] E) := evolution_unitary H hH Δ
  have hV : V ∈ unitary (E →L[ℂ] E) :=
    evolution_unitary (P * H * P) (compression_self H P hH hPs) Δ
  rcases hW with hw | hw
  · subst W
    have happ : ∀ j ∈ Finset.range M, ‖(U ^ j) Φ - γ ((j : ℝ) * Δ)‖ ≤ δ := by
      intro j hj
      dsimp [U]
      rw [evolution_power]
      exact hγ _ (hτ j hj)
    have hh := power_approx_bound U V hU hV Φ hΦ M δ κ hκ
      (fun j => γ ((j : ℝ) * Δ)) happ hlocal
    dsimp [U, V] at hh
    rw [evolution_subdivide H t M hM, evolution_subdivide (P * H * P) t M hM] at hh
    exact hh
  · subst W
    have happ : ∀ j ∈ Finset.range M, ‖(V ^ j) Φ - γ ((j : ℝ) * Δ)‖ ≤ δ := by
      intro j hj
      dsimp [V]
      rw [evolution_power]
      exact hγ _ (hτ j hj)
    have hlocal' : ∀ j ∈ Finset.range M,
        ‖(V - U) (γ ((j : ℝ) * Δ))‖ ≤ κ * ‖γ ((j : ℝ) * Δ)‖ := by
      intro j hj
      rw [sub_apply, norm_sub_rev, ← sub_apply]
      exact hlocal j hj
    have hh := power_approx_bound V U hV hU Φ hΦ M δ κ hκ
      (fun j => γ ((j : ℝ) * Δ)) happ hlocal'
    dsimp [U, V] at hh
    rw [evolution_subdivide H t M hM, evolution_subdivide (P * H * P) t M hM,
      norm_sub_rev] at hh
    exact hh


/-- Lemma 2 of arXiv:1205.3782v2, using one chosen trajectory and actual Krylov propagation. -/
theorem source_lemma2_truncation
    (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hPidem : P * P = P) (hPself : star P = P)
    (Φ : E) (hΦ : ‖Φ‖ = 1)
    (T δ : ℝ) (N₀ : ℕ) (hδ : 0 < δ) (hN₀ : 0 < N₀)
    (W : E →L[ℂ] E) (hW : W = H ∨ W = P * H * P)
    (γ : ℝ → E)
    (hγ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • W) Φ - γ t‖ ≤ δ)
    (horth : ∀ t ∈ Icc (0 : ℝ) T, ∀ r : ℕ, r < N₀ → (1 - P) ((H ^ r) (γ t)) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ
        - NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖
      ≤ (4 * Real.exp 1 * ‖H‖ * t / (N₀ : ℝ) + 2)
          * (δ + (2 : ℝ) ^ (-(N₀ : ℝ)) * (1 + δ)) := by
  intro t ht
  by_cases htzero : t = 0
  · subst t
    simp
    positivity
  by_cases hHzero : H = 0
  · subst H
    simp
    positivity
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have hHpos : 0 < ‖H‖ := norm_pos_iff.mpr hHzero
  have hNc : 0 < (N₀ : ℝ) := by exact_mod_cast hN₀
  let c := 2 * Real.exp 1 * ‖H‖ * t / (N₀ : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let M := Nat.ceil c
  have hM : 0 < M := Nat.ceil_pos.mpr hc
  have hMc : 0 < (M : ℝ) := by exact_mod_cast hM
  have hlower : c ≤ (M : ℝ) := Nat.le_ceil c
  have hupper : (M : ℝ) ≤ c + 1 := (Nat.ceil_lt_add_one hc.le).le
  have hstep := truncation_steps H P W hH hPidem hPself hW Φ hΦ T δ N₀ hN₀
    γ hγ horth M hM t ht
  have hbase0 : 0 ≤ Real.exp 1 * ‖H‖ * (t / (M : ℝ)) / (N₀ : ℝ) := by positivity
  have hhalf : Real.exp 1 * ‖H‖ * (t / (M : ℝ)) / (N₀ : ℝ) ≤ 1 / 2 := by
    have hbound : 2 * Real.exp 1 * ‖H‖ * t ≤ (M : ℝ) * (N₀ : ℝ) :=
      (div_le_iff₀ hNc).mp hlower
    have heq : Real.exp 1 * ‖H‖ * (t / (M : ℝ)) / (N₀ : ℝ) =
        Real.exp 1 * ‖H‖ * t / ((M : ℝ) * (N₀ : ℝ)) := by ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos hMc hNc)).mpr
    nlinarith
  have hpow := pow_le_pow_left₀ hbase0 hhalf N₀
  have hpower : (2 : ℝ) ^ (-(N₀ : ℝ)) = (1 / 2 : ℝ) ^ N₀ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]
  calc
    _ ≤ (M : ℝ) * (2 * δ + 2 *
        (Real.exp 1 * ‖H‖ * (t / (M : ℝ)) / (N₀ : ℝ)) ^ N₀ * (1 + δ)) := hstep
    _ ≤ (M : ℝ) * (2 * δ + 2 * (1 / 2 : ℝ) ^ N₀ * (1 + δ)) := by gcongr
    _ = 2 * (M : ℝ) * (δ + (1 / 2 : ℝ) ^ N₀ * (1 + δ)) := by ring
    _ ≤ 2 * (c + 1) * (δ + (1 / 2 : ℝ) ^ N₀ * (1 + δ)) := by gcongr
    _ = _ := by rw [hpower]; dsimp [c]; ring

end Qatlib.Papers.UniversalWalk12.MainResults.Truncation
