/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QComplexity97.MachineModel.QtmPrecision
import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeQuantumMachineDefs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Accumulation of transition perturbations

This module develops finite-state perturbation estimates for the precision analysis of
[BernsteinVazirani1997]. Starting from `op_pow_telescope`, it controls the difference of
iterated linear maps when the reference map preserves `stateNorm` and the perturbation has a
uniform relative bound.

The estimates `corollary_3_4_4_bound` and `observation_accuracy_bound` specialize the local
error to `ε / (12 * T)` and bound the resulting state and Born-weight errors. The final lemmas
also control individual columns of native transition rules.

## Main statements

* `stateNorm_perturbed_powers`: bounds accumulated state error by geometric growth.
* `corollary_3_4_4_bound`: bounds normalized-input state error by `ε / 4` under the stated
  precision assumptions.
* `observation_accuracy_bound`: bounds total variation of the resulting Born weights by `ε`.
* `rule_column_perturb_le`: bounds a native rule-column difference from entrywise amplitude
  errors.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QComplexity97.PrecisionModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QComplexity97.MachineDefs.QtmPrecision
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped BigOperators

/-- In any ring, the difference `U' ^ T - U ^ T` is the sum of `U' ^ (T - 1 - k) * (U' - U) * U
^ k` over `k < T`. -/
theorem op_pow_telescope {A : Type*} [Ring A] (U U' : A) (T : ℕ) :
    U' ^ T - U ^ T =
      ∑ k ∈ Finset.range T, U' ^ (T - 1 - k) * (U' - U) * U ^ k := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ']
      have hstep : U' ^ (T + 1) - U ^ (T + 1) =
          U' ^ T * (U' - U) + (U' ^ T - U ^ T) * U := by
        rw [pow_succ U' T, pow_succ U T]
        noncomm_ring
      rw [hstep, ih]
      have hcomb : (∑ k ∈ Finset.range T, U' ^ (T - 1 - k) * (U' - U) * U ^ k) * U =
          ∑ k ∈ Finset.range T, U' ^ (T - 1 - k) * (U' - U) * U ^ (k + 1) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [pow_succ, mul_assoc]
      rw [hcomb, add_comm]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro k _
        have h1 : T - 1 - k = T - (k + 1) := by omega
        have h2 : T + 1 - 1 - (k + 1) = T - (k + 1) := by omega
        rw [h1, h2]
      · simp

/-- The state norm of a finite sum is at most the sum of the state norms. -/
theorem stateNorm_sum_le {I J : Type*} [Fintype I] (s : Finset J) (f : J → QState I) :
    stateNorm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, stateNorm (f j) := by
  have hmap : (EuclideanSpace.equiv I ℂ).symm (∑ j ∈ s, f j) =
      ∑ j ∈ s, (EuclideanSpace.equiv I ℂ).symm (f j) := by
    exact map_sum _ _ _
  rw [stateNorm, hmap]
  have := norm_sum_le s (fun j => (EuclideanSpace.equiv I ℂ).symm (f j))
  simpa [stateNorm] using this

/-- Every natural power of a state-norm-preserving linear map has output state norm at most the
input state norm. -/
theorem stateNorm_pow_le {I : Type*} [Fintype I]
    (U : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ) (k : ℕ) :
    ∀ ψ : QState I, stateNorm ((U ^ k) ψ) ≤ stateNorm ψ := by
  induction k with
  | zero => intro ψ; simp
  | succ k ih =>
      intro ψ
      rw [pow_succ, Module.End.mul_apply]
      exact (ih (U ψ)).trans (le_of_eq (hU ψ))

/-- If `U` preserves state norm and `(U' - U)` has relative state-norm bound `δ`, then `U'`
grows state norm by at most the factor `1 + δ`. -/
theorem stateNorm_step_le {I : Type*} [Fintype I]
    (U U' : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    {δ : ℝ} (hΔ : ∀ ψ, stateNorm ((U' - U) ψ) ≤ δ * stateNorm ψ) (ψ : QState I) :
    stateNorm (U' ψ) ≤ (1 + δ) * stateNorm ψ := by
  have heq : U' ψ = U ψ + (U' - U) ψ := by
    rw [LinearMap.sub_apply]; abel
  rw [heq]
  calc stateNorm (U ψ + (U' - U) ψ) ≤
        stateNorm (U ψ) + stateNorm ((U' - U) ψ) := stateNorm_add_le _ _
    _ ≤ stateNorm ψ + δ * stateNorm ψ := by
        rw [hU]; exact add_le_add le_rfl (hΔ ψ)
    _ = (1 + δ) * stateNorm ψ := by ring

/-- If `U` preserves state norm and its perturbation has nonnegative relative bound `δ`, the
`k`th power of `U'` grows state norm by at most `(1 + δ) ^ k`. -/
theorem stateNorm_pow_le' {I : Type*} [Fintype I]
    (U U' : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hΔ : ∀ ψ, stateNorm ((U' - U) ψ) ≤ δ * stateNorm ψ) (k : ℕ) :
    ∀ ψ : QState I, stateNorm ((U' ^ k) ψ) ≤ (1 + δ) ^ k * stateNorm ψ := by
  induction k with
  | zero => intro ψ; simp
  | succ k ih =>
      intro ψ
      rw [pow_succ, Module.End.mul_apply]
      calc stateNorm ((U' ^ k) (U' ψ)) ≤ (1 + δ) ^ k * stateNorm (U' ψ) := ih (U' ψ)
        _ ≤ (1 + δ) ^ k * ((1 + δ) * stateNorm ψ) :=
            mul_le_mul_of_nonneg_left (stateNorm_step_le U U' hU hΔ ψ) (by positivity)
        _ = (1 + δ) ^ (k + 1) * stateNorm ψ := by rw [pow_succ]; ring

/-- If `U` preserves state norm and `(U' - U)` has nonnegative relative bound `δ`, then the
error after `T` iterations is at most `((1 + δ) ^ T - 1) * stateNorm x`. -/
theorem stateNorm_perturbed_powers {I : Type*} [Fintype I]
    (U U' : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hΔ : ∀ ψ, stateNorm ((U' - U) ψ) ≤ δ * stateNorm ψ)
    (x : QState I) (T : ℕ) :
    stateNorm ((U' ^ T) x - (U ^ T) x) ≤ ((1 + δ) ^ T - 1) * stateNorm x := by
  have htel := op_pow_telescope U U' T
  have hx : (U' ^ T) x - (U ^ T) x =
      ∑ k ∈ Finset.range T, (U' ^ (T - 1 - k) * (U' - U) * U ^ k) x := by
    rw [← LinearMap.sub_apply, htel, LinearMap.sum_apply]
  rw [hx]
  calc stateNorm (∑ k ∈ Finset.range T, (U' ^ (T - 1 - k) * (U' - U) * U ^ k) x)
      ≤ ∑ k ∈ Finset.range T, stateNorm ((U' ^ (T - 1 - k) * (U' - U) * U ^ k) x) :=
        stateNorm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range T, ((1 + δ) ^ (T - 1 - k) * δ * stateNorm x) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hmul : ((U' ^ (T - 1 - k) * (U' - U) * U ^ k) x) =
            (U' ^ (T - 1 - k)) ((U' - U) ((U ^ k) x)) := by
          simp only [Module.End.mul_apply]
        rw [hmul]
        have h1 : stateNorm ((U' ^ (T - 1 - k)) ((U' - U) ((U ^ k) x))) ≤
            (1 + δ) ^ (T - 1 - k) * stateNorm ((U' - U) ((U ^ k) x)) :=
          stateNorm_pow_le' U U' hU hδ hΔ (T - 1 - k) _
        have h2 : stateNorm ((U' - U) ((U ^ k) x)) ≤ δ * stateNorm ((U ^ k) x) := hΔ _
        have h3 : stateNorm ((U ^ k) x) ≤ stateNorm x := stateNorm_pow_le U hU k x
        calc stateNorm ((U' ^ (T - 1 - k)) ((U' - U) ((U ^ k) x)))
            ≤ (1 + δ) ^ (T - 1 - k) * stateNorm ((U' - U) ((U ^ k) x)) := h1
          _ ≤ (1 + δ) ^ (T - 1 - k) * (δ * stateNorm ((U ^ k) x)) := by
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ (1 + δ) ^ (T - 1 - k) * (δ * stateNorm x) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h3 hδ) (by positivity)
          _ = (1 + δ) ^ (T - 1 - k) * δ * stateNorm x := by ring
    _ = ((1 + δ) ^ T - 1) * stateNorm x := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 1
        rw [Finset.sum_range_reflect]
        have hg := geom_sum_mul (1 + δ) T
        rw [show (1 + δ) - 1 = δ by ring] at hg
        exact hg

/-- For `δ ≥ 0`, the geometric increment `(1 + δ) ^ T - 1` is at most `T * δ * (1 + δ) ^ (T -
1)`. -/
theorem geometric_growth_bound {δ : ℝ} (hδ : 0 ≤ δ) (T : ℕ) :
    (1 + δ) ^ T - 1 ≤ (T : ℝ) * δ * (1 + δ) ^ (T - 1) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · have hg : (∑ j ∈ Finset.range T, (1 + δ) ^ j) * δ = (1 + δ) ^ T - 1 := by
      have h := geom_sum_mul (1 + δ) T
      rw [show (1 + δ) - 1 = δ by ring] at h
      exact h
    rw [← hg]
    have hbase : (1 : ℝ) ≤ 1 + δ := by linarith
    have hsum : ∑ j ∈ Finset.range T, (1 + δ) ^ j ≤ (T : ℝ) * (1 + δ) ^ (T - 1) := by
      calc ∑ j ∈ Finset.range T, (1 + δ) ^ j
          ≤ ∑ _j ∈ Finset.range T, (1 + δ) ^ (T - 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_range] at hj
            exact pow_le_pow_right₀ hbase (by omega)
        _ = (T : ℝ) * (1 + δ) ^ (T - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (∑ j ∈ Finset.range T, (1 + δ) ^ j) * δ
        ≤ ((T : ℝ) * (1 + δ) ^ (T - 1)) * δ :=
          mul_le_mul_of_nonneg_right hsum hδ
      _ = (T : ℝ) * δ * (1 + δ) ^ (T - 1) := by ring

/-- For `δ ≥ 0`, `1 ≤ T`, and `δ * T ≤ 1`, the factor `(1 + δ) ^ (T - 1)` is at most `3`. -/
theorem one_add_pow_le_three {δ : ℝ} (hδ : 0 ≤ δ) {T : ℕ} (hT : 1 ≤ T)
    (hδT : δ * T ≤ 1) : (1 + δ) ^ (T - 1) ≤ 3 := by
  have hTreal : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hexp : (1 + δ) ^ (T - 1) ≤ Real.exp (δ * (T - 1)) := by
    have h1 : (1 + δ) ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    have h0 : (0 : ℝ) ≤ 1 + δ := by positivity
    calc (1 + δ) ^ (T - 1) ≤ (Real.exp δ) ^ (T - 1) := pow_le_pow_left₀ h0 h1 _
      _ = Real.exp (δ * (T - 1)) := by
          rw [show δ * (T - 1) = (T - 1) * δ by ring, ← Real.exp_nat_mul]
          congr 1
          rw [Nat.cast_sub hT]
          ring
  have hle : δ * (T - 1) ≤ δ * T := by nlinarith
  calc (1 + δ) ^ (T - 1) ≤ Real.exp (δ * (T - 1)) := hexp
    _ ≤ Real.exp (δ * T) := Real.exp_le_exp.mpr hle
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hδT
    _ ≤ 3 := le_of_lt Real.exp_one_lt_three

/-- For `δ ≥ 0` and `δ * T ≤ 1`, the factor `(1 + δ) ^ T` is at most `3`. -/
theorem one_add_pow_le_three_T {δ : ℝ} (hδ : 0 ≤ δ) {T : ℕ} (hδT : δ * T ≤ 1) :
    (1 + δ) ^ T ≤ 3 := by
  have hexp : (1 + δ) ^ T ≤ Real.exp (δ * T) := by
    have h1 : (1 + δ) ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    have h0 : (0 : ℝ) ≤ 1 + δ := by positivity
    calc (1 + δ) ^ T ≤ (Real.exp δ) ^ T := pow_le_pow_left₀ h0 h1 _
      _ = Real.exp (δ * T) := by
          rw [show δ * T = (T : ℝ) * δ by ring, ← Real.exp_nat_mul]
  calc (1 + δ) ^ T ≤ Real.exp (δ * T) := hexp
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hδT
    _ ≤ 3 := le_of_lt Real.exp_one_lt_three

/-- For a normalized input, a state-norm-preserving `U`, and a perturbation of relative size `δ
≥ 0` with `1 ≤ T` and `δ * T ≤ 1`, the error after `T` iterations is at most `3 * T * δ`. -/
theorem stateNorm_accuracy_bound {I : Type*} [Fintype I]
    (U U' : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hΔ : ∀ ψ, stateNorm ((U' - U) ψ) ≤ δ * stateNorm ψ)
    {T : ℕ} (hT : 1 ≤ T) (hδT : δ * T ≤ 1)
    (x : QState I) (hx : stateNorm x = 1) :
    stateNorm ((U' ^ T) x - (U ^ T) x) ≤ (T : ℝ) * δ * 3 := by
  have hmain := stateNorm_perturbed_powers U U' hU hδ hΔ x T
  rw [hx, mul_one] at hmain
  calc stateNorm ((U' ^ T) x - (U ^ T) x) ≤ (1 + δ) ^ T - 1 := hmain
    _ ≤ (T : ℝ) * δ * (1 + δ) ^ (T - 1) := geometric_growth_bound hδ T
    _ ≤ (T : ℝ) * δ * 3 := by
        exact mul_le_mul_of_nonneg_left (one_add_pow_le_three hδ hT hδT) (by positivity)

/-- For normalized input, norm-preserving `U`, `1 ≤ T`, and `0 < ε ≤ 12`, a relative
perturbation bound `ε / (12 * T)` yields state error at most `ε / 4` after `T` iterations.
This is the finite-state precision estimate used for [BernsteinVazirani1997]. -/
theorem corollary_3_4_4_bound {I : Type*} [Fintype I]
    (U U' : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    {T : ℕ} {ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) (hε12 : ε ≤ 12)
    (hΔ : ∀ ψ, stateNorm ((U' - U) ψ) ≤ (ε / (12 * T)) * stateNorm ψ)
    (x : QState I) (hx : stateNorm x = 1) :
    stateNorm ((U' ^ T) x - (U ^ T) x) ≤ ε / 4 := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hδ0 : (0 : ℝ) ≤ ε / (12 * T) := by positivity
  have hδT : (ε / (12 * T)) * T ≤ 1 := by
    have heq : ε / (12 * T) * T = ε / 12 := by
      have hT0 : (T : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq]
    linarith
  have hmain := stateNorm_accuracy_bound U U' hU hδ0 hΔ hT hδT x hx
  have harith : (T : ℝ) * (ε / (12 * T)) * 3 = ε / 4 := by
    field_simp
    ring
  rwa [harith] at hmain

/-- If the state norms of `ψ` and `φ` are bounded by nonnegative `a` and `b` and their distance
is at most `g`, their Born weights have total variation at most `(a + b) * g / 2`. -/
theorem totalVariation_born_le_of_bounds {I : Type*} [Fintype I] (ψ φ : QState I)
    {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hψ : stateNorm ψ ≤ a) (hφ : stateNorm φ ≤ b) (h : stateNorm (ψ - φ) ≤ g) :
    totalVariation (BornProb ψ) (BornProb φ) ≤ (1 / 2) * ((a + b) * g) := by
  have h1 := born_gap_sum_le ψ φ
  have h2 : (stateNorm ψ + stateNorm φ) * stateNorm (ψ - φ) ≤ (a + b) * g := by
    have hle1 : stateNorm ψ + stateNorm φ ≤ a + b := add_le_add hψ hφ
    exact mul_le_mul hle1 h (stateNorm_nonneg _) (by positivity)
  rw [totalVariation]
  nlinarith

/-- For normalized input, norm-preserving `U`, `1 ≤ T`, and `0 < ε ≤ 12`, a relative
perturbation bound `ε / (12 * T)` yields total variation at most `ε` between the Born
weights after `T` iterations, as required in the precision analysis of
[BernsteinVazirani1997]. -/
theorem observation_accuracy_bound {I : Type*} [Fintype I]
    (U U' : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    {T : ℕ} {ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) (hε12 : ε ≤ 12)
    (hΔ : ∀ ψ, stateNorm ((U' - U) ψ) ≤ (ε / (12 * T)) * stateNorm ψ)
    (x : QState I) (hx : stateNorm x = 1) :
    totalVariation (BornProb ((U' ^ T) x)) (BornProb ((U ^ T) x)) ≤ ε := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hgap := corollary_3_4_4_bound U U' hU hT hε hε12 hΔ x hx
  have hδ0 : (0 : ℝ) ≤ ε / (12 * T) := by positivity
  have hδT : (ε / (12 * T)) * T ≤ 1 := by
    have heq : ε / (12 * T) * T = ε / 12 := by
      have hT0 : (T : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq]
    linarith
  have hψ : stateNorm ((U' ^ T) x) ≤ 3 := by
    have h := stateNorm_pow_le' U U' hU hδ0 hΔ T x
    rw [hx, mul_one] at h
    exact h.trans (one_add_pow_le_three_T hδ0 hδT)
  have hφ : stateNorm ((U ^ T) x) ≤ 1 := by
    have h := stateNorm_pow_le U hU T x
    rwa [hx] at h
  have htv := totalVariation_born_le_of_bounds ((U' ^ T) x) ((U ^ T) x)
    (a := 3) (b := 1) (g := ε / 4) (by norm_num) (by norm_num) hψ hφ hgap
  have harith : (1 / 2 : ℝ) * ((3 + 1) * (ε / 4)) = ε / 2 := by ring
  rw [harith] at htv
  linarith

/-- The basis ket of a native machine configuration has norm `1`. -/
theorem ket_norm {Q A : Type*} {blank : A} (c : Config Q A blank) : ‖ket c‖ = 1 := by
  classical
  rw [ket, lp.norm_single (by norm_num)]
  simp

/-- For a fixed source configuration, distinct move-state-symbol triples give distinct target
configurations. -/
theorem target_injective {Q A : Type*} {blank : A} (c : Config Q A blank) :
    Function.Injective (fun t : Move × Q × A => target c t.1 t.2.1 t.2.2) := by
  rintro ⟨m, q, a⟩ ⟨m', q', a'⟩ h
  have hm : m = m' := Move.offset_injective (by
    have hh : c.head + m.offset = c.head + m'.offset := by
      simpa [target] using congrArg Config.head h
    exact add_left_cancel hh)
  have hq : q = q' := by
    have hh := congrArg Config.state h
    simpa [target] using hh
  have ha : a = a' := by
    have hh := congrArg (fun cfg : Config Q A _ => cfg.tape c.head) h
    simpa [target, Tape.write_same] using hh
  subst hm; subst hq; subst ha; rfl

/-- If every transition amplitude changes by at most `b`, the norm of each rule-column
difference is at most `Fintype.card (Move × Q × A) * b`. -/
theorem rule_column_perturb_le {Q A : Type*} [Fintype Q] [Fintype A]
    {blank : A} (ampl ampl' : Q → A → Move → Q → A → ℂ) {b : ℝ}
    (hb : ∀ (q : Q) (a : A) (m : Move) (q' : Q) (a' : A),
      ‖ampl q a m q' a' - ampl' q a m q' a'‖ ≤ b)
    (c : Config Q A blank) :
    ‖(⟨blank, ampl⟩ : Rule Q A).column c - (⟨blank, ampl'⟩ : Rule Q A).column c‖
      ≤ (Fintype.card (Move × Q × A) : ℝ) * b := by
  have hcol : (⟨blank, ampl⟩ : Rule Q A).column c -
      (⟨blank, ampl'⟩ : Rule Q A).column c =
      ∑ t : Move × Q × A,
        (ampl c.state (c.tape c.head) t.1 t.2.1 t.2.2 -
         ampl' c.state (c.tape c.head) t.1 t.2.1 t.2.2) •
        ket (target c t.1 t.2.1 t.2.2) := by
    rw [Rule.column, Rule.column, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [sub_smul]
  rw [hcol]
  calc ‖∑ t : Move × Q × A,
        (ampl c.state (c.tape c.head) t.1 t.2.1 t.2.2 -
         ampl' c.state (c.tape c.head) t.1 t.2.1 t.2.2) •
        ket (target c t.1 t.2.1 t.2.2)‖
      ≤ ∑ t : Move × Q × A,
          ‖(ampl c.state (c.tape c.head) t.1 t.2.1 t.2.2 -
           ampl' c.state (c.tape c.head) t.1 t.2.1 t.2.2) •
          ket (target c t.1 t.2.1 t.2.2)‖ := norm_sum_le _ _
    _ ≤ ∑ _t : Move × Q × A, b := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [norm_smul, ket_norm, mul_one]
        exact hb _ _ _ _ _
    _ = (Fintype.card (Move × Q × A) : ℝ) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Qatlib.Papers.QComplexity97.PrecisionModel
