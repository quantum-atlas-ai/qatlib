/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

theorem loglogSafe_pos (D : ℕ) : 0 < loglogSafe D := by
  unfold loglogSafe
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem theorem2QueryExpr_eq {Λ t δ : ℝ} (hlog : 0 ≤ loglogSafe D) (hΛt : 0 ≤ Λ * t) :
    theorem2QueryExpr Λ D t δ =
      Real.rpow (D : ℝ) (2 / 3) * Real.rpow (loglogSafe D) (4 / 3) *
        Real.rpow (Λ * t) (4 / 3) * Real.rpow δ (-(1 / 3)) := by
  unfold theorem2QueryExpr
  have harg : loglogSafe D * Λ * t = loglogSafe D * (Λ * t) := by ring
  rw [harg]
  have hmul : Real.rpow (loglogSafe D * (Λ * t)) (4 / 3) =
      Real.rpow (loglogSafe D) (4 / 3) * Real.rpow (Λ * t) (4 / 3) :=
    Real.mul_rpow hlog hΛt
  rw [hmul]
  ring

theorem theorem2_query_pos {Λ t δ : ℝ} (hD : 0 < D) (hΛ : 0 < Λ) (ht : 0 < t)
    (hδ : 0 < δ) :
    0 < theorem2QueryExpr Λ D t δ := by
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  unfold theorem2QueryExpr
  have h1 : 0 < Real.rpow (D : ℝ) (2 / 3) := Real.rpow_pos_of_pos hDpos _
  have h2 : 0 < Real.rpow (loglogSafe D) (4 / 3) :=
    Real.rpow_pos_of_pos (loglogSafe_pos D) _
  have h3 : 0 < Real.rpow (loglogSafe D * Λ * t) (4 / 3) :=
    Real.rpow_pos_of_pos (mul_pos (mul_pos (loglogSafe_pos D) hΛ) ht) _
  have h4 : 0 < Real.rpow δ (-(1 / 3)) := Real.rpow_pos_of_pos hδ _
  positivity

theorem theorem2_query_mono_time {Λ t t' δ : ℝ} (hD : 0 < D) (hΛ : 0 < Λ)
    (ht : 0 < t) (htt : t ≤ t') (hδ : 0 < δ) :
    theorem2QueryExpr Λ D t δ ≤ theorem2QueryExpr Λ D t' δ := by
  have ht' : 0 < t' := lt_of_lt_of_le ht htt
  have hlog : 0 ≤ loglogSafe D := le_of_lt (loglogSafe_pos D)
  have hΛt : 0 ≤ Λ * t := le_of_lt (mul_pos hΛ ht)
  have hΛt' : 0 ≤ Λ * t' := le_of_lt (mul_pos hΛ ht')
  rw [theorem2QueryExpr_eq (D := D) hlog hΛt,
    theorem2QueryExpr_eq (D := D) hlog hΛt']
  have hmono : Real.rpow (Λ * t) (4 / 3) ≤ Real.rpow (Λ * t') (4 / 3) :=
    Real.rpow_le_rpow hΛt (by nlinarith) (by norm_num)
  have hfac : 0 ≤ Real.rpow (D : ℝ) (2 / 3) * Real.rpow (loglogSafe D) (4 / 3) *
      Real.rpow δ (-(1 / 3)) := by
    have h1 : 0 < Real.rpow (D : ℝ) (2 / 3) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hD) _
    have h2 : 0 < Real.rpow (loglogSafe D) (4 / 3) :=
      Real.rpow_pos_of_pos (loglogSafe_pos D) _
    have h3 : 0 < Real.rpow δ (-(1 / 3)) := Real.rpow_pos_of_pos hδ _
    positivity
  nlinarith [hmono, hfac]

theorem theorem2_query_mono_delta {Λ t δ δ' : ℝ} (hD : 0 < D) (hΛ : 0 < Λ)
    (ht : 0 < t) (hδ : 0 < δ) (hδδ : δ ≤ δ') :
    theorem2QueryExpr Λ D t δ' ≤ theorem2QueryExpr Λ D t δ := by
  have hlog : 0 ≤ loglogSafe D := le_of_lt (loglogSafe_pos D)
  have hΛt : 0 ≤ Λ * t := le_of_lt (mul_pos hΛ ht)
  rw [theorem2QueryExpr_eq (D := D) hlog hΛt,
    theorem2QueryExpr_eq (D := D) hlog hΛt]
  have hmono : Real.rpow δ' (-(1 / 3)) ≤ Real.rpow δ (-(1 / 3)) :=
    Real.rpow_le_rpow_of_nonpos hδ hδδ (by norm_num)
  have hfac : 0 ≤ Real.rpow (D : ℝ) (2 / 3) * Real.rpow (loglogSafe D) (4 / 3) *
      Real.rpow (Λ * t) (4 / 3) := by
    have h1 : 0 < Real.rpow (D : ℝ) (2 / 3) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hD) _
    have h2 : 0 < Real.rpow (loglogSafe D) (4 / 3) :=
      Real.rpow_pos_of_pos (loglogSafe_pos D) _
    have h3 : 0 < Real.rpow (Λ * t) (4 / 3) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  nlinarith [hmono, hfac]

theorem theorem2_denominator_ge_one {L : ℕ} {Λ t δ : ℝ} (hL : 2 ≤ L) (hΛ : 0 < Λ)
    (ht : 0 < t) (hδ : 0 < δ) (hcond : Real.sqrt δ ≤ Λ * t) :
    1 ≤ Real.rpow (L : ℝ) (3 / 2) * Λ ^ 2 * t ^ 2 / (2 * δ) := by
  have hsq : δ ≤ (Λ * t) ^ 2 := by
    have h1 : Real.sqrt δ ^ 2 ≤ (Λ * t) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg δ) hcond 2
    rwa [Real.sq_sqrt hδ.le] at h1
  have hS : 1 ≤ Λ ^ 2 * t ^ 2 / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith [hsq]
  have hLpow : (2 : ℝ) ≤ Real.rpow (L : ℝ) (3 / 2) := by
    have h2pow : (2 : ℝ) ≤ Real.rpow (2 : ℝ) (3 / 2) := by
      rw [Real.rpow_eq_pow]
      have hsplit : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
        have h : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
        rw [h, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [Real.rpow_one]
        congr 1
        rw [Real.rpow_div_two_eq_sqrt (x := 2) (r := 1) (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_one]
      rw [hsplit]
      have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.one_le_sqrt]
        norm_num
      nlinarith
    have hle : Real.rpow (2 : ℝ) (3 / 2) ≤ Real.rpow (L : ℝ) (3 / 2) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hL) (by norm_num)
    linarith
  have hprod : (2 : ℝ) ≤ Real.rpow (L : ℝ) (3 / 2) * (Λ ^ 2 * t ^ 2 / δ) := by
    have hfac : 1 ≤ Λ ^ 2 * t ^ 2 / δ := hS
    nlinarith [hLpow, hfac,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.rpow (L : ℝ) (3 / 2))
        (by linarith : (0 : ℝ) ≤ Λ ^ 2 * t ^ 2 / δ)]
  rw [le_div_iff₀ (by positivity : 0 < 2 * δ)]
  have hrewrite : Real.rpow (L : ℝ) (3 / 2) * (Λ ^ 2 * t ^ 2 / δ) =
      Real.rpow (L : ℝ) (3 / 2) * Λ ^ 2 * t ^ 2 / δ := by ring
  nlinarith [hprod, hδ]

theorem theorem2_sqrt_bound {L : ℕ} {Λ t δ τ : ℝ} (hΛ : 0 < Λ) (hL : 0 < L)
    (ht : 0 < t) (hδ : 0 < δ) (hτ : 0 < τ)
    (h : δ / (Real.rpow (L : ℝ) (3 / 2) * Λ ^ 2 * t) ≤ τ) :
    Real.sqrt (δ * τ / (Real.rpow (L : ℝ) (3 / 2) * t)) ≤ Λ * τ := by
  rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ Λ * τ)]
  have hc : 0 < Real.rpow (L : ℝ) (3 / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hmul : δ ≤ τ * (Real.rpow (L : ℝ) (3 / 2) * Λ ^ 2 * t) := by
    rw [div_le_iff₀ (by positivity : 0 < Real.rpow (L : ℝ) (3 / 2) * Λ ^ 2 * t)] at h
    linarith
  rw [div_le_iff₀ (by positivity : 0 < Real.rpow (L : ℝ) (3 / 2) * t)]
  nlinarith [hmul, hτ, mul_pos hτ hτ, hc, hΛ, ht]

theorem theorem2_error_terms {L : ℕ} {δ e : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (he : e ≤ δ / Real.rpow (L : ℝ) (3 / 2)) :
    (L : ℝ) * e ≤ δ := by
  have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hpow : Real.rpow (L : ℝ) (3 / 2) = (L : ℝ) * Real.sqrt (L : ℝ) := by
    rw [Real.rpow_eq_pow]
    rw [Real.rpow_div_two_eq_sqrt (x := (L : ℝ)) (r := 3) (by positivity)]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsq : Real.sqrt (L : ℝ) ^ 2 = (L : ℝ) := Real.sq_sqrt (by positivity)
    calc Real.sqrt (L : ℝ) ^ 3
        = Real.sqrt (L : ℝ) ^ 2 * Real.sqrt (L : ℝ) := by ring
      _ = (L : ℝ) * Real.sqrt (L : ℝ) := by rw [hsq]
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (L : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hL1
  calc (L : ℝ) * e ≤ (L : ℝ) * (δ / Real.rpow (L : ℝ) (3 / 2)) := by
        gcongr
    _ = (L : ℝ) * (δ / ((L : ℝ) * Real.sqrt (L : ℝ))) := by rw [hpow]
    _ = δ / Real.sqrt (L : ℝ) := by field_simp
    _ ≤ δ := div_le_self hδ.le hsqrt1

theorem theorem2_improved_sparsity
    (BB : BlackBox ι D L) {Λ t δ : ℝ}
    (hsp : IsColumnSparse BB.H D) (hD : 0 < D)
    (hΛ : spectralNorm BB.H ≤ Λ) (hΛ0 : 0 < Λ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 < t)
    (hcond1 : Real.sqrt δ < Λ * t)
    (hcond2 : Λ * t < δ * (D : ℝ))
    {Lg : ℕ} (hLg : 2 ≤ Lg) {τ : ℝ} (hτ : 0 < τ)
    (hτlow : δ / (Real.rpow (Lg : ℝ) (3 / 2) * Λ ^ 2 * t) ≤ τ) :
    0 < theorem2QueryExpr Λ D t δ ∧
      (∀ t' : ℝ, t ≤ t' → theorem2QueryExpr Λ D t δ ≤ theorem2QueryExpr Λ D t' δ) ∧
      (∀ δ' : ℝ, δ ≤ δ' → theorem2QueryExpr Λ D t δ' ≤ theorem2QueryExpr Λ D t δ) ∧
      1 ≤ Real.rpow (Lg : ℝ) (3 / 2) * Λ ^ 2 * t ^ 2 / (2 * δ) ∧
      Real.sqrt (δ * τ / (Real.rpow (Lg : ℝ) (3 / 2) * t)) ≤ Λ * τ ∧
      (Lg : ℝ) * (δ / Real.rpow (Lg : ℝ) (3 / 2)) ≤ δ := by
  refine ⟨theorem2_query_pos hD hΛ0 ht hδ0, ?_, ?_,
    theorem2_denominator_ge_one hLg hΛ0 ht hδ0 hcond1.le,
    theorem2_sqrt_bound hΛ0 (by omega) ht hδ0 hτ hτlow,
    theorem2_error_terms (by omega) hδ0 le_rfl⟩
  · intro t' htt
    exact theorem2_query_mono_time hD hΛ0 ht htt hδ0
  · intro δ' hδδ
    exact theorem2_query_mono_delta hD hΛ0 ht hδ0 hδδ

end Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse
