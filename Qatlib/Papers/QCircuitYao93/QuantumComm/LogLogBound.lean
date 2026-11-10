/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircuitYao93.QuantumComm.ProtocolLowerBound
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QuantumComm.LogLogBound

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QCircuitYao93.QuantumComm.ProtocolLowerBound

theorem feature_count_lower {ι : Type} [Fintype ι] [DecidableEq ι] {n k l : ℕ}
    {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (ha : ∀ x ε, ∑ i, ‖a x ε i‖ ^ 2 = 1)
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    (hgap : 6 * (Fintype.card ι : ℝ) ^ 2 < L ^ 3)
    (hacc : ∀ x y : Fin n → Bool, n ≤ wordWeight x + wordWeight y →
      (2 : ℝ) / 3 < acceptProb a b x y)
    (hrej : ∀ x y : Fin n → Bool, wordWeight x + wordWeight y < n →
      acceptProb a b x y < (1 : ℝ) / 3) :
    n + 1 ≤ Fintype.card (FeatureSpace M ι) := by
  classical
  by_contra h
  exact theorem4_no_cheap_protocol hLpos hLM a b ha hb
    (Nat.lt_of_not_le h) hgap hacc hrej

theorem feature_count_lower_pow {ι : Type} [Fintype ι] [DecidableEq ι] {n k l t : ℕ}
    {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (ha : ∀ x ε, ∑ i, ‖a x ε i‖ ^ 2 = 1)
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    (hcard : Fintype.card ι = 2 ^ (t - 1))
    (hgap : 6 * (Fintype.card ι : ℝ) ^ 2 < L ^ 3)
    (hacc : ∀ x y : Fin n → Bool, n ≤ wordWeight x + wordWeight y →
      (2 : ℝ) / 3 < acceptProb a b x y)
    (hrej : ∀ x y : Fin n → Bool, wordWeight x + wordWeight y < n →
      acceptProb a b x y < (1 : ℝ) / 3) :
    n + 1 ≤ (2 * M + 1) ^ (2 * (2 ^ (t - 1)) * (2 ^ (t - 1))) := by
  classical
  have h := feature_count_lower hLpos hLM a b ha hb hgap hacc hrej
  rw [card_featureSpace] at h
  rwa [hcard] at h

theorem wires_dichotomy {ι : Type} [Fintype ι] [DecidableEq ι] {n k l t : ℕ}
    {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (ha : ∀ x ε, ∑ i, ‖a x ε i‖ ^ 2 = 1)
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    (hcard : Fintype.card ι = 2 ^ (t - 1))
    (hacc : ∀ x y : Fin n → Bool, n ≤ wordWeight x + wordWeight y →
      (2 : ℝ) / 3 < acceptProb a b x y)
    (hrej : ∀ x y : Fin n → Bool, wordWeight x + wordWeight y < n →
      acceptProb a b x y < (1 : ℝ) / 3) :
    L ^ 3 ≤ 6 * ((2 : ℝ) ^ (t - 1)) ^ 2 ∨
      n + 1 ≤ (2 * M + 1) ^ (2 * (2 ^ (t - 1)) * (2 ^ (t - 1))) := by
  classical
  by_cases hgap : 6 * (Fintype.card ι : ℝ) ^ 2 < L ^ 3
  · right
    exact feature_count_lower_pow hLpos hLM a b ha hb hcard hgap hacc hrej
  · left
    have hge : L ^ 3 ≤ 6 * (Fintype.card ι : ℝ) ^ 2 := by
      have := not_lt.mp hgap
      linarith
    rw [hcard] at hge
    have hcast : ((2 ^ (t - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (t - 1) := by push_cast; ring
    rw [hcast] at hge
    exact hge

theorem log_feature_bound {n M t : ℕ} (hM : 1 ≤ M)
    (h : n + 1 ≤ (2 * M + 1) ^ (2 * (2 ^ (t - 1)) * (2 ^ (t - 1)))) :
    Real.log ((n : ℝ) + 1) / Real.log (((2 * M + 1 : ℕ) : ℝ)) ≤
      2 * ((2 : ℝ) ^ (t - 1)) ^ 2 := by
  classical
  have hcast : ((n : ℝ) + 1) ≤
      (((2 * M + 1 : ℕ) : ℝ)) ^ (2 * (2 ^ (t - 1)) * (2 ^ (t - 1))) := by
    exact_mod_cast h
  have hbase : (1 : ℝ) < (((2 * M + 1 : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ (((2 * M + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show (2 : ℕ) ≤ 2 * M + 1 by omega)
    linarith
  have hpos : 0 < Real.log (((2 * M + 1 : ℕ) : ℝ)) := Real.log_pos hbase
  have hlog : Real.log ((n : ℝ) + 1) ≤
      (2 * (2 ^ (t - 1)) * (2 ^ (t - 1)) : ℕ) * Real.log (((2 * M + 1 : ℕ) : ℝ)) := by
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < ((n : ℝ) + 1)) hcast
    rwa [Real.log_pow] at h1
  rw [div_le_iff₀ hpos]
  calc Real.log ((n : ℝ) + 1)
      ≤ (2 * (2 ^ (t - 1)) * (2 ^ (t - 1)) : ℕ) * Real.log (((2 * M + 1 : ℕ) : ℝ)) := hlog
    _ = 2 * ((2 : ℝ) ^ (t - 1)) ^ 2 * Real.log (((2 * M + 1 : ℕ) : ℝ)) := by
        push_cast
        ring

theorem wires_dichotomy_log {ι : Type} [Fintype ι] [DecidableEq ι] {n k l t : ℕ}
    {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ)) (hM : 1 ≤ M)
    (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (ha : ∀ x ε, ∑ i, ‖a x ε i‖ ^ 2 = 1)
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    (hcard : Fintype.card ι = 2 ^ (t - 1))
    (hacc : ∀ x y : Fin n → Bool, n ≤ wordWeight x + wordWeight y →
      (2 : ℝ) / 3 < acceptProb a b x y)
    (hrej : ∀ x y : Fin n → Bool, wordWeight x + wordWeight y < n →
      acceptProb a b x y < (1 : ℝ) / 3) :
    L ^ 3 ≤ 6 * ((2 : ℝ) ^ (t - 1)) ^ 2 ∨
      Real.log ((n : ℝ) + 1) / Real.log (((2 * M + 1 : ℕ) : ℝ)) ≤
        2 * ((2 : ℝ) ^ (t - 1)) ^ 2 := by
  classical
  rcases wires_dichotomy hLpos hLM a b ha hb hcard hacc hrej with h | h
  · exact Or.inl h
  · exact Or.inr (log_feature_bound hM h)

theorem t_lower_from_feature {n M t : ℕ} (hM : 1 ≤ M) (hn : 2 ≤ n) (ht : 1 ≤ t)
    (h : n + 1 ≤ (2 * M + 1) ^ (2 * (2 ^ (t - 1)) * (2 ^ (t - 1)))) :
    Real.logb 2 (Real.log ((n : ℝ) + 1) / Real.log (((2 * M + 1 : ℕ) : ℝ))) ≤
      2 * (t : ℝ) - 1 := by
  classical
  have hn1 : (1 : ℝ) < ((n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by omega)
    linarith
  have hbase : (1 : ℝ) < (((2 * M + 1 : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ (((2 * M + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show (2 : ℕ) ≤ 2 * M + 1 by omega)
    linarith
  have hXpos : 0 < Real.log ((n : ℝ) + 1) / Real.log (((2 * M + 1 : ℕ) : ℝ)) :=
    div_pos (Real.log_pos hn1) (Real.log_pos hbase)
  have hle := log_feature_bound hM h
  have hpow : 2 * ((2 : ℝ) ^ (t - 1)) ^ 2 = (2 : ℝ) ^ (2 * t - 1) := by
    rw [← pow_mul]
    have hexp : 2 * t - 1 = (t - 1) * 2 + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [hpow] at hle
  have hmono := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hXpos hle
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hmono
  have hsub : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht]
    norm_num
  have hcast : ((2 * t - 1 : ℕ) : ℝ) = 2 * (t : ℝ) - 1 := by
    have h2 : 2 * t - 1 = 2 * (t - 1) + 1 := by omega
    rw [h2]
    push_cast
    rw [hsub]
    ring
  linarith [hcast]

end Qatlib.Papers.QCircuitYao93.QuantumComm.LogLogBound
