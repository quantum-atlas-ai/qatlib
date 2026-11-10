/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.ResidualCuts

open Qatlib.Papers.QMatchingFlow05.SearchTools

theorem exists_small_adjacent_product (n : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (sz : ℕ → ℝ) (hsz : ∀ i, 0 ≤ sz i)
    (hsum : (∑ i ∈ Finset.range (k + 1), sz i) ≤ n) (hn : 0 ≤ n) :
    ∃ i ∈ Finset.range k, sz i * sz (i + 1) ≤ (2 * n / (k : ℝ)) ^ 2 := by
  by_contra h
  push Not at h
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk0)
  set c : ℝ := 2 * n / (k : ℝ) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    positivity

  have hstrict : ∀ i ∈ Finset.range k, c < sz i + sz (i + 1) := by
    intro i hi
    have hprod : c ^ 2 < sz i * sz (i + 1) := h i hi
    by_contra hcon
    push Not at hcon
    have hsi : sz i ≤ c := by linarith [hsz i, hsz (i + 1), hcon]
    have hsj : sz (i + 1) ≤ c := by linarith [hsz i, hsz (i + 1), hcon]
    have hle : sz i * sz (i + 1) ≤ c * c :=
      mul_le_mul hsi hsj (hsz (i + 1)) hc0
    have hcc : c * c = c ^ 2 := by ring
    linarith [hprod, hle, hcc]
  have hlt : (∑ i ∈ Finset.range k, c) < ∑ i ∈ Finset.range k, (sz i + sz (i + 1)) := by
    refine Finset.sum_lt_sum (fun i hi => le_of_lt (hstrict i hi)) ?_
    exact ⟨0, Finset.mem_range.mpr hk0, hstrict 0 (Finset.mem_range.mpr hk0)⟩

  have hconst : (∑ i ∈ Finset.range k, c) = 2 * n := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hc]
    field_simp

  have h1 : (∑ i ∈ Finset.range k, sz i) ≤ ∑ i ∈ Finset.range (k + 1), sz i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.le_succ k))
      (fun x _ _ => hsz x)
  have h2 : (∑ i ∈ Finset.range k, sz (i + 1)) ≤ ∑ i ∈ Finset.range (k + 1), sz i := by
    have hsplit := Finset.sum_range_succ' sz k
    have h0 := hsz 0
    linarith [hsplit]
  have hdouble : (∑ i ∈ Finset.range k, (sz i + sz (i + 1))) ≤
      2 * (∑ i ∈ Finset.range (k + 1), sz i) := by
    rw [Finset.sum_add_distrib]
    linarith [h1, h2]
  have hupper : (∑ i ∈ Finset.range k, (sz i + sz (i + 1))) ≤ 2 * n := by
    nlinarith [hdouble, hsum]
  rw [hconst] at hlt
  linarith [hlt, hupper]

theorem exists_small_edge_layer (k m : ℕ) (hk : 1 ≤ k) (ec : ℕ → ℝ)
    (_hec : ∀ i, 0 ≤ ec i) (hsum : (∑ i ∈ Finset.range k, ec i) ≤ (m : ℝ)) :
    ∃ i ∈ Finset.range k, ec i ≤ (m : ℝ) / (k : ℝ) := by
  by_contra h
  push Not at h
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk0)
  have hconst : (∑ i ∈ Finset.range k, ((m : ℝ) / (k : ℝ))) = (m : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hlt : (∑ i ∈ Finset.range k, ((m : ℝ) / (k : ℝ))) <
      ∑ i ∈ Finset.range k, ec i := by
    refine Finset.sum_lt_sum (fun i hi => le_of_lt (h i hi)) ?_
    exact ⟨0, Finset.mem_range.mpr hk0, h 0 (Finset.mem_range.mpr hk0)⟩
  rw [hconst] at hlt
  linarith [hsum]

theorem residual_flow_vertex_bound (n k : ℕ) (U flow : ℝ) (hk : 1 ≤ k)
    (sz : ℕ → ℝ) (hsz : ∀ i, 0 ≤ sz i)
    (hsum : (∑ i ∈ Finset.range (k + 1), sz i) ≤ (n : ℝ))
    (hU : 0 ≤ U)
    (hflow : ∀ i ∈ Finset.range k, flow ≤ U * (sz i * sz (i + 1))) :
    flow ≤ U * (2 * (n : ℝ) / (k : ℝ)) ^ 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  obtain ⟨i, hi, hprod⟩ :=
    exists_small_adjacent_product (n : ℝ) k hk sz hsz hsum hn
  have hUle : U * (sz i * sz (i + 1)) ≤ U * (2 * (n : ℝ) / (k : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left hprod hU
  exact le_trans (hflow i hi) hUle

theorem residual_flow_edge_bound (k m : ℕ) (U flow : ℝ) (hk : 1 ≤ k)
    (ec : ℕ → ℝ) (hec : ∀ i, 0 ≤ ec i)
    (hsum : (∑ i ∈ Finset.range k, ec i) ≤ (m : ℝ))
    (hU : 0 ≤ U)
    (hflow : ∀ i ∈ Finset.range k, flow ≤ U * ec i) :
    flow ≤ U * ((m : ℝ) / (k : ℝ)) := by
  obtain ⟨i, hi, hle⟩ := exists_small_edge_layer k m hk ec hec hsum
  have hUle : U * ec i ≤ U * ((m : ℝ) / (k : ℝ)) :=
    mul_le_mul_of_nonneg_left hle hU
  exact le_trans (hflow i hi) hUle

theorem residual_flow_min_bound (n k m : ℕ) (U flow : ℝ) (hk : 1 ≤ k)
    (sz : ℕ → ℝ) (hsz : ∀ i, 0 ≤ sz i)
    (hsumv : (∑ i ∈ Finset.range (k + 1), sz i) ≤ (n : ℝ))
    (ec : ℕ → ℝ) (hec : ∀ i, 0 ≤ ec i)
    (hsume : (∑ i ∈ Finset.range k, ec i) ≤ (m : ℝ))
    (hU : 0 ≤ U)
    (hflowv : ∀ i ∈ Finset.range k, flow ≤ U * (sz i * sz (i + 1)))
    (hflowe : ∀ i ∈ Finset.range k, flow ≤ U * ec i) :
    flow ≤ min (U * (2 * (n : ℝ) / (k : ℝ)) ^ 2) (U * ((m : ℝ) / (k : ℝ))) :=
  le_min (residual_flow_vertex_bound n k U flow hk sz hsz hsumv hU hflowv)
    (residual_flow_edge_bound k m U flow hk ec hec hsume hU hflowe)

end Qatlib.Papers.QMatchingFlow05.ResidualCuts

end
