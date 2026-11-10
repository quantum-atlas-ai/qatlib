/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.AdiabHypergph12.SymmetrySector

noncomputable section

open Filter
open scoped BigOperators

def diagFilter {n : ℕ} (lam : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => lam i * v i

theorem diagFilter_iterate {n : ℕ} (lam : Fin (n + 1) → ℝ) (m : ℕ)
    (v : Fin (n + 1) → ℝ) :
    (diagFilter lam)^[m] v = fun i => (lam i)^m * v i := by
  induction m generalizing v with
  | zero => funext i; simp
  | succ m ih =>
      funext i
      rw [Function.iterate_succ_apply', ih v]
      simp only [diagFilter]
      rw [pow_succ]
      ring

theorem diagFilter_eigen {n : ℕ} (lam : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    diagFilter lam (Pi.single i (1 : ℝ)) = lam i • Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [diagFilter]
  · simp [diagFilter, h]

def groundWeight {n : ℕ} (lam : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℝ)
    (m : ℕ) : ℝ :=
  (lam 0)^(2 * m) * (v 0)^2 / (∑ i, (lam i)^(2 * m) * (v i)^2)

theorem groundWeight_eq {n : ℕ} (lam : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℝ)
    (m : ℕ) (h0 : lam 0 ≠ 0) :
    groundWeight lam v m
      = (v 0)^2 / (∑ i, (lam i / lam 0)^(2 * m) * (v i)^2) := by
  unfold groundWeight
  have hden : (∑ i, (lam i)^(2 * m) * (v i)^2)
      = (lam 0)^(2 * m) * (∑ i, (lam i / lam 0)^(2 * m) * (v i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have ha : (lam 0)^(2 * m) ≠ 0 := pow_ne_zero _ h0
    rw [div_pow]
    field_simp
  rw [hden]
  exact mul_div_mul_left ((v 0)^2)
    (∑ i, (lam i / lam 0)^(2 * m) * (v i)^2) (pow_ne_zero _ h0)

theorem groundWeight_tendsto {n : ℕ} (lam : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℝ) (h0 : 0 < lam 0)
    (hgap : ∀ i, i ≠ 0 → |lam i| < lam 0) (hv : v 0 ≠ 0) :
    Tendsto (fun m => groundWeight lam v m) atTop (nhds 1) := by
  have hlamp : lam 0 ≠ 0 := ne_of_gt h0
  have hterm : ∀ i : Fin (n + 1),
      Tendsto (fun m => (lam i / lam 0)^(2 * m) * (v i)^2) atTop
        (nhds ((if i = 0 then (1 : ℝ) else 0) * (v i)^2)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simp [hlamp]
    · have hratio : |lam i / lam 0| < 1 := by
        rw [abs_div, abs_of_pos h0, div_lt_one h0]
        exact hgap i hi
      obtain ⟨hr1, hr2⟩ := abs_lt.mp hratio
      have hsq : (lam i / lam 0)^2 < 1 := by nlinarith
      have hge : 0 ≤ (lam i / lam 0)^2 := sq_nonneg _
      have hlim : Tendsto (fun m : ℕ => ((lam i / lam 0)^2)^m) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hge hsq
      have hscaled := hlim.mul_const ((v i)^2)
      simpa [pow_mul, hi] using hscaled
  have hsum : Tendsto
      (fun m => ∑ i, (lam i / lam 0)^(2 * m) * (v i)^2) atTop
      (nhds (∑ i, (if i = 0 then (1 : ℝ) else 0) * (v i)^2)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  have hlimsum : (∑ i, (if i = 0 then (1 : ℝ) else 0) * (v i)^2) = (v 0)^2 := by
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hlimsum] at hsum
  have hne : (v 0)^2 ≠ 0 := pow_ne_zero 2 hv
  have hconst : Tendsto (fun _ : ℕ => (v 0)^2) atTop (nhds ((v 0)^2)) :=
    tendsto_const_nhds
  have hdiv : Tendsto
      (fun m => (v 0)^2 / (∑ i, (lam i / lam 0)^(2 * m) * (v i)^2)) atTop
      (nhds ((v 0)^2 / (v 0)^2)) := by
    simpa [Pi.div_apply] using! hconst.div hsum hne
  have heq : (fun m => groundWeight lam v m)
      =ᶠ[atTop]
        (fun m => (v 0)^2 / (∑ i, (lam i / lam 0)^(2 * m) * (v i)^2)) :=
    Filter.Eventually.of_forall (fun m => groundWeight_eq lam v m hlamp)
  have hfinal := Tendsto.congr' heq.symm hdiv
  simpa [div_self hne] using hfinal

end

end Qatlib.Papers.AdiabHypergph12.SymmetrySector
