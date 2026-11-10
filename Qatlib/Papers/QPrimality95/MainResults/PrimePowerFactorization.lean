/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.OrderCounts
import Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.ExponentRecovery
import Qatlib.Papers.QPrimality95.MainResults.ComplexityAssembly
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QPrimality95.MainResults

theorem appendix_b_exact_order_success (p n : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 2 ≤ n) :
    (2 : ℚ) / 3 ≤
      (Nat.card {m : (ZMod (p ^ n))ˣ //
        p ^ n / Nat.gcd (p ^ n) (orderOf m) = p} : ℚ) /
        (Nat.card (ZMod (p ^ n))ˣ : ℚ) :=
  Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.prime_power_extraction_probability p n hp hp2 hn

noncomputable def primePowerCost (M : ℕ) : ℝ :=
  (Real.log (M : ℝ)) ^ 2 * (Real.log (Real.log (M : ℝ))) ^ 2 *
    Real.log (Real.log (Real.log (M : ℝ)))

theorem prime_power_cost_sum_of_bounds
    (orderCost extractCost : ℕ → ℝ) (C1 C2 : ℝ)
    (hC : 0 < C1 + C2)
    (horder : ∀ M : ℕ, 3 ≤ M → orderCost M ≤ C1 * primePowerCost M)
    (hextract : ∀ M : ℕ, 3 ≤ M → extractCost M ≤ C2 * primePowerCost M) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M →
      orderCost M + extractCost M ≤ C * primePowerCost M := by
  refine ⟨C1 + C2, hC, ?_⟩
  intro M hM
  calc
    orderCost M + extractCost M ≤ C1 * primePowerCost M + C2 * primePowerCost M :=
      add_le_add (horder M hM) (hextract M hM)
    _ = (C1 + C2) * primePowerCost M := by ring

theorem primePower_averaged_success (p n k : ℕ) [NeZero (p ^ n)] (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 2 ≤ n) (s : (ZMod (p ^ n))ˣ → ℝ) (hs : ∀ u, 0 ≤ s u)
    (hgood : ∀ u : (ZMod (p ^ n))ˣ, p ^ (n - 1) ∣ orderOf u →
      1 - (1 / 2 : ℝ) ^ k ≤ s u) :
    (2 : ℝ) / 3 * (1 - (1 / 2 : ℝ) ^ k) ≤
      (∑ u : (ZMod (p ^ n))ˣ, s u) / (Fintype.card (ZMod (p ^ n))ˣ : ℝ) := by
  classical
  set c : ℝ := 1 - (1 / 2 : ℝ) ^ k with hcdef
  have hc : 0 ≤ c := by
    have hle : (1 / 2 : ℝ) ^ k ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    simp only [hcdef]
    linarith
  set good : Finset (ZMod (p ^ n))ˣ :=
    Finset.univ.filter (fun u => p ^ (n - 1) ∣ orderOf u) with hgooddef
  have hgood' : ∀ u ∈ good, c ≤ s u := by
    intro u hu
    exact hgood u (Finset.mem_filter.mp hu).2
  have havg := average_success_ge s good c hc hs hgood'
  have hprob :=
    Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.prime_power_probability
      p n hp hp2 hn
  have hcard_good : (Nat.card {m : (ZMod (p ^ n))ˣ // p ^ (n - 1) ∣ orderOf m} : ℚ)
      = (good.card : ℚ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard_units : (Nat.card (ZMod (p ^ n))ˣ : ℚ)
      = (Fintype.card (ZMod (p ^ n))ˣ : ℚ) := by
    rw [Nat.card_eq_fintype_card]
  have hfracQ : (2 : ℚ) / 3 ≤
      (good.card : ℚ) / (Fintype.card (ZMod (p ^ n))ˣ : ℚ) := by
    rw [← hcard_good, ← hcard_units]
    exact hprob
  have hfracR : (2 : ℝ) / 3 ≤
      (good.card : ℝ) / (Fintype.card (ZMod (p ^ n))ˣ : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hfracQ
    push_cast at h
    exact h
  have hstep : (2 : ℝ) / 3 * c ≤
      c * (good.card : ℝ) / (Fintype.card (ZMod (p ^ n))ˣ : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hfracR hc
    calc (2 : ℝ) / 3 * c
        ≤ ((good.card : ℝ) / (Fintype.card (ZMod (p ^ n))ˣ : ℝ)) * c := h
      _ = c * (good.card : ℝ) / (Fintype.card (ZMod (p ^ n))ˣ : ℝ) := by ring
  exact hstep.trans havg

end Qatlib.Papers.QPrimality95.MainResults
