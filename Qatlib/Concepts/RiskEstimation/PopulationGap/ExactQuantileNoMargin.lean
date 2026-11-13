/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.ExactQuantileNoMargin
import Qatlib.Concepts.RiskEstimation.VaRQuantile.VaRAlgorithmFiniteRestrictedQuan

/-!
# Exact quantile bisection without a margin

This module proves exact bisection for a monotone finite CDF and applies it to a sorted support
list under unitary preparation. It also gives a counterexample showing that the unitarity
hypothesis in `riskExactQuantileNoMargin` is necessary.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `riskExactQuantileNoMargin`: For unitary preparation and a nonempty sorted list containing
  every loss, exact CDF bisection finds the first quantile index and its least threshold value
  for `0 < q < 1`, without a margin hypothesis; see [WoernerEgger2019].
* `exactQuantileNoMargin_counterexample_without_unitary`: The exact quantile bisection guarantee
  fails in general when the preparation matrix is not required to be unitary.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- Given a monotone finite sequence, a valid bracketing interval, and enough bisection fuel,
exact bisection returns an index in that interval whose value reaches `q` and whose
predecessors are all below `q`. -/
theorem exactBisect_spec (F : ℕ → ℝ) (q : ℝ) (len : ℕ)
    (hmono : ∀ u v, u ≤ v → v < len → F u ≤ F v) :
    ∀ (fuel lo hi : ℕ),
      lo ≤ hi → hi < len → hi - lo < 2 ^ fuel →
      (∀ u < lo, F u < q) → q ≤ F hi →
      let exactBisect : ℕ → ℕ → ℕ → ℕ := fun fuel lo hi =>
        Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
          (fun lo _ => lo)
          (fun _ rec lo hi => if hi ≤ lo then lo else
            let mid := (lo+hi)/2
            if q ≤ F mid then rec lo mid else rec (mid+1) hi)
          fuel lo hi
      let v := exactBisect fuel lo hi
      lo ≤ v ∧ v ≤ hi ∧ (∀ u < v, F u < q) ∧ q ≤ F v := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hlo _ hwidth hbelow habove
    have heq : lo = hi := by norm_num at hwidth; omega
    subst hi
    exact ⟨le_rfl, le_rfl, hbelow, habove⟩
  | succ fuel ih =>
    intro lo hi hlo hhi hwidth hbelow habove
    (try dsimp only)
    split_ifs with hstop hqmid
    · have heq : lo = hi := by omega
      subst hi
      exact ⟨le_rfl, le_rfl, hbelow, habove⟩
    · have hmidlo : lo ≤ (lo + hi) / 2 := by omega
      have hmidhi : (lo + hi) / 2 < hi := by omega
      have hwL : (lo + hi) / 2 - lo < 2 ^ fuel := by rw [pow_succ] at hwidth; omega
      obtain ⟨h1, h2, h3, h4⟩ := ih lo ((lo + hi) / 2) hmidlo (by omega) hwL hbelow hqmid
      exact ⟨h1, h2.trans hmidhi.le, h3, h4⟩
    · have hmidlo : lo ≤ (lo + hi) / 2 + 1 := by omega
      have hmidhi : (lo + hi) / 2 + 1 ≤ hi := by omega
      have hwR : hi - ((lo + hi) / 2 + 1) < 2 ^ fuel := by rw [pow_succ] at hwidth; omega
      have hbelowR : ∀ u < (lo + hi) / 2 + 1, F u < q := by
        intro u hu
        by_cases hulo : u < lo
        · exact hbelow u hulo
        · exact (hmono u ((lo + hi) / 2) (by omega) (by omega)).trans_lt (lt_of_not_ge hqmid)
      obtain ⟨h1, h2, h3, h4⟩ := ih ((lo + hi) / 2 + 1) hi hmidhi hhi hwR hbelowR habove
      exact ⟨hmidlo.trans h1, h2, h3, h4⟩

/-- For unitary preparation and a nonempty sorted list containing every loss, exact CDF
bisection finds the first quantile index and its least threshold value for `0 < q < 1`,
without a margin hypothesis; see [WoernerEgger2019]. -/
theorem riskExactQuantileNoMargin : ExactQuantileNoMargin := by
  show ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
      (loss : I → ℚ) (xs : List ℚ) (q : ℝ),
      A ∈ Matrix.unitaryGroup I ℂ →
      xs ≠ [] → xs.SortedLE → (∀ i, loss i ∈ xs) → 0 < q → q < 1 →
      let F := fun v : ℕ => riskCDF A j loss (xs.getD v 0)
      let exactBisect : ℕ → ℕ → ℕ → ℕ := fun fuel lo hi =>
        Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
          (fun lo _ => lo)
          (fun _ rec lo hi => if hi ≤ lo then lo else
            let mid := (lo+hi)/2
            if q ≤ F mid then rec lo mid else rec (mid+1) hi)
          fuel lo hi
      let v := exactBisect (Nat.clog 2 xs.length + 1) 0 (xs.length - 1)
      v < xs.length ∧
      (∀ u : ℕ, u < v → F u < q) ∧
      (q ≤ F v) ∧
      (∀ u : ℕ, u < xs.length → q ≤ F u → xs.getD v 0 ≤ xs.getD u 0)
  intro I _ _ A j loss xs q hA hxs hs hloss _ hq1 F exactBisect v
  have hlen : 0 < xs.length := List.length_pos_of_ne_nil hxs
  have hlast : F (xs.length - 1) = 1 := by
    dsimp [F]
    have hh : xs.getD (xs.length - 1) 0 = xs.getLastD 0 := by
      simp only [List.getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    rw [hh]
    exact riskCDF_last A j loss xs hA hxs hs hloss
  have hd : xs.length - 1 - 0 < 2 ^ (Nat.clog 2 xs.length + 1) := by
    have hh := Nat.le_pow_clog (by norm_num : 1 < 2) xs.length
    rw [pow_succ]; omega
  obtain ⟨_, hvhi, hbelow, habove⟩ := exactBisect_spec F q xs.length
    (fun u w huw hw => riskCDF_indices A j loss xs hs u w (by omega) hw huw)
    (Nat.clog 2 xs.length + 1) 0 (xs.length - 1) (by omega) (by omega) hd
    (by intro u hu; omega) (by rw [hlast]; exact hq1.le)
  have hvv : v < xs.length := Nat.lt_of_le_of_lt hvhi (by omega)
  refine ⟨hvv, hbelow, habove, ?_⟩
  intro u hu hqu
  have hvu : ¬ u < v := fun hlt => not_lt_of_ge hqu (hbelow u hlt)
  rw [List.getD_eq_getElem xs 0 hvv, List.getD_eq_getElem xs 0 hu]
  exact hs.getElem_le_getElem_of_le (Nat.le_of_not_lt hvu)

/-- An alternative name for the exact quantile bisection guarantee `riskExactQuantileNoMargin`. -/
theorem exactQuantileNoMargin : ExactQuantileNoMargin := riskExactQuantileNoMargin

/-- The exact quantile bisection guarantee fails in general when the preparation matrix is not
required to be unitary. -/
theorem exactQuantileNoMargin_counterexample_without_unitary :
    ¬ (∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
      (loss : I → ℚ) (xs : List ℚ) (q : ℝ),
      xs ≠ [] → xs.SortedLE → (∀ i, loss i ∈ xs) → 0 < q → q < 1 →
      let F := fun v : ℕ => riskCDF A j loss (xs.getD v 0)
      let exactBisect : ℕ → ℕ → ℕ → ℕ := fun fuel lo hi =>
        Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
          (fun lo _ => lo)
          (fun _ rec lo hi => if hi ≤ lo then lo else
            let mid := (lo+hi)/2
            if q ≤ F mid then rec lo mid else rec (mid+1) hi)
          fuel lo hi
      let v := exactBisect (Nat.clog 2 xs.length + 1) 0 (xs.length - 1)
      v < xs.length ∧
      (∀ u : ℕ, u < v → F u < q) ∧
      (q ≤ F v) ∧
      (∀ u : ℕ, u < xs.length → q ≤ F u → xs.getD v 0 ≤ xs.getD u 0)) := by
  intro h
  have hs0 : ([0] : List ℚ).SortedLE := by
    rw [List.sortedLE_iff_pairwise]
    exact List.pairwise_singleton _ 0
  have hc := h Unit 0 () (fun _ => 0) [0] (1 / 2) (by decide) hs0
    (by intro _; simp) (by norm_num) (by norm_num)
  have hcdf : ∀ v : ℕ, riskCDF (0 : Matrix Unit Unit ℂ) () (fun _ => 0) ([0].getD v 0) = 0 := by
    intro v
    simp [riskCDF, BornProb]
  have hle := hc.2.2.1
  (try dsimp only at hle)
  rw [hcdf] at hle
  linarith

end Qatlib.Concepts.RiskEstimation.PopulationGap
