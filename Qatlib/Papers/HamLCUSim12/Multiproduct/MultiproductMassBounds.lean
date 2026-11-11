/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientAux
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientDiagnostics

/-!
# Positive and negative multiproduct coefficient masses

This module bounds the positive and negative masses of `mCoeff` when N > k ≥ 1.
`multiproduct_kappa_of_coefficient_bound` converts a uniform bound on the first k coefficients
into a comparison between scaled negative mass and positive mass. See [ChildsWiebe2012] for the
multiproduct and linear-combination simulation framework.

## Main statements

* `multiproduct_positive_mass_ge_one`: For k ≥ 1 and N > k, the sum of the positive multiproduct
  coefficients is at least 1.
* `multiproduct_negative_mass_le`: For k ≥ 1 and N > k, if the first k coefficient magnitudes
  are bounded by B, the total absolute mass of negative coefficients is at most kB.
* `multiproduct_kappa_of_coefficient_bound`: For k ≥ 1 and N > k, a uniform first-k coefficient
  bound B and a nonnegative scale with kB · scale ≤ 1 imply that scaled negative mass is at most
  positive mass.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

/-- For k ≥ 1 and N > k, the sum of the positive multiproduct coefficients is at least 1. -/
theorem multiproduct_positive_mass_ge_one (k : ℕ) (hk : 1 ≤ k)
    (N : ℝ) (hN : (k : ℝ) < N) :
    1 ≤ ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) => 0 < mCoeff k N q),
      mCoeff k N q := by
  have hl := multiproduct_last_coefficient_ge_one k hk N hN
  apply hl.trans
  apply Finset.single_le_sum
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.le
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith

/-- For k ≥ 1 and N > k, if the first k coefficient magnitudes are bounded by B, the total
absolute mass of negative coefficients is at most kB. -/
theorem multiproduct_negative_mass_le (k : ℕ) (hk : 1 ≤ k)
    (N : ℝ) (hN : (k : ℝ) < N) (B : ℝ)
    (hB : ∀ q : Fin (k+1), q.val < k → |mCoeff k N q| ≤ B) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) => mCoeff k N q < 0),
      |mCoeff k N q|) ≤ (k : ℝ)*B := by
  have hsub : Finset.univ.filter (fun q : Fin (k+1) => mCoeff k N q < 0) ⊆
      Finset.univ.erase (Fin.last k) := by
    intro q hq
    have hn := (Finset.mem_filter.mp hq).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    rw [he] at hn
    linarith [multiproduct_last_coefficient_ge_one k hk N hN]
  calc
    _ ≤ ∑ q ∈ Finset.univ.erase (Fin.last k), |mCoeff k N q| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => abs_nonneg _)
    _ ≤ ∑ _q ∈ Finset.univ.erase (Fin.last k), B := by
      apply Finset.sum_le_sum
      intro q hq
      have hne : q.val ≠ k := by
        intro he
        exact (Finset.mem_erase.mp hq).1 (Fin.ext he)
      exact hB q (by omega)
    _ = _ := by simp

/-- For k ≥ 1 and N > k, a uniform first-k coefficient bound B and a nonnegative scale with kB ·
scale ≤ 1 imply that scaled negative mass is at most positive mass. -/
theorem multiproduct_kappa_of_coefficient_bound (k : ℕ) (hk : 1 ≤ k)
    (N : ℝ) (hN : (k : ℝ) < N) (B scale : ℝ) (hscale : 0 ≤ scale)
    (hB : ∀ q : Fin (k+1), q.val < k → |mCoeff k N q| ≤ B)
    (hnorm : (k : ℝ)*B*scale ≤ 1) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) => mCoeff k N q < 0),
      |mCoeff k N q|)*scale ≤
        ∑ q ∈ Finset.univ.filter (fun q : Fin (k+1) => 0 < mCoeff k N q),
          mCoeff k N q := by
  exact (mul_le_mul_of_nonneg_right
    (multiproduct_negative_mass_le k hk N hN B hB) hscale).trans
      (hnorm.trans (multiproduct_positive_mass_ge_one k hk N hN))

end Qatlib.Papers.HamLCUSim12.Multiproduct
