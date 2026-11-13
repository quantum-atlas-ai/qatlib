/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.Spectral.ChainProduct

/-!
# Johnson-chain eigenvalue estimates

This module defines Johnson vertices, adjacency, the normalized transition formula
`johnsonChain`, and the scalar formula `johnsonEigenvalue` used in the walk analysis of
[Tani2009]. It establishes symmetry and nonnegativity of the chain and bounds the nontrivial
eigenvalue formulas in absolute value.

## Main statements

* `johnsonAdj_symm`: symmetry of single-element replacement adjacency.
* `johnsonEigenvalue_sub`: a difference formula for eigenvalue expressions.
* `johnsonEigenvalue_abs_le`: the bound `1-1/k` for indices between one and `k`.

## References

* [Tani, 2009][Tani2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open scoped BigOperators

/-- The type of `k`-element subsets of `Fin n`, forming the vertices of the Johnson graph. -/
abbrev JohnsonVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

instance johnsonVertexFintype (n k : ℕ) : Fintype (JohnsonVertex n k) :=
  Fintype.ofInjective (fun v : JohnsonVertex n k => v.1) Subtype.val_injective

/-- Two Johnson vertices are adjacent when the first set has exactly one element outside the
second set. -/
def johnsonAdj {n k : ℕ} (a b : JohnsonVertex n k) : Prop := (a.1 \ b.1).card = 1

instance johnsonAdjDecidable {n k : ℕ} (a b : JohnsonVertex n k) :
    Decidable (johnsonAdj a b) := by
  unfold johnsonAdj
  infer_instance

/-- Johnson adjacency is symmetric. -/
theorem johnsonAdj_symm {n k : ℕ} {a b : JohnsonVertex n k}
    (h : johnsonAdj a b) : johnsonAdj b a := by
  have ha : a.1.card = k := a.2
  have hb : b.1.card = k := b.2
  have h1 := Finset.card_sdiff_add_card_inter a.1 b.1
  have h2 := Finset.card_sdiff_add_card_inter b.1 a.1
  have h3 : (a.1 ∩ b.1).card = (b.1 ∩ a.1).card := by rw [Finset.inter_comm]
  simp only [johnsonAdj] at h ⊢
  omega

/-- The Johnson-chain matrix, with entry `1/(k*(n-k))` on adjacent pairs and zero elsewhere. -/
def johnsonChain (n k : ℕ) : JohnsonVertex n k → JohnsonVertex n k → ℝ :=
  fun a b => if johnsonAdj a b then ((k : ℝ) * ((n : ℝ) - k))⁻¹ else 0

/-- The Johnson-chain matrix is symmetric; see [Tani2009]. -/
theorem johnsonChain_symm (n k : ℕ) : ∀ a b : JohnsonVertex n k,
    johnsonChain n k a b = johnsonChain n k b a := by
  intro a b
  simp only [johnsonChain]
  by_cases h : johnsonAdj a b
  · rw [if_pos h, if_pos (johnsonAdj_symm h)]
  · rw [if_neg h, if_neg (fun h' => h (johnsonAdj_symm h'))]

/-- For `k ≤ n`, every entry of the Johnson-chain matrix is nonnegative; see [Tani2009]. -/
theorem johnsonChain_nonneg (n k : ℕ) (hkn : k ≤ n) : ∀ a b : JohnsonVertex n k,
    0 ≤ johnsonChain n k a b := by
  have hdeg : (0 : ℝ) ≤ (k : ℝ) * ((n : ℝ) - k) := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) - k := by
      have hle : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      linarith
    exact mul_nonneg h1 h2
  intro a b
  simp only [johnsonChain]
  split_ifs with h
  · exact inv_nonneg.mpr hdeg
  · exact le_refl 0

/-- The real-valued Johnson eigenvalue formula `((k-j)*(n-k-j)-j)/(k*(n-k))`. -/
def johnsonEigenvalue (n k j : ℝ) : ℝ :=
  ((k - j) * (n - k - j) - j) / (k * (n - k))

/-- The difference between the Johnson eigenvalue formulas at `j` and `j+1` is
`(n-2*j)/(k*(n-k))`. -/
theorem johnsonEigenvalue_step (n k j : ℝ) :
    johnsonEigenvalue n k j - johnsonEigenvalue n k (j + 1)
      = (n - 2 * j) / (k * (n - k)) := by
  simp only [johnsonEigenvalue]
  rw [div_sub_div_same]
  congr 1
  ring

/-- Expresses the difference of the Johnson eigenvalue formulas at two indices as
`(j'-j)*(n+1-j-j')/(k*(n-k))`. -/
theorem johnsonEigenvalue_sub (n k j j' : ℝ) :
    johnsonEigenvalue n k j - johnsonEigenvalue n k j'
      = (j' - j) * (n + 1 - j - j') / (k * (n - k)) := by
  simp only [johnsonEigenvalue]
  rw [div_sub_div_same]
  congr 1
  ring

/-- For `k ≥ 2` and `2*k ≤ n`, the Johnson eigenvalue formula decreases between indices `j ≤ j'
≤ k`. -/
theorem johnsonEigenvalue_antitone {n k j j' : ℝ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (hj : j ≤ j') (hj' : j' ≤ k) :
    johnsonEigenvalue n k j' ≤ johnsonEigenvalue n k j := by
  have hden : (0 : ℝ) < k * (n - k) := by
    have hk0 : (0 : ℝ) < k := by linarith
    have hnk : (0 : ℝ) < n - k := by linarith
    positivity
  have hdiff := johnsonEigenvalue_sub n k j j'
  have hmul : 0 ≤ (j' - j) * (n + 1 - j - j') := by
    apply mul_nonneg (by linarith)
    linarith
  have hle : 0 ≤ johnsonEigenvalue n k j - johnsonEigenvalue n k j' := by
    rw [hdiff]
    exact div_nonneg hmul hden.le
  linarith

/-- For positive `k`, `2*k ≤ n`, and `0 ≤ j ≤ k`, the Johnson eigenvalue formula at `j+1` is at
most its value at `j`. -/
theorem johnsonEigenvalue_succ_le {n k j : ℝ} (hkn : 2 * k ≤ n)
    (_hj0 : 0 ≤ j) (hjk : j ≤ k) (hk0 : 0 < k) :
    johnsonEigenvalue n k (j + 1) ≤ johnsonEigenvalue n k j := by
  have hnk : (0 : ℝ) < n - k := by linarith
  have hstep := johnsonEigenvalue_step n k j
  have hnonneg : 0 ≤ (n - 2 * j) / (k * (n - k)) := by
    apply div_nonneg _ (by positivity)
    linarith
  linarith

/-- The Johnson eigenvalue formula at index zero equals one when `k` and `n-k` are nonzero. -/
theorem johnsonEigenvalue_zero {n k : ℝ} (hk0 : k ≠ 0) (hnk : n - k ≠ 0) :
    johnsonEigenvalue n k 0 = 1 := by
  simp only [johnsonEigenvalue]
  field_simp
  ring

/-- For `k ≥ 2` and `2*k ≤ n`, the Johnson eigenvalue formula at index one is at most `1-1/k`. -/
theorem johnsonEigenvalue_one_le {n k : ℝ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    johnsonEigenvalue n k 1 ≤ 1 - 1 / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hnk : (0 : ℝ) < n - k := by linarith
  have hden : (0 : ℝ) < k * (n - k) := by positivity
  have h1 : (1 - 1 / k) * (k * (n - k)) = (k - 1) * (n - k) := by
    field_simp [hk0.ne']
  rw [johnsonEigenvalue, div_le_iff₀ hden, h1]
  nlinarith

/-- The Johnson eigenvalue formula at index `k` equals `-1/(n-k)` when the denominator factors
are nonzero. -/
theorem johnsonEigenvalue_k_eq {n k : ℝ} (hk0 : k ≠ 0) (hnk : n - k ≠ 0) :
    johnsonEigenvalue n k k = -1 / (n - k) := by
  simp only [johnsonEigenvalue]
  field_simp
  ring

/-- For `k ≥ 2` and `2*k ≤ n`, the Johnson eigenvalue formula at index `k` is at least
`-(1-1/k)`. -/
theorem johnsonEigenvalue_k_ge {n k : ℝ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    -(1 - 1 / k) ≤ johnsonEigenvalue n k k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hnk : (0 : ℝ) < n - k := by linarith
  rw [johnsonEigenvalue_k_eq hk0.ne' hnk.ne']
  have hpos : 1 / (n - k) ≤ 1 - 1 / k := by
    have h1 : 1 - 1 / k = (k - 1) / k := by
      field_simp [hk0.ne']
    rw [h1, div_le_div_iff₀ hnk hk0]

    nlinarith [mul_le_mul_of_nonneg_right hkn (show (0 : ℝ) ≤ k - 1 by linarith),
      mul_nonneg hk0.le (show (0 : ℝ) ≤ k - 2 by linarith)]
  have hneg : -1 / (n - k) = -(1 / (n - k)) := neg_div (n - k) 1
  rw [hneg]
  linarith

/-- For `k ≥ 2`, `2*k ≤ n`, and `1 ≤ j ≤ k`, the absolute Johnson eigenvalue formula is at most
`1-1/k`, as used in [Tani2009]. -/
theorem johnsonEigenvalue_abs_le {n k j : ℝ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    |johnsonEigenvalue n k j| ≤ 1 - 1 / k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hnk : (0 : ℝ) < n - k := by linarith
  have hden : (0 : ℝ) < k * (n - k) := by positivity
  have hupper : johnsonEigenvalue n k j ≤ 1 - 1 / k :=
    le_trans (johnsonEigenvalue_antitone hk hkn hj1 hjk)
      (johnsonEigenvalue_one_le hk hkn)
  have hlower : -(1 - 1 / k) ≤ johnsonEigenvalue n k j :=
    le_trans (johnsonEigenvalue_k_ge hk hkn)
      (johnsonEigenvalue_antitone hk hkn hjk le_rfl)
  rw [abs_le]
  exact ⟨hlower, hupper⟩

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
