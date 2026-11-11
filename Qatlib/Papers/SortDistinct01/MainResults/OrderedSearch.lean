/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Ordered-search weights and conditional step bounds

This module defines reciprocal-distance weights on first-true indices and the corresponding real
overlap potential. It combines a supplied regrouping estimate, a Hilbert-form estimate, and a
squared-norm budget to prove `lemma7_ordered_step_bound`, the `pi*N` step bound in the adversary
analysis of [HoyerNeerbekShi2001].

## Main statements

* `hilbert_weighted_step_bound`: If `|X| ≤ pi*a*b` and `a^2 + b^2 ≤ N` for nonnegative `a` and
  `b`, then `2*|X| ≤ pi*N`, the numeric step estimate used in [HoyerNeerbekShi2001].
* `lemma7_ordered_step_bound`: Assuming the stated regrouping, Hilbert-form, and squared-norm
  bounds, one ordered-potential step changes by at most `pi*N`, the bound in [Hoyer et al.,
  Lemma 7][HoyerNeerbekShi2001].

## References

* [Hoyer et al., 2001][HoyerNeerbekShi2001]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.SortDistinct01.MainResults.OrderedSearch

/-- The joint index type for a workspace of size `Z` and a query register of size `N`. -/
abbrev QIdx (Z N : ℕ) : Type := Fin Z × Fin N

/-- The finite-dimensional complex Euclidean state space on workspace/query indices. -/
abbrev QState (Z N : ℕ) : Type := EuclideanSpace ℂ (QIdx Z N)

/-- The Euclidean state vector with coordinate function `f`. -/
def mkQ {Z N : ℕ} (f : QIdx Z N → ℂ) : QState Z N := WithLp.toLp 2 f

/-- The coordinatewise oracle action multiplying each amplitude by the input value at its query
index. -/
def phaseOracle {Z N : ℕ} (x : Fin N → ℂ) (u : QState Z N) : QState Z N :=
  mkQ fun j => x j.2 * u j

/-- The complex sign vector taking value `-1` at true bits and `1` at false bits. -/
def signOf {N : ℕ} (x : Fin N → Bool) : Fin N → ℂ :=
  fun i => if x i then -1 else 1

/-- A Boolean vector different from the all-false vector contains a true entry. -/
theorem ones_of_ne_zero {N : ℕ} {x : Fin N → Bool} (hx : x ≠ fun _ => false) :
    ∃ i, x i = true := by
  by_contra h
  apply hx
  funext i
  cases hi : x i
  · rfl
  · exact absurd ⟨i, hi⟩ h

/-- A Boolean vector different from the all-false vector has a true entry at some natural-number
index less than `N`. -/
theorem exists_index {N : ℕ} {x : Fin N → Bool} (hx : x ≠ fun _ => false) :
    ∃ n, ∃ _h : n < N, x ⟨n, _h⟩ = true := by
  obtain ⟨i, hi⟩ := ones_of_ne_zero hx
  exact ⟨i.1, i.2, hi⟩

/-- The least natural-number index of a true bit in a nonzero Boolean vector. -/
def firstOne {N : ℕ} (x : {x : Fin N → Bool // x ≠ fun _ => false}) : ℕ :=
  Nat.find (exists_index x.2)

/-- The reciprocal difference of first-true indices when the first input's index is smaller, and
zero otherwise. -/
def orderedWeight {N : ℕ}
    (x y : {x : Fin N → Bool // x ≠ fun _ => false}) : ℝ :=
  if firstOne x < firstOne y then
    1 / ((firstOne y : ℝ) - (firstOne x : ℝ))
  else 0

/-- The weighted sum of real inner products over all pairs of nonzero Boolean inputs at time
`j`. -/
def orderedPotential {Z N : ℕ}
    (ψ : {x : Fin N → Bool // x ≠ fun _ => false} → ℕ → QState Z N) (j : ℕ) : ℝ :=
  ∑ x : {x : Fin N → Bool // x ≠ fun _ => false},
    ∑ y : {x : Fin N → Bool // x ≠ fun _ => false},
      orderedWeight x y * Complex.re ⟪ψ x j, ψ y j⟫

/-- If `|X| ≤ pi*a*b` and `a^2 + b^2 ≤ N` for nonnegative `a` and `b`, then `2*|X| ≤ pi*N`, the
numeric step estimate used in [HoyerNeerbekShi2001]. -/
theorem hilbert_weighted_step_bound {X a b N : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hN : a ^ 2 + b ^ 2 ≤ N)
    (hX : |X| ≤ Real.pi * a * b) :
    2 * |X| ≤ Real.pi * N := by
  have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hX' : 2 * |X| ≤ 2 * (Real.pi * a * b) := by linarith [hX]
  calc 2 * |X| ≤ 2 * (Real.pi * a * b) := hX'
    _ = Real.pi * (2 * (a * b)) := by ring
    _ ≤ Real.pi * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_left h2ab Real.pi_pos.le
    _ ≤ Real.pi * N := mul_le_mul_of_nonneg_left hN Real.pi_pos.le

/-- Assuming the stated regrouping, Hilbert-form, and squared-norm bounds, one ordered-potential
step changes by at most `pi*N`, the bound in [Hoyer et al., Lemma 7][HoyerNeerbekShi2001]. -/
theorem lemma7_ordered_step_bound {Z N T : ℕ} (_hN : 2 ≤ N)
    (ψ : {x : Fin N → Bool // x ≠ fun _ => false} → ℕ → QState Z N)
    (U : QState Z N ≃ₗᵢ[ℂ] QState Z N)
    (_hunit : ∀ x j, ‖ψ x j‖ = 1)
    (_hstep : ∀ x j, ψ x (j + 1) = U (phaseOracle (signOf x.1) (ψ x j)))
    {j : ℕ} (_hj : j < T)
    (γ δ : Fin (N - 1) → ℝ)
    (hregroup : |orderedPotential ψ j - orderedPotential ψ (j + 1)|
      ≤ 2 * ∑ i : Fin (N - 1), ∑ k : Fin (N - 1), γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * δ k)
    (hhilb : |∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
        γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * δ k|
      ≤ Real.pi * Real.sqrt (∑ i, (γ i) ^ 2) * Real.sqrt (∑ k, (δ k) ^ 2))
    (hnorm : (∑ i : Fin (N - 1), (γ i) ^ 2) + (∑ k : Fin (N - 1), (δ k) ^ 2) ≤ (N : ℝ)) :
    |orderedPotential ψ j - orderedPotential ψ (j + 1)| ≤ Real.pi * (N : ℝ) := by
  set X : ℝ := ∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
      γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * δ k with hXdef
  set a : ℝ := Real.sqrt (∑ i : Fin (N - 1), (γ i) ^ 2) with hadef
  set b : ℝ := Real.sqrt (∑ k : Fin (N - 1), (δ k) ^ 2) with hbdef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ∑ i : Fin (N - 1), (γ i) ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hb2 : b ^ 2 = ∑ k : Fin (N - 1), (δ k) ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hXab : |X| ≤ Real.pi * a * b := hhilb
  have hNab : a ^ 2 + b ^ 2 ≤ (N : ℝ) := by rw [ha2, hb2]; exact hnorm
  have hcore := hilbert_weighted_step_bound ha hb hNab hXab
  have hmain : |orderedPotential ψ j - orderedPotential ψ (j + 1)| ≤ 2 * X := hregroup
  calc |orderedPotential ψ j - orderedPotential ψ (j + 1)|
      ≤ 2 * X := hmain
    _ ≤ 2 * |X| := by nlinarith [le_abs_self X]
    _ ≤ Real.pi * (N : ℝ) := hcore

end Qatlib.Papers.SortDistinct01.MainResults.OrderedSearch
