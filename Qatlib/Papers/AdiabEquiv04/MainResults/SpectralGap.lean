/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.HistoryProperties

/-!
# Clock spectral-gap statements and the initial ground vector

This module proves the diagonal form and positivity of `S0Init` and identifies its ground
vector. It defines the propositions for the reduced, full, and compressed path gap assertions in
Lemmas 3.5, 3.11, and 3.12 of [AharonovEtAl2007Adiabatic], including the endpoint ground vectors
for the compressed path.

## Main statements

* `S0Init_ground`: the coordinate vector at zero is a ground vector of `S0Init`.
* `lemma_3_5_spectral_gap_S0Statement`: the inverse-square reduced-path gap proposition.
* `lemma_3_11_spectral_gap_fullStatement` and `lemma_3_12_compressed_gapStatement`: the
  inverse-cube gap propositions.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.SpectralGap

open Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- At parameter zero, the reduced clock Hamiltonian has matrix `S0Init L`. -/
theorem HS0_zero (L : ℕ) :
    (HS0 L 0).mat = S0Init L := by
  unfold HS0 Hamiltonian.path Hamiltonian.add Hamiltonian.realSmul
  simp

/-- The matrix `S0Init L` is diagonal, with zero at index zero and one at every other diagonal
index. -/
theorem S0Init_eq_diagonal (L : ℕ) :
    S0Init L = diagonal (fun i : Fin (L + 1) => if i.val = 0 then (0 : ℂ) else 1) := by
  ext i j
  unfold S0Init
  rw [Matrix.diagonal_apply]

/-- The Rayleigh expression of `S0Init L` is the sum of squared coordinate norms excluding index
zero. -/
theorem rayleigh_S0Init (L : ℕ) (ψ : Vector (Fin (L + 1))) :
    rayleigh (S0Init L) ψ =
      ∑ i, (if i.val = 0 then 0 else Complex.normSq (ψ i)) := by
  classical
  have hmul : S0Init L *ᵥ ψ =
      fun i => (if i.val = 0 then (0 : ℂ) else 1) * ψ i := by
    ext i
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp [S0Init]
    · intro j _ hj
      have hji : ¬ (i = j) := fun h => hj h.symm
      simp [S0Init, hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  unfold rayleigh
  rw [hmul, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val = 0
  · simp [h]
  · simp only [h, if_false]
    have : ((star ψ) i) * ψ i = ((Complex.normSq (ψ i) : ℝ) : ℂ) := by
      rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [show ((star ψ) i * (1 * ψ i)) = ((star ψ) i * ψ i) by ring, this]
    simp

/-- The reduced initial clock matrix has nonnegative Rayleigh expression on every vector. -/
theorem S0Init_isPositive (L : ℕ) : IsPositive (S0Init L) := by
  intro ψ
  rw [rayleigh_S0Init]
  exact Finset.sum_nonneg (fun i _ => by
    by_cases h : i.val = 0
    · simp [h]
    · simp [h, Complex.normSq_nonneg])

/-- The coordinate basis vector at index zero is a ground vector of the reduced initial clock
Hamiltonian. See [AharonovEtAl2007Adiabatic]. -/
theorem S0Init_ground (L : ℕ) :
    IsGroundVector ⟨S0Init L, S0Init_isHermitian L⟩ (basisKet ⟨0, Nat.zero_lt_succ L⟩) := by
  refine ⟨isNormalized_basisKet _, ?_⟩
  intro φ _
  have h0 : rayleigh (S0Init L) (basisKet ⟨0, Nat.zero_lt_succ L⟩) = 0 := by
    rw [rayleigh_S0Init]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h : i.val = 0
    · simp [h]
    · have hi : i ≠ (0 : Fin (L + 1)) := by
        intro he
        exact h (by rw [he]; simp)
      simp [h, hi, basisKet]
  rw [h0]
  exact S0Init_isPositive L φ

/-- The statement that, for each `L ≥ 1`, the gap of `HS0 L s` is at least `c / (L + 1)²` on
`[0, 1]` for some positive `c`. See [AharonovEtAl2007Adiabatic]. -/
def lemma_3_5_spectral_gap_S0Statement : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    GapAtLeast (HS0 L s) (c / ((L : ℝ) + 1) ^ 2)

/-- The statement that, for each circuit with `L ≥ 2`, the gap of `Hpath` is at least `c / (L +
1)³` uniformly on `[0, 1]` for some positive `c`. See [AharonovEtAl2007Adiabatic]. -/
def lemma_3_11_spectral_gap_fullStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n), ∃ c : ℝ, 0 < c ∧
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      GapAtLeast (Hpath n L hL2 gates s) (c / ((L : ℝ) + 1) ^ 3)

/-- The statement that the compressed path has the time-zero vector and history state as
endpoint ground vectors and a gap at least `c / (L + 1)³` on `[0, 1]` for some positive `c`.
See [AharonovEtAl2007Adiabatic]. -/
def lemma_3_12_compressed_gapStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n),
    IsGroundVector (HS n L hL2 gates 0) (gamma (L := L) gates 0) ∧
    IsGroundVector (HS n L hL2 gates 1) (historyState (L := L) gates) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      GapAtLeast (HS n L hL2 gates s) (c / ((L : ℝ) + 1) ^ 3)

end Qatlib.Papers.AdiabEquiv04.MainResults.SpectralGap
