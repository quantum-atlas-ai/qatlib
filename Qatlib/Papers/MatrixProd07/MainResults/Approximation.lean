/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs

/-!
# Matrix product approximation and entropy bounds

`theorem15_mps_approximation` bounds the squared approximation error by twice the sum of Schmidt
tails at internal cuts. The module defines `AchievesError`, least achieving bond dimension, and
the half-chain Rényi expression, then packages a proposed bond dimension estimate as the
proposition `theorem17_polynomial_bond`. These constructions are associated with
[PerezGarciaEtAl2007].

## Main statements

* `theorem15_mps_approximation`: existence of an approximation controlled by Schmidt tails.
* `theorem17_polynomial_bond`: proposition specifying the entropy-dependent bond bound.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.Approximation

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

/-- For `D ≥ 1`, the squared Schmidt tail at the zero cut vanishes. See [PerezGarciaEtAl2007]. -/
theorem schmidtTailSq_cut_zero {n d D : ℕ} (ψ : (Fin n → Fin d) → ℂ) (hD : 1 ≤ D) :
    schmidtTailSq n d ψ 0 D = 0 :=
  schmidtTailSq_eq_zero_of_cutRank_le ψ
    (le_trans (cutRank_le_one_left ψ) hD)

/-- For a nonempty chain and `D ≥ 1`, summing squared Schmidt tails over cuts below `n` equals
summing over the internal cuts from one to `n - 1`. See [PerezGarciaEtAl2007]. -/
theorem range_sum_eq_Ico_sum {n d D : ℕ} (ψ : (Fin n → Fin d) → ℂ) (hn : 1 ≤ n)
    (hD : 1 ≤ D) :
    (∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D)
      = ∑ k ∈ Finset.Ico 1 n, schmidtTailSq n d ψ k D := by
  have h := Finset.sum_range_add_sum_Ico (fun c => schmidtTailSq n d ψ c D)
    (m := 1) (n := n) hn
  rw [Finset.sum_range_one, schmidtTailSq_cut_zero ψ hD, zero_add] at h
  exact h.symm

/-- A normalized amplitude function on a nonempty chain has a bond dimension `D > 0` matrix
product approximation with squared error at most twice the sum of the squared Schmidt tails
over internal cuts. See [PerezGarciaEtAl2007]. -/
theorem theorem15_mps_approximation {n d D : ℕ} (ψ : (Fin n → Fin d) → ℂ)
    (hn : 1 ≤ n) (hD : 0 < D) (hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∃ (hD' : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      (∑ x, Complex.normSq (@mpsAmplitude n d D hD' A x - ψ x))
        ≤ 2 * ∑ k ∈ Finset.Ico 1 n, schmidtTailSq n d ψ k D := by
  obtain ⟨hD', A, hA⟩ := clause2_clause3 n d ψ hnorm hn D hD
  refine ⟨hD', A, ?_⟩
  rw [range_sum_eq_Ico_sum ψ hn hD] at hA
  exact hA

/-- The predicate that a nonzero bond dimension `D` permits a matrix product approximation to
`ψ` with squared error at most `ε`. -/
def AchievesError {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (ε : ℝ) (D : ℕ) : Prop :=
  ∃ (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    ∑ x, Complex.normSq (@mpsAmplitude n d D hD A x - ψ x) ≤ ε

/-- The predicate that `D` achieves squared error at most `ε` and is no larger than any other
dimension achieving that error. -/
def IsLeastAchieving {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (ε : ℝ) (D : ℕ) : Prop :=
  AchievesError ψ ε D ∧ ∀ D', AchievesError ψ ε D' → D ≤ D'

/-- The half-chain Rényi expression computed from the singular values of the middle cut matrix
as `log (∑ σᵢ ^ (2 * α)) / (1 - α)`. -/
def halfChainRenyi {d : ℕ} {L : ℕ} (ψ : (Fin (2 * L) → Fin d) → ℂ) (α : ℝ) : ℝ :=
  (1 - α)⁻¹ * Real.log
    (∑ i ∈ (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues
        (cutMatrix (2 * L) d ψ L)).support,
      (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues
        (cutMatrix (2 * L) d ψ L) i) ^ (2 * α))

/-- The proposition specifying a uniform constant in the displayed upper bound for the least
bond dimension achieving error `ε0 / L`, parameterized by the assumed logarithmic half-chain
Rényi bounds. -/
def theorem17_polynomial_bond  (d : ℕ) (c cbar ε0 : ℝ) (_hc : 0 < c) (_hcbar : 0 ≤ cbar)
    (_hε0 : 0 < ε0) (ψ : (L : ℕ) → (Fin (2 * L) → Fin d) → ℂ)
    (_hS : ∀ (α : ℝ), 0 < α → α < 1 → ∀ L : ℕ, 1 ≤ L →
      halfChainRenyi (ψ L) α ≤ (c / 6) * (1 + 1 / α) * Real.log L + cbar) : Prop :=
  ∃ cst : ℝ, 0 < cst ∧
      ∀ (α : ℝ) (_hα0 : 0 < α) (_hα1 : α < 1) (L : ℕ) (_hL : 1 ≤ L) (D : ℕ),
        IsLeastAchieving (ψ L) (ε0 / L) D →
        (D : ℝ) ≤ cst * (((L : ℝ) ^ 2 / ((1 - α) * ε0)) ^ (α / (1 - α)))
          * (L : ℝ) ^ ((c + cbar) / 12 * ((1 + α) / α))
end Qatlib.Papers.MatrixProd07.MainResults.Approximation
