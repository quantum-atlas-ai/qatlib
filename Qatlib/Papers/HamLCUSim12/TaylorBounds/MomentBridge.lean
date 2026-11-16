/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentHami

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.HamLCUSim12.TaylorBounds
open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Fixed arXiv:1202.5822v1, Eq. (19): the coefficient vector `C : Fin (k+1) → ℝ`
satisfies the multi-product moment system of order `chi`, i.e.
`Σ_q C_q = 1` (row `m = 1` of the right-hand side) and
`Σ_q C_q / ℓ_q^{2chi + 2j} = 0` for `j = 0, ..., k-1`
(rows `m = j+2`; the paper prints the exponent `-2chi-2(m-2)` for row `m >= 2`,
which is `2chi + 2j` with `m = j + 2`). -/
def MomentCondition (k χ : ℕ) (N : ℝ) (C : Fin (k + 1) → ℝ) : Prop :=
  (∑ q, C q = 1) ∧ ∀ j : ℕ, j < k → (∑ q, C q / (mNode k N q) ^ (2 * χ + 2 * j)) = 0

/-- Fixed arXiv:1202.5822v1, Eq. (19) at `chi = 1`: the frozen coefficients `C_q` of
Eq. (17) satisfy the moment system.  Reuses the frozen identity
`multiproductMoment.multiproductMoment` (`Σ C_q = 1` and `Σ C_q / ℓ_q^{2m} = 0`). -/
theorem lemma4_moment_condition_chi_one (k : ℕ) (N : ℝ) (hN : 0 < N)
    (hd : NodesDistinct k N) :
    MomentCondition k 1 N (mCoeff k N) := by
  obtain ⟨hmass, hmom⟩ := multiproductMoment k N hN hd
  refine ⟨hmass, ?_⟩
  intro j hj
  have hexp : 2 * 1 + 2 * j = 2 * (j + 1) := by ring
  rw [hexp]
  exact hmom (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) (Nat.succ_le_of_lt hj)


end Qatlib.Papers.HamLCUSim12.TaylorBounds
