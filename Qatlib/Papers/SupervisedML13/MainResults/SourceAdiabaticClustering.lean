/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c005 — adiabatic construction of the k-means clustering state

Fixed arXiv:1307.0411v2, p. 4–5 and supplementary material p. 9–11.

The paper rephrases `k`-means as a quadratic program and constructs the
clustering state

`|χ⟩ = (1/√M) Σ_j |c_j⟩|j⟩`  (eq. (S1), p. 9)

with the quantum adiabatic algorithm.  Each adiabatic step acts only on the
`c'` cluster labels, whose initial/final overlap squared is `O(1/k)`, so one
step costs `O(k log kMN)` (p. 11); the overall construction to accuracy `ε`
costs `O(ε⁻¹ k log kMN)`, dropping to `O(ε⁻¹ log kMN)` when the minimum gap is
`O(1)` (p. 5, p. 11).

The Lean statements are the exact logarithmic accounting identities and the
normalization of the clustering state's label distribution.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- Probability weight `1/M` carried by each vector label `j` in the
clustering state `|χ⟩ = (1/√M) Σ_j |c_j⟩|j⟩` (eq. (S1), p. 9). -/
def clusteringStateWeight (M : ℕ) : ℝ := (M : ℝ)⁻¹

/-- The label distribution of the clustering state is a probability
distribution: the `M` labels each carry weight `1/M`.

Source: arXiv:1307.0411v2 eq. (S1), p. 9. -/
theorem clustering_state_mass_normalized (M : ℕ) (hM : 0 < M) :
    ∑ _j : Fin M, clusteringStateWeight M = 1 := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hM0

/-- **c005** (paper p. 4–5, p. 11).  For positive `k`, `M`, `N` the adiabatic
clustering cost `ε⁻¹ · k · (log₂ k + log₂ M + log₂ N + 3)` equals
`ε⁻¹ · k · (log₂(k·M·N) + 3)`, the paper's `O(ε⁻¹ k log kMN)`.

Source: arXiv:1307.0411v2 p. 5 "The algorithm takes time no greater than
`O(ε⁻¹ k log kMN)`"; p. 11 "the time per step ... is no greater than
`O(k log kMN)`".
Proof step: `Real.logb_mul` twice, then `ring`. -/
theorem adiabatic_clustering_runtime (ε : ℝ) (k M N : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) :
    adiabaticClusteringCost ε k M N
      = ε⁻¹ * (k : ℝ) * (Real.logb 2 (((k : ℝ) * (M : ℝ)) * (N : ℝ)) + 3) := by
  unfold adiabaticClusteringCost
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rw [Real.logb_mul (mul_ne_zero hk0 hM0) hN0, Real.logb_mul hk0 hM0]

/-- **c005**, well-separated case (paper p. 5, p. 11).  When the minimum
adiabatic gap is `O(1)` the factor `k` drops out and the cost is
`ε⁻¹ (log₂(k·M·N) + 3)`, the paper's `O(ε⁻¹ log kMN)`.

Source: arXiv:1307.0411v2 p. 5 "... and could take time as little as
`O(ε⁻¹ log kMN)` if the clusters are relatively well separated, so that the
gap of the adiabatic algorithm is `O(1)`." -/
theorem adiabatic_clustering_runtime_gap_one (ε : ℝ) (k M N : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) :
    adiabaticClusteringCostGapOne ε k M N
      = ε⁻¹ * (Real.logb 2 (((k : ℝ) * (M : ℝ)) * (N : ℝ)) + 3) := by
  unfold adiabaticClusteringCostGapOne
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rw [Real.logb_mul (mul_ne_zero hk0 hM0) hN0, Real.logb_mul hk0 hM0]

end Qatlib.Papers.SupervisedML13.MainResults
