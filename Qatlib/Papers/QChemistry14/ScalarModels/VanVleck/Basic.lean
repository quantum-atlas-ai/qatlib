/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.VanVleck

open Finset

theorem vanVleck_bias_eq (N Δ Eg Ee : ℝ) :
    N * (Δ ^ 2 * Eg + (1 - Δ ^ 2) * Ee) - N * Eg
      = N * (1 - Δ ^ 2) * (Ee - Eg) := by
  ring

theorem vanVleck_bias_gap (N Δ Eg Ee ω : ℝ) (hω : ω = Ee - Eg) :
    N * (Δ ^ 2 * Eg + (1 - Δ ^ 2) * Ee) - N * Eg
      = N * (1 - Δ ^ 2) * ω := by
  rw [vanVleck_bias_eq, hω]

theorem qpe_ground_probability (Δ : ℝ) (N : ℕ) :
    (∏ _i : Fin N, Δ ^ 2) = Δ ^ (2 * N) := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (pow_mul Δ 2 N).symm

theorem qpe_ground_amplitude (Δ : ℝ) (N : ℕ) :
    |∏ _i : Fin N, Δ| = |Δ| ^ N := by
  rw [Finset.abs_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem qpe_ground_probability_abs (Δ : ℝ) (N : ℕ) :
    (∏ _i : Fin N, Δ ^ 2) = |Δ| ^ (2 * N) := by
  rw [qpe_ground_probability, ← abs_pow]
  exact (abs_of_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg Δ) N)).symm

theorem qpe_ground_probability_lt_one (Δ : ℝ) (N : ℕ) (hΔ : |Δ| < 1)
    (hN : 1 ≤ N) :
    |Δ| ^ (2 * N) < 1 := by
  have h2N : 0 < 2 * N := by omega
  have h0 : 0 ≤ |Δ| := abs_nonneg Δ
  exact pow_lt_one₀ h0 hΔ (by omega)

end Qatlib.Papers.QChemistry14.ScalarModels.VanVleck
